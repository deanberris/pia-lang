#!/usr/bin/env python3
"""Writes lib/Pia/Sys/Gen/<target>.pia from the target's C headers.

ADR 0051, section 6: Pia's POSIX declarations are generated from the
platform's headers, so they cannot drift from them. This script reads the
names listed in tools/bindings/posix.toml and asks clang for everything
about them:

- functions: the C signature from `-ast-dump=json`, including whether it
  is variadic;
- constants: the value and type of each macro or enumerator, read from
  the AST of a C++ probe that instantiates `v<+(NAME)>`, so nothing is
  compiled or run and a value is exactly what the compiler sees;
- structs: size, alignment, and each field's offset and size, from the
  same probe.

It runs on the target itself (the CI job of each platform), since the
headers are the target's. `--check` compares with the checked-in file and
fails with a diff, which is how CI keeps the files honest.
"""

import argparse
import difflib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MANIFEST = os.path.join(ROOT, "tools", "bindings", "posix.toml")
OUT_DIR = os.path.join(ROOT, "lib", "Pia", "Sys", "Gen")

TARGETS = {
    ("Linux", "x86_64"): "x86_64_linux",
    ("Darwin", "arm64"): "arm64_macos",
}

# Pia's keywords and the builtins a parameter must not shadow (ADR 0022).
RESERVED = set(
    """let rec meta in type of where if then else match with for spread while
    do done requires ensures invariant decreases assert assume forall exists
    interface sig module struct end import operator handle defer as true
    false borrowed moved out inout fixed mutable mod unsafe extern result
    old len size min max abs popcount clz ctz bswap rotl rotr element
    spec lemma theory model axiom""".split()
)

# C types by spelling. Typedefs that name a width the ABI ties to pointers
# keep that meaning; the rest are mapped after desugaring.
TYPEDEFS = {"size_t": "usize", "ssize_t": "isize", "uintptr_t": "usize", "intptr_t": "isize"}
BUILTINS = {
    "_Bool": "bool",
    "bool": "bool",
    "char": "i8",
    "signed char": "i8",
    "unsigned char": "u8",
    "short": "i16",
    "unsigned short": "u16",
    "int": "i32",
    "unsigned int": "u32",
    "long": "i64",
    "unsigned long": "u64",
    "long long": "i64",
    "unsigned long long": "u64",
}


def fail(msg):
    sys.exit("gen.py: " + msg)


def host_target():
    key = (platform.system(), platform.machine())
    if key not in TARGETS:
        fail(f"no Pia target for {key[0]} on {key[1]}")
    return TARGETS[key]


def sysroot_flags(target):
    if target != "arm64_macos":
        return []
    sdk = subprocess.run(["xcrun", "--show-sdk-path"], capture_output=True, text=True, check=True)
    return ["-isysroot", sdk.stdout.strip()]


def clang_json(clang, flags, source, suffix, extra):
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "probe" + suffix)
        with open(path, "w") as f:
            f.write(source)
        cmd = [clang, *flags, *extra, "-fsyntax-only", "-Xclang", "-ast-dump=json", path]
        run = subprocess.run(cmd, capture_output=True, text=True)
        if run.returncode != 0:
            fail("clang failed on the probe:\n" + run.stderr)
        return json.loads(run.stdout)


def type_of(node):
    t = node.get("type", {})
    return t.get("qualType", ""), t.get("desugaredQualType", t.get("qualType", ""))


def strip_const(t):
    return re.sub(r"\b(const|volatile|restrict|__restrict)\b", "", t).strip()


def pia_type(qual, desugared, is_result):
    """The Pia type of a C type, or None with the reason it has none yet."""
    name = strip_const(qual)
    if name in TYPEDEFS:
        return TYPEDEFS[name], None
    d = re.sub(r"\s+", " ", strip_const(desugared))
    d = re.sub(r"\bint\b", "", d).strip() if d not in ("int", "unsigned int") else d
    d = {"unsigned": "unsigned int", "long": "long", "short": "short"}.get(d, d)
    if d == "void" and is_result:
        return "unit", None
    if "(*)" in d or "(" in d:
        return None, "a function pointer"
    if d.endswith("*") or d.endswith("]"):
        if is_result:
            return None, "it returns a pointer"
        return "[u8]", None
    if d in BUILTINS:
        return BUILTINS[d], None
    if d.startswith(("struct ", "union ")):
        return None, f"it passes {d} by value"
    return None, f"Pia has no type for {d}"


SIG_TEMPLATE = """template <class R, class... A> struct sig {
  using r = R;
  template <int I> using a = typename std::tuple_element<I, std::tuple<A...>>::type;
};
// Deduction drops noexcept and noreturn, which a pattern match keeps.
template <class R, class... A> sig<R, A...> deduce(R (*)(A...));
template <class R, class... A> sig<R, A...> deduce(R (*)(A..., ...));
template <class T> struct ty {};
"""


def canonical(probe):
    """The type a probe names, as its template argument: "ty<unsigned
    long>" is "unsigned long"."""
    m = re.fullmatch(r"(?:pia_probe::)?ty<(.*)>", probe.strip())
    if not m:
        fail(f"cannot read the probe's type {probe!r}")
    return m.group(1).strip()


def split_signature(t):
    """A function type's result and parameter types, as spelled: "int
    (int, const char *, ...)" is ("int", ["int", "const char *", "..."])."""
    depth, start = 0, None
    for i, c in enumerate(t):
        if c == "(" and depth == 0 and start is None:
            start = i
        depth += {"(": 1, ")": -1}.get(c, 0)
    result = t[:start].strip()
    inner = t[start + 1 : t.rindex(")")]
    params, depth, cur = [], 0, ""
    for c in inner:
        depth += {"(": 1, ")": -1}.get(c, 0)
        if c == "," and depth == 0:
            params.append(cur.strip())
            cur = ""
        else:
            cur += c
    if cur.strip() and cur.strip() != "void":
        params.append(cur.strip())
    return result, [p for p in params if p != "..."]


def top_level(ast):
    for node in ast.get("inner", []):
        if node.get("isImplicit"):
            continue
        yield node


def find_functions(ast, names):
    found = {}
    for node in top_level(ast):
        name = node.get("name")
        if node.get("kind") == "FunctionDecl" and name in names and name not in found:
            found[name] = node
    return found


def find_structs(ast, names):
    found = {}

    def visit(node):
        if node.get("kind") == "RecordDecl" and node.get("completeDefinition"):
            name = node.get("name")
            if name in names and name not in found:
                found[name] = node
        for child in node.get("inner", []):
            if child.get("kind") in ("RecordDecl", "TypedefDecl", "LinkageSpecDecl"):
                visit(child)

    for node in top_level(ast):
        visit(node)
    return found


def struct_fields(record):
    """Named fields, in order, with anonymous members flattened as C sees
    them. Reserved names (`__pad`) are not API, and bit-fields have no
    offset, so both are left out."""
    fields = []
    anon = None
    for child in record.get("inner", []):
        kind = child.get("kind")
        if kind == "RecordDecl" and not child.get("name"):
            anon = child
            continue
        if kind != "FieldDecl":
            continue
        name = child.get("name")
        if not name:
            if anon is not None:
                fields.extend(struct_fields(anon))
            continue
        if name.startswith("__") or child.get("isBitfield"):
            continue
        qual, _ = type_of(child)
        fields.append((name, qual))
    return fields


def param_name(raw, index, taken):
    name = (raw or "").lstrip("_").lower() or f"a{index}"
    if not re.fullmatch(r"[a-z][a-z0-9_]*", name):
        name = f"a{index}"
    while name in RESERVED or name in taken:
        name += "_"
    taken.add(name)
    return name


def pia_name(c_name):
    return c_name.lstrip("_").lower()


def literal(text):
    m = re.fullmatch(r"\(?(-?\d+)[uUlL]*\)?", text.strip())
    if not m:
        fail(f"cannot read the constant {text!r}")
    return int(m.group(1))


def fits(pia, value):
    if pia == "bool":
        return False
    bits = int(pia[1:])
    if pia[0] == "u":
        return 0 <= value < 1 << bits
    return -(1 << (bits - 1)) <= value < 1 << (bits - 1)


def generate(target, clang):
    with open(MANIFEST, "rb") as f:
        manifest = tomllib.load(f)
    sections = [manifest["all"], manifest.get(target, {})]
    headers = [h for s in sections for h in s.get("headers", [])]
    functions = [n for s in sections for n in s.get("functions", [])]
    constants = [n for s in sections for n in s.get("constants", [])]
    structs = [n for s in sections for n in s.get("structs", [])]
    flags = sysroot_flags(target)
    includes = "".join(f"#include <{h}>\n" for h in headers)

    # Functions and struct fields, from the headers as C reads them.
    c_ast = clang_json(clang, flags, includes, ".c", ["-std=c11", "-D_GNU_SOURCE"])
    decls = find_functions(c_ast, set(functions))
    records = find_structs(c_ast, set(structs))
    missing = [n for n in functions if n not in decls] + [
        "struct " + n for n in structs if n not in records
    ]
    if missing:
        fail(f"not declared in the {target} headers: " + ", ".join(missing))

    # Values, sizes and offsets, as a C++ probe's template arguments.
    probe = [includes, "#include <cstddef>\n#include <tuple>\nnamespace pia_probe {\n", "template <auto V> struct v {};\n"]
    for i, n in enumerate(constants):
        probe.append(f"v<+({n})> c{i};\ndecltype(+({n})) t{i};\n")
    # Each function's result and parameter types, desugared to the types
    # C passes: a header can hide them behind typedefs, macros or glibc's
    # transparent __SOCKADDR_ARG union. A pointer to each is a variable,
    # so that void is one too.
    probe.append(SIG_TEMPLATE)
    for i, n in enumerate(functions):
        if n not in decls:
            continue
        arity = sum(1 for c in decls[n].get("inner", []) if c.get("kind") == "ParmVarDecl")
        probe.append(f"ty<decltype(deduce(&::{n}))::r> f{i};\n")
        for k in range(arity):
            probe.append(f"ty<decltype(deduce(&::{n}))::a<{k}>> f{i}_{k};\n")
    layout = {}
    for i, n in enumerate(structs):
        fields = struct_fields(records[n])
        layout[n] = fields
        probe.append(f"v<sizeof(struct {n})> s{i};\nv<alignof(struct {n})> a{i};\n")
        for j, (f, qual) in enumerate(fields):
            probe.append(f"v<offsetof(struct {n}, {f})> o{i}_{j};\n")
            if not qual.endswith("[]"):
                probe.append(f"v<sizeof(((struct {n} *)nullptr)->{f})> z{i}_{j};\n")
    probe.append("}\n")
    cxx_ast = clang_json(
        clang, flags, "".join(probe), ".cpp",
        ["-x", "c++", "-std=c++17", "-D_GNU_SOURCE", "-Xclang", "-ast-dump-filter=pia_probe"],
    )
    values = {}

    def collect(node):
        if node.get("kind") == "VarDecl":
            qual, desugared = type_of(node)
            m = re.fullmatch(r"(?:pia_probe::)?v<(.*)>", desugared)
            values[node["name"]] = literal(m.group(1)) if m else desugared
        for child in node.get("inner", []):
            collect(child)

    collect(cxx_ast)

    out = [header(target)]
    names = set()

    def define(name):
        if name in names:
            fail(f"two generated items are named {name}")
        names.add(name)
        return name

    # Constants and layouts first: their names are reserved before any
    # parameter is named, so no parameter shadows one.
    const_lines = []
    for i, n in enumerate(constants):
        ctype = strip_const(values[f"t{i}"])
        pia, why = pia_type(ctype, ctype, False)
        value = values[f"c{i}"]
        if pia is None or not fits(pia, value):
            fail(f"{n} = {value} has C type {ctype}, which Pia cannot hold")
        const_lines.append(f"let {define(pia_name(n))} : {pia} @target({target}) = {value}\n")
    layout_lines = []
    for i, n in enumerate(structs):
        size, align = values[f"s{i}"], values[f"a{i}"]
        layout_lines.append(f"\n(* struct {n}: {size} bytes, aligned to {align}. *)\n")
        layout_lines.append(f"let {define(n + '_size')} : usize @target({target}) = {size}\n")
        layout_lines.append(f"let {define(n + '_align')} : usize @target({target}) = {align}\n")
        for j, (f, qual) in enumerate(layout[n]):
            off = values[f"o{i}_{j}"]
            fsize = values.get(f"z{i}_{j}", 0)
            base = f"{n}_{f.lower()}"
            layout_lines.append(
                f"let {define(base + '_offset')} : usize @target({target}) = {off}"
                f"  \\ {qual}, {fsize} bytes\n"
            )

    fn_lines, skipped = [], []
    for i, n in enumerate(functions):
        node = decls[n]
        qual, _ = type_of(node)
        spelled_result, spelled_params = split_signature(qual)
        result, why = pia_type(spelled_result, canonical(values[f"f{i}"]), True)
        params = [c for c in node.get("inner", []) if c.get("kind") == "ParmVarDecl"]
        taken = set(names)
        pieces = []
        for k, p in enumerate(params):
            pt, pwhy = pia_type(type_of(p)[0], canonical(values[f"f{i}_{k}"]), False)
            if pt is None:
                why = why or f"parameter {k + 1}: {pwhy}"
                break
            pieces.append(f"({param_name(p.get('name'), k, taken)} : {pt})")
        if why:
            skipped.append(f"\\   {n}: {qual}: {why}\n")
            continue
        attrs = f"@target({target})"
        if node.get("variadic"):
            attrs += f" @variadic({len(params)})"
        args = ", ".join(spelled_params) or "void"
        # A line comment, since a C pointer's "*)" would end a (* comment.
        fn_lines.append(f"\n\\ {spelled_result} {n}({args})\n")
        fn_lines.append(
            f"let {define(n)} {' '.join(pieces) or '()'} : {result} {attrs}\n"
            f"= extern \"{n}\"\n"
        )

    out.append(SECTION_CONSTANTS)
    out.extend(const_lines)
    out.append(SECTION_LAYOUTS)
    out.extend(layout_lines)
    out.append(SECTION_FUNCTIONS)
    out.extend(fn_lines)
    if skipped:
        out.append("\n\\ Not declared yet, because Pia's foreign calls cannot express them:\n")
        out.extend(skipped)
    return "".join(out)


def header(target):
    return f"""(* GENERATED by tools/bindings/gen.py from the {target} headers named in
   tools/bindings/posix.toml (ADR 0051, section 6). Do not edit it: CI
   regenerates it on {target} and fails on any difference. To add a name,
   list it in posix.toml and run the generator on that target.

   Every item is `@target({target})`, so it is compiled and proved only
   for that target. None has a contract, so each function can be called
   only as `unsafe`, until the contract overlay gives it one. *)
"""


SECTION_CONSTANTS = """
(* Constants: each macro or enumerator's value, with the type C gives it. *)
"""

SECTION_LAYOUTS = """
(* Struct layouts: sizes, alignments and field offsets in bytes. A struct
   is passed to C as a byte buffer of its size. *)
"""

SECTION_FUNCTIONS = """
(* Functions: C's signatures, each above its declaration. A pointer is a
   byte buffer, and a variadic function takes only its named parameters
   here; its variadic arguments come with the overlay. *)
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--target", help="the Pia target (default: the host's)")
    ap.add_argument("--clang", default=os.environ.get("CLANG") or shutil.which("clang") or "clang")
    ap.add_argument("--check", action="store_true", help="fail if the checked-in file differs")
    ap.add_argument("-o", "--output", help="where to write (default: lib/Pia/Sys/Gen/<target>.pia)")
    args = ap.parse_args()
    target = args.target or host_target()
    if target != host_target():
        fail(f"{target} is generated on {target}, from its own headers")
    text = generate(target, args.clang)
    path = args.output or os.path.join(OUT_DIR, target + ".pia")
    if args.check:
        old = open(path).read() if os.path.exists(path) else ""
        if old == text:
            return
        sys.stdout.writelines(
            difflib.unified_diff(
                old.splitlines(True), text.splitlines(True),
                os.path.relpath(path, ROOT), "generated",
            )
        )
        fail(f"{os.path.relpath(path, ROOT)} is out of date: run tools/bindings/gen.py on {target}")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)


if __name__ == "__main__":
    main()
