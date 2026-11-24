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
OVERLAY = os.path.join(ROOT, "lib", "Pia", "Sys", "Posix.pia")
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
// A C enum is passed as its underlying integer (macOS's clockid_t).
template <class T, bool = std::is_enum<T>::value> struct canon { using type = T; };
template <class T> struct canon<T, true> { using type = typename std::underlying_type<T>::type; };
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
    probe = [includes, "#include <cstddef>\n#include <tuple>\n#include <type_traits>\nnamespace pia_probe {\n", "template <auto V> struct v {};\n"]
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
        probe.append(f"ty<canon<decltype(deduce(&::{n}))::r>::type> f{i};\n")
        for k in range(arity):
            probe.append(f"ty<canon<decltype(deduce(&::{n}))::a<{k}>>::type> f{i}_{k};\n")
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

    consts = []
    for i, n in enumerate(constants):
        ctype = strip_const(values[f"t{i}"])
        pia, why = pia_type(ctype, ctype, False)
        value = values[f"c{i}"]
        if pia is None or not fits(pia, value):
            fail(f"{n} = {value} has C type {ctype}, which Pia cannot hold")
        consts.append((pia_name(n), pia, value))
    layouts = []
    for i, n in enumerate(structs):
        fields = [
            (f.lower(), qual, values[f"o{i}_{j}"], values.get(f"z{i}_{j}", 0))
            for j, (f, qual) in enumerate(layout[n])
        ]
        layouts.append((n, values[f"s{i}"], values[f"a{i}"], fields))
    fns, skipped = [], []
    for i, n in enumerate(functions):
        node = decls[n]
        qual, _ = type_of(node)
        spelled_result, spelled_params = split_signature(qual)
        result, why = pia_type(spelled_result, canonical(values[f"f{i}"]), True)
        params = [c for c in node.get("inner", []) if c.get("kind") == "ParmVarDecl"]
        ps = []
        for k, p in enumerate(params):
            c = canonical(values[f"f{i}_{k}"])
            pt, pwhy = pia_type(type_of(p)[0], c, False)
            if pt is None:
                why = why or f"parameter {k + 1}: {pwhy}"
                break
            ps.append((p.get("name"), pt, c))
        if why:
            skipped.append((n, qual, why))
            continue
        args = ", ".join(spelled_params + (["..."] if node.get("variadic") else [])) or "void"
        fns.append(Fn(n, f"{spelled_result} {n}({args})", ps, result, bool(node.get("variadic"))))
    return emit(target, consts, layouts, fns, skipped, read_overlay())


class Fn:
    """A C function as the header declares it: its signature as spelled,
    each parameter's name, Pia type and canonical C type, its Pia result
    type, and whether it is variadic."""

    def __init__(self, name, spelled, params, result, variadic):
        self.name, self.spelled, self.params = name, spelled, params
        self.result, self.variadic = result, variadic


class Row:
    """One `let` of the Posix interface: a function's parameters as
    (name, modifiers, type), its result, its @variadic count, and its
    contract lines; or a constant's type."""

    def __init__(self, name, params, result, variadic, contract, is_fn):
        self.name, self.params, self.result = name, params, result
        self.variadic, self.contract, self.is_fn = variadic, contract, is_fn


def split_top(text, sep):
    parts, depth, cur, i = [], 0, "", 0
    while i < len(text):
        c = text[i]
        depth += {"(": 1, ")": -1, "[": 1, "]": -1}.get(c, 0)
        if depth == 0 and text.startswith(sep, i):
            parts.append(cur.strip())
            cur, i = "", i + len(sep)
            continue
        cur += c
        i += 1
    parts.append(cur.strip())
    return parts


def read_overlay():
    """The interface text and its rows, from lib/Pia/Sys/Posix.pia."""
    text = open(OVERLAY).read()
    m = re.search(r"^interface Posix = sig\n.*?^end\n", text, re.M | re.S)
    if not m:
        fail(f"{os.path.relpath(OVERLAY, ROOT)} has no `interface Posix = sig ... end`")
    interface = m.group(0)
    rows, current = [], None
    for line in interface.splitlines()[1:-1]:
        t = line.strip()
        if t.startswith("let "):
            current = [t, []]
            rows.append(current)
        elif t.startswith(("requires ", "ensures ")) and current:
            current[1].append(t)
    parsed = []
    for head, contract in rows:
        name, sig = re.fullmatch(r"let ([a-z_][a-z0-9_]*) : (.*)", head).groups()
        variadic = None
        v = re.search(r"\s*@variadic\((\d+)\)$", sig)
        if v:
            variadic, sig = int(v.group(1)), sig[: v.start()]
        parts = split_top(sig, "->")
        if len(parts) == 1:
            parsed.append(Row(name, [], parts[0], None, contract, False))
            continue
        params = []
        for part in parts[:-1]:
            pm = re.fullmatch(r"\(([a-z_][a-z0-9_]*) : (.*)\)", part)
            if not pm:
                fail(f"row {name}: cannot read the parameter {part!r}")
            words = pm.group(2).split()
            mods = [w for w in words if w in MODIFIERS]
            params.append((pm.group(1), mods, " ".join(w for w in words if w not in MODIFIERS)))
        parsed.append(Row(name, params, parts[-1], variadic, contract, True))
    return interface, parsed


MODIFIERS = {"borrowed", "moved", "in", "out", "inout", "fixed", "mutable"}


def join(row, fn, target):
    """Fails unless the row fits the header's declaration on this target."""
    where = f"row {row.name} ({fn.spelled}) on {target}"
    named = len(fn.params)
    if fn.variadic != (row.variadic is not None):
        fail(f"{where}: C's function is {'' if fn.variadic else 'not '}variadic")
    if fn.variadic and row.variadic != named:
        fail(f"{where}: C names {named} parameters, so the row needs @variadic({named})")
    if not fn.variadic and len(row.params) != named:
        fail(f"{where}: C takes {named} parameters, the row {len(row.params)}")
    for (pname, mods, ptype), (_, ctype, canon) in zip(row.params, fn.params):
        if ptype != ctype:
            fail(f"{where}: '{pname}' is {canon} in C, which is {ctype} in Pia, not {ptype}")
        if ("mutable" in mods or "out" in mods) and canon.startswith("const "):
            fail(f"{where}: '{pname}' is {canon}, so C does not write it: drop mutable and out")
    if row.result != fn.result:
        fail(f"{where}: C returns {fn.result} in Pia, not {row.result}")


def emit(target, consts, layouts, fns, skipped, overlay):
    interface, rows = overlay
    with open(MANIFEST, "rb") as f:
        aliases = tomllib.load(f).get("aliases", {})
    by_name = {f.name: f for f in fns}
    const_types = {n: t for n, t, _ in consts}
    covered = set()
    row_lines = []
    for row in rows:
        if not row.is_fn:
            if row.name not in const_types:
                fail(f"row {row.name}: no such constant in the {target} headers")
            if const_types[row.name] != row.result:
                fail(f"row {row.name}: C's type is {const_types[row.name]}, not {row.result}")
            continue
        symbol = aliases.get(row.name, row.name)
        if symbol not in by_name:
            fail(f"row {row.name}: no function {symbol} in the {target} headers, or Pia cannot declare it")
        join(row, by_name[symbol], target)
        covered.add(symbol)
        params = " ".join(
            f"({n} : {' '.join(mods + [t])})" for n, mods, t in row.params
        ) or "()"
        attrs = f" @variadic({row.variadic})" if row.variadic is not None else ""
        row_lines.append(f"\n\\ {by_name[symbol].spelled}\n")
        row_lines.append(f"let {row.name} {params} : {row.result}{attrs}\n")
        row_lines.extend(f"  {c}\n" for c in row.contract)
        row_lines.append(f"= extern \"{symbol}\"\n")

    names = {n for n, _, _ in consts}
    out = [header(target), "module Pia.Sys.Posix : Posix\n\n", interface]
    out.append(SECTION_CONSTANTS)
    out.extend(f"let {n} : {t} = {v}\n" for n, t, v in consts)
    out.append(SECTION_LAYOUTS)
    for n, size, align, fields in layouts:
        out.append(f"\n(* struct {n}: {size} bytes, aligned to {align}. *)\n")
        out.append(f"let {n}_size : usize = {size}\n")
        out.append(f"let {n}_align : usize = {align}\n")
        for f, qual, off, fsize in fields:
            out.append(f"let {n}_{f}_offset : usize = {off}  \\ {qual}, {fsize} bytes\n")
        names |= {f"{n}_size", f"{n}_align"} | {f"{n}_{f}_offset" for f, *_ in fields}
    out.append(SECTION_ROWS)
    out.extend(row_lines)
    out.append(SECTION_FUNCTIONS)
    for fn in fns:
        if fn.name in covered:
            continue
        if fn.name in names:
            fail(f"the function {fn.name} has the name of a generated constant")
        taken = set(names)
        pieces = [f"({param_name(p, k, taken)} : {t})" for k, (p, t, _) in enumerate(fn.params)]
        attrs = f" @variadic({len(fn.params)})" if fn.variadic else ""
        # A line comment, since a C pointer's "*)" would end a (* comment.
        out.append(f"\n\\ {fn.spelled}\n")
        out.append(f"let {fn.name} {' '.join(pieces) or '()'} : {fn.result}{attrs}\n= extern \"{fn.name}\"\n")
    if skipped:
        out.append("\n\\ Not declared yet, because Pia's foreign calls cannot express them:\n")
        out.extend(f"\\   {n}: {q}: {w}\n" for n, q, w in skipped)
    return "".join(out)


def header(target):
    return f"""(* GENERATED by tools/bindings/gen.py from the {target} headers named in
   tools/bindings/posix.toml and the interface in lib/Pia/Sys/Posix.pia
   (ADR 0051, section 6, and ADR 0057). Do not edit it: CI regenerates it
   on {target} and fails on any difference. To add a name, list it in
   posix.toml, or add a row to the interface, and run the generator on
   that target.

   This is Pia.Sys.Posix for {target}; the build picks it by target.
   Importers see only the interface, so its constants' values stay here. *)
"""


SECTION_CONSTANTS = """
(* Constants: each macro or enumerator's value, with the type C gives it. *)
"""

SECTION_LAYOUTS = """
(* Struct layouts: sizes, alignments and field offsets in bytes. A struct
   is passed to C as a byte buffer of its size. *)
"""

SECTION_ROWS = """
(* The interface's functions: each row's modifiers and contract, checked
   against the C declaration above it. *)
"""

SECTION_FUNCTIONS = """
(* The other functions: C's signatures, with no contract, private to this
   module until the interface gives them a row. A pointer is a byte
   buffer, and a variadic function takes only its named parameters. *)
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
