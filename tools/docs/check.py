#!/usr/bin/env python3
"""Checks that the public documentation (docs/, https://pia-lang.dev) keeps
up with what is built.

Usage: python3 tools/docs/check.py   (from anywhere in the repository)

The examples inside the docs are run by //tests/docs:doc_examples_test
against the real piac. This script checks what that test cannot, without
building anything, so it runs on every pull request in seconds
(.github/workflows/docs-check.yml). It is the docs' counterpart of
tools/skills/check.py, which does the same for the agent skill pack.

The public docs are every Markdown page under docs/ except the decision
records in docs/adr/: an ADR records a design, it does not teach a user.

1. Every keyword the lexer knows, every flag piac and pia accept, every
   attribute the library, the examples and the feature tests use, and every
   lint is mentioned in code on some public page. A feature PR that adds
   one fails here until a page teaches it (or an exemption below says why
   it need not).
2. Every feature test, tests/verify/<feature>.pia, is named by some public
   page, usually docs/features.md, which links each feature to the page
   that explains it and to its working example. A feature PR adds a test,
   so it fails here until the docs point at the feature.
3. Every standard library module, lib/Pia/**.pia, is named on
   docs/library.md, the reference of the library as built.
4. Every public page with Pia examples (```ocaml or ```pia blocks, or a
   `$ piac` or `$ pia` console block) is run by a test in
   tests/docs/BUILD.bazel, or is listed below with the reason it is not.
5. Every relative link from a public page to a file outside docs/, such as
   ../tests/verify/loops.pia, names a file or directory that exists.

Exit status: 0 when everything holds, 1 otherwise, with one line per
problem.
"""

import importlib.util
import os
import re
import subprocess
import sys

# What counts as "in code", and the contextual keywords, are the skill
# pack's (tools/skills/check.py), so the two checks agree.
_spec = importlib.util.spec_from_file_location(
    "skills_check", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                 "..", "skills", "check.py"))
_skills = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_skills)
CONTEXTUAL, code_words = _skills.CONTEXTUAL, _skills.code_words

# Flags no user needs, and why.
FLAG_EXEMPT = {
    # Only for the memory-independence test of solver cost
    # (tests/verify/memory_independent_cost.pia).
    "--memory-ballast",
}

# Keywords that need no teaching of their own, and why.
KEYWORD_EXEMPT = {
    # `true` and `false` are values, not features.
    "true",
    "false",
}

# Attributes no user writes, and why.
ATTRIBUTE_EXEMPT = set()

# Feature tests that test no feature of their own, and why.
VERIFY_EXEMPT = {
    # A parser regression (#259): where a contract clause ends.
    "body_after_ensures.pia",
    # A solver-cost regression: a goal costs the same in a large process.
    "memory_independent_cost.pia",
    # A soundness regression (#375): repeated pure calls in a contract agree.
    "pure_contract_calls.pia",
    # A soundness regression: a spec function's facts only where proved.
    "spec_arg_range.pia",
    # A completeness regression: slice elements keep their range in specs.
    "spec_slice_ranges.pia",
}

# Public pages with Pia examples that tests/docs does not run, and why.
UNTESTED_PAGES = {
    # Built and run on the GPU by //examples/streams:placed, which only the
    # macOS CI job can run.
    "docs/placed.pia.md":
        "built by examples/streams/BUILD.bazel",
    "docs/pull_gpu.pia.md":
        "built by examples/streams/BUILD.bazel",
    # Design documents: their examples show syntax that is designed, much
    # of it not built yet. What is built is taught, and tested, on the tour.
    "docs/design.md": "design",
    "docs/meta.md": "design",
    "docs/stdlib.md": "design",
    "docs/concurrency.md": "design",
    # Compiler internals: fragments that show what a stage does.
    "docs/codegen.md": "internals",
    "docs/verifier.md": "internals",
}


def root():
    out = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                         capture_output=True, text=True,
                         cwd=os.path.dirname(os.path.abspath(__file__)))
    return out.stdout.strip() if out.returncode == 0 else os.getcwd()


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def files_under(top, suffixes):
    found = []
    for d, _, names in os.walk(top):
        for n in names:
            if n.endswith(suffixes):
                found.append(os.path.join(d, n).replace(os.sep, "/"))
    return sorted(found)


def pia_code(path):
    """The code of a Pia file, without comments or string literals, so
    that an attribute named in a comment is not taken as used."""
    text = read(path)
    if path.endswith(".md"):
        text = "\n".join(re.findall(r"^```pia[^\n]*\n(.*?)^```", text,
                                    re.S | re.M))
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("*)", i):
            depth, i = depth - 1, i + 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    code = re.sub(r'"(\\.|[^"\\\n])*"', '""', "".join(out))
    return re.sub(r"(^|\s)\\ .*", "", code, flags=re.M)


def main():
    top = root()
    os.chdir(top)
    problems = []

    pages = [p for p in files_under("docs", (".md",))
             if not p.startswith("docs/adr/")]
    texts = {p: read(p) for p in pages}
    taught = set()
    for t in texts.values():
        taught |= code_words(t)
    everything = "\n".join(texts.values())

    # 1. Keywords, flags, attributes and lints.
    lexer = read("src/syntax/Lexer.cpp")
    table = lexer[lexer.find("keywords()"):]
    table = table[:table.find("};")]
    keywords = re.findall(r'\{"([a-z]+)"', table) + CONTEXTUAL
    for k in keywords:
        if k not in taught and k not in KEYWORD_EXEMPT:
            problems.append(f"docs: the keyword `{k}` (src/syntax/Lexer.cpp) is in no public page's code; teach it (docs/tour.md, docs/grammar.md), or exempt it in tools/docs/check.py with a reason")
    flags = []
    for tool in ("tools/piac/piac.cpp", "tools/pia/pia.cpp"):
        for f in sorted(set(re.findall(r'"(--[a-z][a-z-]*)', read(tool)))):
            flags.append(f)
            if f not in taught and f not in FLAG_EXEMPT:
                problems.append(f"docs: the flag `{f}` ({tool}) is in no public page's code; document it, or exempt it in tools/docs/check.py with a reason")
    sources = (files_under("tests/verify", (".pia",)) +
               files_under("lib", (".pia",)) +
               files_under("examples", (".pia", ".pia.md")))
    attributes = {}
    for s in sources:
        for a in re.findall(r"(?<![\w$])@([a-z_]+)", pia_code(s)):
            attributes.setdefault(a, s)
    for a, where in sorted(attributes.items()):
        if f"@{a}" not in taught and a not in ATTRIBUTE_EXEMPT:
            problems.append(f"docs: the attribute `@{a}` (used in {where}) is in no public page's code; teach it, or exempt it in tools/docs/check.py with a reason")
    lint = read("src/syntax/Lint.cpp")
    lint = lint[lint.find("lintNames()"):]
    lints = re.findall(r'"([a-z_]+)"', lint[:lint.find("};")])
    idioms = read("docs/idioms.md")
    for name in lints:
        if name not in code_words(idioms):
            problems.append(f"docs/idioms.md: the lint `{name}` (src/syntax/Lint.cpp) is not in \"The lints\"")

    # 2. Feature tests.
    verify = [os.path.basename(f) for f in files_under("tests/verify", (".pia",))]
    for f in verify:
        if f"tests/verify/{f}" not in everything and f not in VERIFY_EXEMPT:
            problems.append(f"docs: tests/verify/{f} is named by no public page; add the feature to docs/features.md, with a link to the page that explains it, or exempt it in tools/docs/check.py with a reason")
    for f in sorted(VERIFY_EXEMPT):
        if f not in verify:
            problems.append(f"tools/docs/check.py: VERIFY_EXEMPT names tests/verify/{f}, which is gone")

    # 3. Library modules.
    library = read("docs/library.md")
    modules = [m[len("lib/"):-len(".pia")].replace("/", ".")
               for m in files_under("lib", (".pia",))]
    for m in modules:
        if f"`{m}`" not in library:
            problems.append(f"docs/library.md: the module `{m}` (lib/{m.replace('.', '/')}.pia) is not listed")

    # 4. Pages with examples are tested.
    build = read("tests/docs/BUILD.bazel")
    example = re.compile(r"^\s*```(ocaml|pia)\s*$|^\s*\$ pia c?\b|^\s*\$ piac\b",
                         re.M)
    for p in pages:
        has_examples = example.search(texts[p]) is not None
        tested = f'"//docs:{p[len("docs/"):]}"' in build
        if has_examples and not tested and p not in UNTESTED_PAGES:
            problems.append(f"{p}: has Pia examples that no test runs; add it to DOCS in tests/docs/BUILD.bazel (and exports_files in docs/BUILD.bazel), or list it in UNTESTED_PAGES in tools/docs/check.py with a reason")
    for p in sorted(UNTESTED_PAGES):
        if p not in texts:
            problems.append(f"tools/docs/check.py: UNTESTED_PAGES names {p}, which is gone")
        elif f'"//docs:{p[len("docs/"):]}"' in build:
            problems.append(f"tools/docs/check.py: {p} is tested now; take it out of UNTESTED_PAGES")

    # 5. Links out of docs/.
    link = re.compile(r"\]\((\.\./[^)\s#]*)")
    for p in pages:
        for target in link.findall(texts[p]):
            path = os.path.normpath(os.path.join(os.path.dirname(p), target))
            if path.startswith("docs" + os.sep) or path == "docs":
                continue
            if not os.path.exists(path):
                problems.append(f"{p}: links to {target}, which does not exist")

    for p in problems:
        print(p)
    if problems:
        print(f"{len(problems)} problem(s); see tools/docs/check.py")
        return 1
    print(f"docs: {len(pages)} pages cover {len(keywords)} keywords, "
          f"{len(flags)} flags, {len(attributes)} attributes, {len(lints)} "
          f"lints, {len(verify) - len(VERIFY_EXEMPT)} feature tests and "
          f"{len(modules)} library modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
