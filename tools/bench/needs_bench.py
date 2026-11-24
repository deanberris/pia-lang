#!/usr/bin/env python3
"""Says whether a change needs the proof build-time benchmark (ADR 0032).

The benchmark proves every file in corpus.txt twice and takes about 35
minutes on a hosted runner, so CI runs it only when a change can move what
it gates: the Z3 cost of each file in baseline.json. A file that is not in
the baseline is reported as new and never gated, so adding one needs no
run. The cost depends on:

* the files in the baseline, and the library modules they import;
* the parts of piac that run under --verify: the front end, the dialect,
  the transforms and the verifier, and piac.cpp itself (code generation and
  certificates run only when compiling, so they are left out);
* Z3, LLVM and MLIR and how Bazel builds them (third_party, the module
  files, .bazelrc);
* the benchmark itself (tools/bench, and the CI workflow that runs it).

Everything else, such as the docs site, ADRs, demos outside the baseline,
new library modules, other tests, the editor extension, the language
server, the REPL and the skills, cannot move a gated cost and is skipped.
CI still runs the benchmark every night on main, whatever changed, in case
this list misses something.

Reads the changed paths, one per line, on stdin and prints `true` or
`false`, with the paths that matched on stderr:

    git diff --name-only BASE HEAD | python3 tools/bench/needs_bench.py

An empty list prints `true`: when CI cannot tell what changed, it runs the
benchmark rather than miss a regression.
"""
import fnmatch
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# What the gated costs depend on besides the files. `*` matches across `/`.
CORE = [
    "src/*",
    "tools/piac/piac.cpp",
    "tools/piac/BUILD.bazel",
    "tools/bench/*",
    "third_party/*",
    "MODULE.bazel",
    "MODULE.bazel.lock",
    "BUILD.bazel",
    ".bazelrc",
    ".bazelversion",
    ".github/workflows/ci.yml",
]

# Parts of src/ that do not run under `piac --verify`: the language server
# and the REPL are other tools, and piac reaches code generation and
# certificates only when it compiles.
NOT_VERIFY = [
    "src/lsp/*",
    "src/repl/*",
    "src/codegen/*",
    "src/cert/*",
]

IMPORT = re.compile(r"^\s*import\s+([A-Z][A-Za-z0-9_.]*)", re.M)


def module_file(name):
    """The library file that defines an imported name, such as
    lib/Pia/Core/Order.pia for Pia.Core.Order.Ops, or None."""
    parts = name.split(".")
    while parts:
        rel = os.path.join("lib", *parts) + ".pia"
        if os.path.isfile(os.path.join(ROOT, rel)):
            return rel
        parts.pop()
    return None


def benchmarked():
    """The files in the baseline, and every library file they import,
    transitively."""
    baseline = json.load(open(os.path.join(ROOT, "tools/bench/baseline.json")))
    todo = list(baseline["files"])
    seen = set()
    while todo:
        rel = todo.pop()
        if rel in seen:
            continue
        seen.add(rel)
        try:
            text = open(os.path.join(ROOT, rel)).read()
        except OSError:
            continue  # deleted in this change; still counts as touched
        for name in IMPORT.findall(text):
            dep = module_file(name)
            if dep:
                todo.append(dep)
    return seen


def matches(path, pats):
    return any(fnmatch.fnmatchcase(path, p) for p in pats)


def needs_bench(paths):
    """Returns the paths that need the benchmark; None if the list is empty."""
    paths = [p.strip() for p in paths if p.strip()]
    if not paths:
        return None
    files = benchmarked()
    return [p for p in paths
            if p in files or (matches(p, CORE) and not matches(p, NOT_VERIFY))]


def main():
    hits = needs_bench(sys.stdin.read().splitlines())
    if hits is None:
        print("needs_bench: no changed paths; running the benchmark",
              file=sys.stderr)
        print("true")
        return
    for p in hits[:20]:
        print("needs_bench: %s" % p, file=sys.stderr)
    if len(hits) > 20:
        print("needs_bench: ... and %d more" % (len(hits) - 20),
              file=sys.stderr)
    if not hits:
        print("needs_bench: nothing the benchmark measures changed",
              file=sys.stderr)
    print("true" if hits else "false")


if __name__ == "__main__":
    main()
