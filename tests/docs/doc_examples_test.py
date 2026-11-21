"""Checks every Pia example in the public documentation against piac.

Usage: doc_examples_test.py <piac> [--pia <pia>] <markdown file>...

Each ```ocaml block in a checked Markdown file is a complete Pia program.
By default it must verify: `piac --verify` exits 0, so every goal in it is
proved. Comments just before a block change that:

    <!-- example: name.pia -->   the file name to write it to (default:
                                 example<N>.pia), used by commands below
    <!-- expect: fail -->        `piac --verify` must exit 1 (a goal fails)
    <!-- untested: reason -->    not checked, such as syntax that is
                                 designed but not implemented yet
    <!-- source: path/f.pia -->  the block must be the whole of that file
                                 in the repository, so a page that shows a
                                 program cannot drift from it
    <!-- repl: name.pia -->      a REPL session, written to that file but
                                 not checked with piac --verify

A ```console block whose first line is `$ piac ...` runs that command in the
directory holding the examples written so far, and its output (stdout and
stderr) must match the rest of the block. A line `...` in the expected
output matches any number of lines. A ```console block whose first line is
`$ pia ...` runs `pia` the same way, and `< file` on that line feeds the
file to its standard input.

Every piac run gets the same deterministic solver limits as `pia_object`
(tools/piac/pia.bzl), unless its command line sets them, so whether a goal
is proved does not depend on how busy the machine is: `bazel test //...`
runs this test alongside everything else.
"""

import os
import re
import shlex
import subprocess
import sys
import tempfile

# The defaults of pia_object in tools/piac/pia.bzl.
SOLVER_LIMITS = ["--solver-rlimit=1200000000", "--solver-timeout=600000"]


def with_limits(args):
    """`args` for piac, with SOLVER_LIMITS added where they are not set."""
    extra = [f for f in SOLVER_LIMITS
             if not any(a.startswith(f.split("=")[0] + "=") for a in args)]
    return extra + args


FENCE = re.compile(r"^(\s*)```(\w*)\s*$")
DIRECTIVE = re.compile(r"^<!--\s*(example|expect|untested|source|repl)\s*:\s*(.*?)\s*-->$")


def blocks(path):
    """Yields (line, info, directives, body) for each fenced block."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    directives = {}
    i = 0
    while i < len(lines):
        m = FENCE.match(lines[i])
        if not m:
            d = DIRECTIVE.match(lines[i].strip())
            if d:
                directives[d.group(1)] = d.group(2)
            elif lines[i].strip():
                directives = {}
            i += 1
            continue
        indent, info, start = m.group(1), m.group(2), i
        body = []
        i += 1
        while i < len(lines) and lines[i].strip() != "```":
            line = lines[i]
            body.append(line[len(indent):] if line.startswith(indent) else line)
            i += 1
        yield start + 1, info, directives, body
        directives = {}
        i += 1


def matches(expected, actual):
    """Matches lines, where an expected `...` matches any run of lines."""
    if not expected:
        return not actual
    if expected[0] == "...":
        return any(matches(expected[1:], actual[k:]) for k in range(len(actual) + 1))
    return bool(actual) and expected[0] == actual[0] and matches(expected[1:], actual[1:])


def main():
    piac = os.path.abspath(sys.argv[1])
    docs = sys.argv[2:]
    pia = None
    if docs[:1] == ["--pia"]:
        pia = os.path.abspath(docs[1])
        docs = docs[2:]
    failures = []
    checked = 0
    for doc in docs:
        with tempfile.TemporaryDirectory() as tmp:
            count = 0
            for line, info, directives, body in blocks(doc):
                where = f"{doc}:{line}"
                if info == "ocaml":
                    if "untested" in directives:
                        continue
                    if "repl" in directives:
                        with open(os.path.join(tmp, directives["repl"]), "w",
                                  encoding="utf-8") as f:
                            f.write("\n".join(body) + "\n")
                        continue
                    count += 1
                    if "source" in directives:
                        with open(directives["source"], encoding="utf-8") as f:
                            source = f.read().splitlines()
                        if source != body:
                            failures.append(
                                f"{where}: the block differs from {directives['source']}")
                    name = directives.get("example", f"example{count}.pia")
                    with open(os.path.join(tmp, name), "w", encoding="utf-8") as f:
                        f.write("\n".join(body) + "\n")
                    want = 1 if directives.get("expect") == "fail" else 0
                    run = subprocess.run([piac] + with_limits(["--verify", name]), cwd=tmp,
                                         capture_output=True, text=True)
                    checked += 1
                    if run.returncode != want:
                        failures.append(
                            f"{where}: piac --verify {name} exited {run.returncode}, "
                            f"expected {want}\n{run.stdout}{run.stderr}")
                elif info == "console" and body and (
                        body[0].startswith("$ piac") or
                        (pia and body[0].startswith("$ pia "))):
                    argv = shlex.split(body[0][2:])
                    stdin = None
                    if "<" in argv:
                        k = argv.index("<")
                        stdin = open(os.path.join(tmp, argv[k + 1]), encoding="utf-8")
                        argv = argv[:k] + argv[k + 2:]
                    tool = piac if argv[0] == "piac" else pia
                    args = with_limits(argv[1:]) if tool == piac else argv[1:]
                    run = subprocess.run([tool] + args, cwd=tmp, stdin=stdin,
                                         capture_output=True, text=True)
                    if stdin:
                        stdin.close()
                    checked += 1
                    actual = [l.rstrip() for l in (run.stdout + run.stderr).splitlines()]
                    expected = [l.rstrip() for l in body[1:]]
                    if not matches(expected, actual):
                        failures.append(
                            f"{where}: output of `{body[0][2:]}` differs\n"
                            "--- expected\n" + "\n".join(expected) +
                            "\n--- actual\n" + "\n".join(actual))
    for failure in failures:
        print(failure + "\n", file=sys.stderr)
    print(f"{checked} checks, {len(failures)} failed")
    return 1 if failures or checked == 0 else 0


if __name__ == "__main__":
    sys.exit(main())
