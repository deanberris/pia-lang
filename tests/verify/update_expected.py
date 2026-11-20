#!/usr/bin/env python3
"""Regenerates the expected report at the end of a `piac --verify` test.

    python3 tests/verify/update_expected.py <piac> tests/verify/<test>.pia

Replaces the trailing "(* Expected report ..." block with CHECK lines built
from the current output. Counterexample values become patterns, since the
solver may pick any witness; tighten the ones a test means to pin down.
Review the diff before committing: this records what piac does, right or
wrong.
"""
import os
import re
import subprocess
import sys

MARKER = "(* Expected report, in order."


def main():
    piac, path = os.path.abspath(sys.argv[1]), sys.argv[2]
    src = open(path).read()
    if MARKER in src:
        src = src[: src.index(MARKER)]
    src = src.rstrip() + "\n"
    open(path, "w").write(src)
    out = subprocess.run(
        [piac, "--verify", os.path.basename(path)],
        cwd=os.path.dirname(os.path.abspath(path)),
        capture_output=True,
        text=True,
    ).stdout
    lines = ["", MARKER]
    for line in out.rstrip("\n").split("\n"):
        if line.startswith("  counterexample:"):
            body = re.sub(r"= -?[0-9]+", "= {{-?[0-9]+}}", line.strip())
            lines.append("// CHECK-NEXT: " + body)
        else:
            lines.append("// CHECK: " + line)
    lines.append("*)")
    with open(path, "a") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
