#!/usr/bin/env python3
"""Checks that CODEMAP.md still describes the repository.

    python3 tools/codemap/check.py [--root DIR]

It fails when
- a tracked file under src/, lib/ or tools/ (other than BUILD.bazel) is not
  named in CODEMAP.md,
- a directory under tests/, examples/ or skills/ is not named,
- an ADR in docs/adr/ has no mention of its number,
- a repository path written in `backticks` in CODEMAP.md does not exist.

A name counts if it appears as a path, or as a brace group such as
`src/syntax/Lexer.{h,cpp}` or `tests/verify/{bump,pool}.pia`. The check is
textual and needs no Bazel, so it runs in seconds in CI and in any session.
"""

import argparse
import itertools
import os
import re
import subprocess
import sys

COVERED_FILES = ("src/", "lib/", "tools/")
COVERED_DIRS = ("tests", "examples", "skills")
PATH_ROOTS = ("src/", "lib/", "tools/", "tests/", "examples/", "skills/", "docs/",
              "grammar/", "editors/", "third_party/", ".github/", ".claude/")


def expand(token):
    """`a/{b,c}.h` -> [`a/b.h`, `a/c.h`]; several groups multiply out."""
    parts = re.split(r"\{([^{}]*)\}", token)
    fixed, groups = parts[0::2], [g.split(",") for g in parts[1::2]]
    out = []
    for combo in itertools.product(*groups):
        s = fixed[0]
        for g, f in zip(combo, fixed[1:]):
            s += g + f
        out.append(s)
    return out


def mentioned_paths(text):
    names = set()
    for tok in re.findall(r"`([^`\s]+)`", text):
        tok = tok.rstrip(".,:;")
        for p in expand(tok):
            names.add(p.rstrip("/"))
    return names


def tracked(root):
    out = subprocess.run(["git", "ls-files"], cwd=root, capture_output=True, text=True, check=True)
    return [l for l in out.stdout.splitlines() if l]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=os.path.join(os.path.dirname(__file__), "..", ".."))
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    with open(os.path.join(root, "CODEMAP.md"), encoding="utf-8") as f:
        text = f.read()
    names = mentioned_paths(text)
    files = tracked(root)
    problems = []

    for f in files:
        if f.startswith(COVERED_FILES) and os.path.basename(f) != "BUILD.bazel" and f not in names:
            problems.append(f"not in CODEMAP.md: {f}")

    dirs = sorted({os.path.dirname(f) for f in files})
    for d in dirs:
        top = d.split("/")[0]
        depth = d.count("/")
        if top in COVERED_DIRS and depth == 1 and d not in names:
            problems.append(f"directory not in CODEMAP.md: {d}")

    for f in files:
        m = re.match(r"docs/adr/(\d{4})-", f)
        if m and not re.search(r"\b%s\b" % m.group(1), text):
            problems.append(f"ADR not in CODEMAP.md: {f}")

    for p in sorted(names):
        if p.startswith(PATH_ROOTS) and "*" not in p and "<" not in p and "NNNN" not in p:
            if not os.path.exists(os.path.join(root, p)):
                problems.append(f"CODEMAP.md names a path that does not exist: {p}")

    if problems:
        print("\n".join(problems))
        print(f"\n{len(problems)} problem(s). Update CODEMAP.md (section 7 says how).")
        return 1
    print("CODEMAP.md covers the repository.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
