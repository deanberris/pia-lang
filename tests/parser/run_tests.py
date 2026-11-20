"""Golden tests for `piac --dump-ast` (milestone M2).

Parses every `ocaml` block in docs/design.md and every file in
tests/grammar/valid/, comparing the tree with tests/parser/golden/. Checks
that every file in tests/grammar/invalid/ is rejected. The corpus is shared
with the reference grammar tests, so the C++ parser and the spec accept and
reject the same programs.

Usage: python3 tests/parser/run_tests.py <path/to/piac> [--update]
"""

import glob
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
GOLDEN = os.path.join(HERE, "golden")


def design_examples():
    with open(os.path.join(ROOT, "docs", "design.md")) as f:
        text = f.read()
    for i, m in enumerate(re.finditer(r"^```ocaml\n(.*?)^```", text, flags=re.S | re.M), 1):
        yield f"design_{i:02d}", m.group(1)


def valid_cases():
    for path in sorted(glob.glob(os.path.join(ROOT, "tests", "grammar", "valid", "*.pia"))):
        with open(path) as f:
            yield "valid_" + os.path.splitext(os.path.basename(path))[0], f.read()


def is_fragment(src):
    stripped = re.sub(r"\(\*.*?\*\)", "", src, flags=re.S).lstrip()
    return stripped.startswith(("requires", "ensures"))


def run_piac(piac, src, tmpdir, name):
    path = os.path.join(tmpdir, name + ".pia")
    with open(path, "w") as f:
        f.write(src)
    args = [piac, "--dump-ast", path]
    if is_fragment(src):
        args.insert(1, "--fragment=contracts")
    return subprocess.run(args, capture_output=True, text=True)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    piac = os.path.abspath(sys.argv[1])
    update = "--update" in sys.argv[2:]
    tmpdir = os.environ.get("TEST_TMPDIR") or os.path.join(HERE, ".tmp")
    os.makedirs(tmpdir, exist_ok=True)
    failures = 0
    count = 0

    for name, src in list(design_examples()) + list(valid_cases()):
        count += 1
        r = run_piac(piac, src, tmpdir, name)
        golden = os.path.join(GOLDEN, name + ".ast")
        if r.returncode != 0:
            failures += 1
            print(f"FAIL {name}: piac exited {r.returncode}\n{r.stderr}")
            continue
        if update:
            with open(golden, "w") as f:
                f.write(r.stdout)
            print(f"updated {name}")
            continue
        if not os.path.exists(golden):
            failures += 1
            print(f"FAIL {name}: no golden file; run with --update")
            continue
        with open(golden) as f:
            expected = f.read()
        if expected != r.stdout:
            failures += 1
            print(f"FAIL {name}: tree differs from {os.path.relpath(golden, ROOT)}")
        else:
            print(f"ok   {name}")

    for path in sorted(glob.glob(os.path.join(ROOT, "tests", "grammar", "invalid", "*.pia"))):
        count += 1
        name = "invalid_" + os.path.splitext(os.path.basename(path))[0]
        with open(path) as f:
            r = run_piac(piac, f.read(), tmpdir, name)
        if r.returncode == 1 and "error:" in r.stderr:
            print(f"ok   {name}: {r.stderr.splitlines()[0].split('error: ', 1)[1]}")
        else:
            failures += 1
            print(f"FAIL {name}: expected a syntax error, got exit {r.returncode}")

    print(f"\n{count - failures} of {count} passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
