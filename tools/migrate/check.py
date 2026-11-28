#!/usr/bin/env python3
"""Checks that a pull request which may break old source ships a migration.

Usage: python3 tools/migrate/check.py [--base=<ref>] [--body-file=<path>]
       python3 tools/migrate/check.py --self-test

ADR 0073, section 5: every change after which source that piac accepted is
rejected, or means something else, ships a migration rule in
src/migrate/rules/ in the same pull request (docs/migrations.md). This
script cannot tell whether a change breaks anything, so it asks: a pull
request that changes the grammar, the keyword table or the prelude, or
deletes an ABI baseline, must either add or change a rule, or say why it
needs none on a line of its description:

    no-migration: only accepts more programs

It runs on every pull request in seconds (.github/workflows/migrate.yml),
which passes the description in the PR_BODY environment variable. Like
tools/skills/check.py, it makes the missing piece impossible to forget, not
impossible to skip with a reason.

Exit status: 0 when the rule holds, 1 otherwise, with one line per problem.
"""

import argparse
import os
import re
import subprocess
import sys

# Files where a change can make old source mean something else or stop
# parsing, and what each holds.
WATCHED = {
    "src/syntax/Lexer.cpp": "the lexer and its keyword table",
    "src/syntax/Token.h": "the token kinds",
    "src/syntax/Parser.cpp": "the grammar",
    "src/syntax/Parser.h": "the grammar",
    "src/syntax/Syntax.h": "the syntax tree",
    "src/syntax/Prelude.cpp": "the prelude every program sees",
}

# A deleted ABI baseline drops a published interface or layout
# (docs/abi.md, "ABI baselines").
BASELINE = re.compile(r"(^|/)abi/[^/]+\.(piai|pial)$")

RULES = "src/migrate/rules/"

EXEMPT = re.compile(r"^\s*no-migration:\s*(\S.*)$", re.MULTILINE)


def root():
    out = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                         capture_output=True, text=True,
                         cwd=os.path.dirname(os.path.abspath(__file__)))
    return out.stdout.strip() if out.returncode == 0 else os.getcwd()


def changes(base):
    """(status, path) for each file this branch changes since `base`."""
    out = subprocess.run(
        ["git", "diff", "--name-status", "--no-renames", base + "...HEAD"],
        capture_output=True, text=True, cwd=root())
    if out.returncode != 0:
        sys.exit("migrate: cannot diff against %s: %s" %
                 (base, out.stderr.strip()))
    result = []
    for line in out.stdout.splitlines():
        status, _, path = line.partition("\t")
        if path:
            result.append((status[:1], path))
    return result


def problems(changed, body):
    """What is missing, as lines: empty when the rule holds."""
    breaking = []
    for status, path in changed:
        if path in WATCHED:
            breaking.append("%s (%s)" % (path, WATCHED[path]))
        elif status == "D" and BASELINE.search(path):
            breaking.append("%s (a deleted ABI baseline)" % path)
    if not breaking:
        return []
    if any(path.startswith(RULES) for _, path in changed):
        return []
    if EXEMPT.search(body or ""):
        return []
    lines = ["changes %s, which may break old source," % p for p in breaking]
    lines.append(
        "but adds or changes no rule in %s. If old source breaks or means "
        "something else, add a migration rule (docs/migrations.md); if not, "
        "say why on a line of the pull request's description: "
        "`no-migration: <why>`." % RULES)
    return lines


def self_test():
    parser = [("M", "src/syntax/Parser.cpp")]
    rule = [("A", "src/migrate/rules/Renamed.cpp")]
    cases = [
        ([("M", "src/irgen/IRGen.cpp")], "", False),
        (parser, "", True),
        (parser, "Adds a lint.\n", True),
        (parser, "no-migration:\n", True),
        (parser, "Adds `x`.\n\nno-migration: only accepts more programs\n",
         False),
        (parser + rule, "", False),
        ([("D", "lib/Pia/abi/Pia.Core.v1.piai")], "", True),
        ([("M", "lib/Pia/abi/Pia.Core.v1.piai")], "", False),
        ([("A", "lib/Pia/abi/Pia.Core.v2.piai")], "", False),
    ]
    failed = 0
    for changed, body, fails in cases:
        if bool(problems(changed, body)) != fails:
            failed += 1
            print("migrate: self-test: %r with %r should %s" %
                  (changed, body, "fail" if fails else "pass"))
    print("migrate: self-test: %d of %d cases hold" %
          (len(cases) - failed, len(cases)))
    return 1 if failed else 0


def main():
    args = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    args.add_argument("--base", default="origin/main",
                      help="the branch the pull request merges into")
    args.add_argument("--body-file",
                      help="the pull request's description, instead of "
                      "$PR_BODY")
    args.add_argument("--self-test", action="store_true")
    opts = args.parse_args()
    if opts.self_test:
        return self_test()
    if opts.body_file:
        with open(opts.body_file, encoding="utf-8") as f:
            body = f.read()
    else:
        body = os.environ.get("PR_BODY", "")
    found = problems(changes(opts.base), body)
    for line in found:
        print("migrate: " + line)
    if not found:
        print("migrate: no change that needs a migration rule, or one is "
              "given")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
