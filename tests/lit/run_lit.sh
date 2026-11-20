#!/usr/bin/env bash
# A minimal lit: runs every `// RUN:` line of a test file.
#
#   %s     the test file
#   <tool> each tool passed on the command line, by its file name
#          (pia-opt, piac, FileCheck)
#   not    inverts the exit status of the command after it
#
# Usage: run_lit.sh <test file> <tool>...
#
# A .pia test keeps its RUN and CHECK lines inside a `(* ... *)` comment.
set -euo pipefail
TEST="$1"
shift

not() { if "$@"; then return 1; else return 0; fi; }
for tool in "$@"; do
  name="$(basename "$tool")"
  path="$(cd "$(dirname "$tool")" && pwd)/$name"
  eval "$name() { \"$path\" \"\$@\"; }"
done

ran=0
while IFS= read -r line; do
  cmd="${line#*RUN:}"
  cmd="${cmd//%s/$TEST}"
  echo "RUN: $cmd"
  if ! eval "set -o pipefail; $cmd"; then
    echo "FAILED: $cmd" >&2
    exit 1
  fi
  ran=$((ran + 1))
done < <(grep -E '^// RUN:' "$TEST")

if [ "$ran" -eq 0 ]; then
  echo "no RUN lines in $TEST" >&2
  exit 1
fi
