#!/usr/bin/env bash
# A minimal lit: runs every `// RUN:` line of a test file.
#
#   %s        the test file
#   pia-opt   the pia-opt binary
#   FileCheck the FileCheck binary
#   not       inverts the exit status of the command after it
#
# Usage: run_lit.sh <pia-opt> <FileCheck> <test file>
set -euo pipefail
PIA_OPT="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
FILECHECK="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
TEST="$3"

not() { if "$@"; then return 1; else return 0; fi; }
pia-opt() { "$PIA_OPT" "$@"; }
FileCheck() { "$FILECHECK" "$@"; }

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
