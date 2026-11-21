#!/bin/sh
# edges_buggy.pia reads past the end of the image, so piac --verify must
# fail with a counterexample, and piac --emit=obj must refuse it.
set -u
piac="$1"
src="$2"
out="$("$piac" --verify "$src" 2>&1)"
status=$?
echo "$out"
[ "$status" -eq 1 ] || { echo "expected exit 1, got $status" >&2; exit 1; }
echo "$out" | grep -q 'failed: the index is within bounds' || exit 1
echo "$out" | grep -q 'counterexample:' || exit 1
if "$piac" --emit=obj -o "${TEST_TMPDIR:-/tmp}/buggy.o" "$src" 2>/dev/null; then
  echo "piac --emit=obj compiled a program with a failed goal" >&2
  exit 1
fi
