#!/bin/sh
# Runs each program with the same arguments and checks that it prints the
# expected answer (ADR 0075, section 3). Output on stderr counts too, because
# plb2's Zig programs print there.
#
# usage: same_output_test.sh <expected> "<args>" <program>...
expected=$1
args=$2
shift 2
status=0
for program in "$@"; do
  # shellcheck disable=SC2086 # args is a list of words
  got=$("$program" $args 2>&1)
  if [ "$got" = "$expected" ]; then
    echo "ok: $program"
  else
    echo "FAILED: $program printed '$got', expected '$expected'"
    status=1
  fi
done
exit $status
