#!/bin/sh
# Writes the header that gives piac its version (Version.h), from Bazel's
# stable status file $1, to $2. A build without stamping passes /dev/null,
# and a status without STABLE_PIA_VERSION, so either is `dev`.
version=$(sed -n 's/^STABLE_PIA_VERSION //p' "$1")
case "$version" in
  *[!0-9A-Za-z.+-]*) echo "stamp.sh: bad version '$version'" >&2; exit 1 ;;
esac
printf '#define PIA_PROVER_VERSION "%s"\n' "${version:-dev}" > "$2"
