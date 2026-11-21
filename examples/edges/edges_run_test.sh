#!/bin/sh
# Runs the demo in a scratch directory and checks that it wrote two BMPs of
# the same size and that the edge map is not blank.
set -eu
edges="$(pwd)/$1"
cd "${TEST_TMPDIR:-$(mktemp -d)}"
"$edges" > out.txt
cat out.txt
for f in edges-input.bmp edges-output.bmp; do
  [ "$(head -c 2 "$f")" = BM ] || { echo "$f is not a BMP" >&2; exit 1; }
done
[ "$(wc -c < edges-input.bmp)" -eq "$(wc -c < edges-output.bmp)" ]
grep -q '^320x200 pixels, edges written to edges-output.bmp$' out.txt
# Strong edges print as '@' in the text preview.
sed -n '/^edges:$/,$p' out.txt | grep -q '@'
