#!/bin/sh
# Runs the demo in a scratch directory and checks that it wrote two PNGs
# and found streams in the synthetic terrain.
set -eu
streams="$(pwd)/$1"
cd "${TEST_TMPDIR:-$(mktemp -d)}"
"$streams" > out.txt
cat out.txt
for f in streams-input.png streams-output.png; do
  [ "$(head -c 4 "$f" | tail -c 3)" = PNG ] || { echo "$f is not a PNG" >&2; exit 1; }
done
grep -q '^384x256 cells; sinks filled in ' out.txt
grep -q 'outlets draining 98304 cells' out.txt
grep -q '^map written to streams-output.png$' out.txt
# Streams print as '~' and '#' in the text preview, and the crater as 'o'.
grep -E '^[ .:=+*~#o-]+$' out.txt > map.txt
grep -q '#' map.txt
grep -q 'o' map.txt
# A GIF too.
"$streams" streams-input.png map.gif > /dev/null
[ "$(head -c 3 map.gif)" = GIF ]
