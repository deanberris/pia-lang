#!/bin/sh
# Runs the demo in a scratch directory and checks that it wrote three PNGs
# and found streams in the synthetic terrain.
set -eu
streams="$(pwd)/$1"
cd "${TEST_TMPDIR:-$(mktemp -d)}"
"$streams" > out.txt
cat out.txt
for f in streams-input.png streams-output.png streams-output-sediment.png; do
  [ "$(head -c 4 "$f" | tail -c 3)" = PNG ] || { echo "$f is not a PNG" >&2; exit 1; }
done
grep -q '^384x256 cells; sinks filled in ' out.txt
grep -q '^1276 outlets drain 98304 cells; ' out.txt
grep -q '^map written to streams-output.png$' out.txt
# Sediment transport ran, and the C side counts the same total it started
# with (main.c also exits 1 if it does not).
grep -q '^sediment: 4 steps over 98304 cells ' out.txt
grep -q '^sediment: [0-9]* units in the beds and the water, [0-9]* out, 9830400 in all; 9830400 at the start$' out.txt
grep -q '^sediment map written to streams-output-sediment.png$' out.txt
# Streams print as '~' and '#' in the text preview, and the crater as 'o'.
grep -E '^[ .:=+*~#o-]+$' out.txt > map.txt
grep -q '#' map.txt
grep -q 'o' map.txt
# The saved terrain is 16-bit, so reading it back gives the same map; and
# GIF output works too.
"$streams" streams-input.png map.gif > again.txt
[ "$(head -c 3 map.gif)" = GIF ]
grep 'lake cells' out.txt > want.txt
grep 'lake cells' again.txt | sed 's/ ([0-9.]* ms)//' > got.txt
sed -i.bak 's/ ([0-9.]* ms)//' want.txt
diff want.txt got.txt
