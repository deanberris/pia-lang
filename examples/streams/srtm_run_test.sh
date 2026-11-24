#!/bin/sh
# Runs the SRTM program on the 256 x 256 crop of N46E008 and checks what
# it found: every cell reached by the flood, every cell drained, sediment
# conserved, and the parallel run equal to the sequential one.
set -eu
srtm="$(pwd)/$1"
tile="$(pwd)/$2"
cd "${TEST_TMPDIR:-$(mktemp -d)}"
"$srtm" "$tile" crop.png > out.txt
cat out.txt
grep -q '^tile: 256x256 cells, relief 2909 m, ' out.txt
grep -q '^fill: [0-9]* cells raised, 0 unreached ' out.txt
grep -q '^directions: .* outlets drain 65536 cells ' out.txt
grep -q '^sediment: 4 steps, sequential, .*; 6553600 in all, 6553600 at the start$' out.txt
grep -q '^basins: 4 steps, .* 0 cells differ$' out.txt
for f in crop.png crop-quarter.png; do
  [ "$(head -c 4 "$f" | tail -c 3)" = PNG ] || { echo "$f is not a PNG" >&2; exit 1; }
done
