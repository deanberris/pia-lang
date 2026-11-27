#!/bin/sh
# Runs D8 directions, the picture and the sediment pull step on the GPU over
# the 256 x 256 crop of N46E008 and checks that they match the CPU, cell for
# cell.
set -eu
"$1" "$2" > out.txt || { cat out.txt; exit 1; }
cat out.txt
grep -q '^tile: 256x256 cells$' out.txt
grep -q '^directions: .* 0 cells differ$' out.txt
grep -q '^render: .* 0 cells differ$' out.txt
grep -q '^pull: .* on both: yes; 0 cells differ$' out.txt
# Every buffer the stages pass is page-aligned, so none is copied but the
# scalars of the single runs, eight bytes each. The pull step's waves are
# dispatches of one command buffer a step, whose scalars are set in it.
grep -Eq '^buffers: [1-9][0-9]* wrapped in place, [0-9]+ copied \([0-9]+ bytes\); [1-9][0-9]* dispatches in sequences$' out.txt
