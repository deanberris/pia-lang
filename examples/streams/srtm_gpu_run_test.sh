#!/bin/sh
# Runs D8 directions and the picture on the GPU over the 256 x 256 crop of
# N46E008 and checks that they match the CPU, cell for cell.
set -eu
"$1" "$2" > out.txt || { cat out.txt; exit 1; }
cat out.txt
grep -q '^tile: 256x256 cells$' out.txt
grep -q '^directions: .* 0 cells differ$' out.txt
grep -q '^render: .* 0 cells differ$' out.txt
