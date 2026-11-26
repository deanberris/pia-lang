#!/bin/sh
# SPIRV-Cross translated the kernel to the Metal Shading Language: one
# kernel function, add, over three device buffers. On macOS with Xcode's
# Metal toolchain, the MSL also compiles to a .metallib.
set -eu
msl="$1"
cat "$msl"
grep -q '^kernel void add(' "$msl"
[ "$(grep -o 'device ' "$msl" | wc -l)" -ge 3 ]
if [ "$(uname)" = Darwin ]; then
  if xcrun -sdk macosx -f metallib > /dev/null 2>&1 &&
     xcrun -sdk macosx metal --version > /dev/null 2>&1; then
    dir="${TEST_TMPDIR:-$(mktemp -d)}"
    xcrun -sdk macosx metal -fno-fast-math -c "$msl" -o "$dir/add.air"
    xcrun -sdk macosx metallib "$dir/add.air" -o "$dir/add.metallib"
    [ "$(head -c 4 "$dir/add.metallib")" = MTLB ]
    echo "metal: add.metallib built"
  else
    echo "SKIPPED the .metallib: Xcode's Metal toolchain is not installed" \
      "(xcodebuild -downloadComponent MetalToolchain)"
  fi
else
  echo "SKIPPED the .metallib: Metal is macOS only"
fi
