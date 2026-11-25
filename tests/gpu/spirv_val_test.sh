#!/bin/sh
# spirv-val accepts the SPIR-V that piac --emit=spirv made from add.mlir.
set -eu
"$1" --target-env vulkan1.1 "$2"
echo "spirv-val: $2 is valid SPIR-V"
