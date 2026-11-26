// Spreads placed on the GPU (ADR 0068, step 3): each `scf.for` that IRGen
// marked `pia.place = "gpu"` becomes a Metal kernel, compiled while piac
// runs and embedded in the object, and a call of the Metal shim that runs
// it.

#ifndef PIA_GPU_PLACE_H
#define PIA_GPU_PLACE_H

#include <cstdint>
#include <string>
#include <vector>

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/ArrayRef.h"

namespace pia::gpu {

// The symbol of the status IRGen leaves after a placed spread, which this
// lowering replaces with the run's status.
inline constexpr const char *kStatusSymbol = "pia$gpu$status";

// Replaces each placed spread in `module`, which is in core MLIR (arith,
// memref, scf and func), with a call of `pia_gpu_run` from the Metal shim:
//
// - the calls in its body are inlined, and the body must then use only
//   integer arithmetic, loads and stores of integer buffers and structured
//   control flow (the device rules of ADR 0068, section 1);
// - the body becomes a gpu.func, one thread per iteration, lowered to
//   SPIR-V, translated to the Metal Shading Language by SPIRV-Cross and
//   compiled by Xcode's Metal toolchain (`xcrun metal`, fast math off);
// - the .metallib and the kernel's name become constants of the module,
//   and the run's status replaces the status IRGen left after the loop.
mlir::LogicalResult lowerPlacedSpreads(mlir::ModuleOp module);

// Compiles MSL to a .metallib with xcrun. False with `error` set if the
// toolchain is missing or the compiler fails.
bool compileMetal(const std::string &msl, std::vector<uint8_t> &metallib,
                  std::string &error);

} // namespace pia::gpu

#endif
