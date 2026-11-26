// The GPU path's first half (ADR 0068, section 2): a gpu.module, with its
// kernels, lowered by upstream MLIR passes to a spirv.module, and that
// module serialised to a SPIR-V binary. SPIRV-Cross then turns the binary
// into the Metal Shading Language, outside piac.

#ifndef PIA_GPU_SPIRV_H
#define PIA_GPU_SPIRV_H

#include <cstdint>

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/DialectRegistry.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/SmallVector.h"

namespace pia::gpu {

// Registers the dialects a gpu.module and its SPIR-V lowering use: gpu,
// spirv, and the arith, memref, scf and func ops kernels are written in.
void registerDialects(mlir::DialectRegistry &registry);

// Registers the passes of the lowering with the pass registry, so that
// pia-opt can run them one at a time.
void registerPasses();

// Lowers every gpu.module in `module` to a spirv.module: memref storage
// classes, convert-gpu-to-spirv (with arith, memref, scf and func), the
// kernels' ABI attributes, and the version, capabilities and extensions
// each spirv.module needs. Each gpu.module must carry a spirv.target_env.
mlir::LogicalResult lowerToSpirv(mlir::ModuleOp module);

// Serialises the one spirv.module in `module` to a SPIR-V binary.
mlir::LogicalResult serializeSpirv(mlir::ModuleOp module,
                                   llvm::SmallVectorImpl<uint32_t> &binary);

} // namespace pia::gpu

#endif
