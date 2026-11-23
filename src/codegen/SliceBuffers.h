#ifndef PIA_CODEGEN_SLICEBUFFERS_H
#define PIA_CODEGEN_SLICEBUFFERS_H

// A buffer whose elements are slices, such as the slots of a vector's
// boxes, becomes two buffers before lowering: one of the elements'
// addresses and one of their lengths (ADR 0048, section 4). A load
// rebuilds the slice from both, and a store records both. The verifier
// has already run on the array-of-arrays form, so this is codegen's own.

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"

namespace pia::codegen {

mlir::LogicalResult splitSliceBuffers(mlir::ModuleOp module);

} // namespace pia::codegen

#endif // PIA_CODEGEN_SLICEBUFFERS_H
