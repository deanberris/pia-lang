#ifndef PIA_CODEGEN_ARRAYRESULTS_H
#define PIA_CODEGEN_ARRAYRESULTS_H

// Arrays are values. A function whose result is an array (after records
// are scalarized, a record result's array fields too) cannot hand back its
// own stack storage, so codegen gives it a hidden output buffer instead:
// the caller makes one in its own frame (`pia.region`) and passes it, and
// each `return` copies the array into it (`pia.copy`). The verifier has
// already run on the value form, so this is codegen's own.

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"

namespace pia::codegen {

mlir::LogicalResult arrayResultsToBuffers(mlir::ModuleOp module);

} // namespace pia::codegen

#endif // PIA_CODEGEN_ARRAYRESULTS_H
