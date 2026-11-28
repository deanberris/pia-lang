#ifndef PIA_CODEGEN_PHASES_H
#define PIA_CODEGEN_PHASES_H

// A spread with collectives (ADR 0086, section 4) runs as phases: the code
// between two collectives becomes its own `scf.parallel` over the range,
// whose join is the barrier, and the if and for statements that
// hold a collective are lifted out of the parallel loops, which their
// uniform conditions allow. An `all_reduce` is an atomic read-modify-write
// of one cell at the end of the phase before it.

#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"

namespace pia::codegen {

// Splits `spread`, an `scf.for` marked `pia.collectives` whose body holds
// calls of `pia$par$...`, into phases, and erases it.
mlir::LogicalResult splitIntoPhases(mlir::scf::ForOp spread);

// Erases the declarations of the collectives once no call is left.
void eraseCollectiveDeclarations(mlir::ModuleOp module);

} // namespace pia::codegen

#endif // PIA_CODEGEN_PHASES_H
