#ifndef PIA_CODEGEN_PHASES_H
#define PIA_CODEGEN_PHASES_H

// A spread with collectives (ADR 0086, section 5) runs as phases: the code
// between two collectives becomes its own `scf.parallel` over the range,
// whose join is the barrier, and the if and for statements that hold a
// collective are lifted out of the parallel loops, which their uniform
// conditions allow. A collective is a call of a function marked
// `pia.collective`, made once between two phases; each slice it gathers
// is a buffer of the spread's count, a cell of which each iteration of
// the phase before it fills.

#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/ADT/StringRef.h"

namespace pia::codegen {

// The declarations a gathered slice is a call of, one per element type.
constexpr llvm::StringLiteral kGatherPrefix = "pia$par$gather$";

// Splits `spread`, an `scf.for` marked `pia.collectives` whose body calls
// collectives, into phases, and erases it.
mlir::LogicalResult splitIntoPhases(mlir::scf::ForOp spread);

// Erases the gathers' declarations once no call is left.
void eraseCollectiveDeclarations(mlir::ModuleOp module);

} // namespace pia::codegen

#endif // PIA_CODEGEN_PHASES_H
