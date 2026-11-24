// Replaces every record value with its fields (docs/irgen.md, "Records").
//
// Records are values, so a function that takes a `pixel` takes its four
// fields, one that returns a `pixel` returns four results, and `pia.record`
// and `pia.field` disappear. The verifier and code generation then only see
// scalars, arrays and slices. Each parameter's fields are named after it,
// as in `p.r`, so counterexamples read naturally.

#ifndef PIA_TRANSFORMS_SCALARIZERECORDS_H
#define PIA_TRANSFORMS_SCALARIZERECORDS_H

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LLVM.h"

namespace pia::transforms {

// Does nothing to a module without records.
mlir::LogicalResult scalarizeRecords(mlir::ModuleOp module);

// The types a value of `t` becomes, in order: a record's fields, depth
// first, a buffer of records as one buffer per field, or `t` itself. A
// recursive value's payload (ADR 0047) is passed as these.
void recordLeaves(mlir::Type t, llvm::SmallVectorImpl<mlir::Type> &out);

}  // namespace pia::transforms

#endif  // PIA_TRANSFORMS_SCALARIZERECORDS_H
