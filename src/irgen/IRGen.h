// IRGen: lowers the scalar subset of Pia to the pia and pia_contract
// dialects (milestone M4). docs/irgen.md describes the lowering.

#ifndef PIA_IRGEN_IRGEN_H
#define PIA_IRGEN_IRGEN_H

#include <string_view>

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/IR/OwningOpRef.h"
#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// Loads every dialect IRGen emits into `ctx`.
void loadDialects(mlir::MLIRContext &ctx);

// Lowers a parsed program. Returns null and reports to `diags` if the
// program is outside the subset or ill-typed. `filename` goes into the
// ops' locations.
mlir::OwningOpRef<mlir::ModuleOp> generate(const syntax::Node &program,
                                           std::string_view filename,
                                           mlir::MLIRContext &ctx,
                                           syntax::Diagnostics &diags);

}  // namespace pia::irgen

#endif  // PIA_IRGEN_IRGEN_H
