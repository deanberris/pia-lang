// IRGen: lowers the scalar subset of Pia to the pia and pia_contract
// dialects (milestone M4). docs/irgen.md describes the lowering.

#ifndef PIA_IRGEN_IRGEN_H
#define PIA_IRGEN_IRGEN_H

#include <string>
#include <string_view>
#include <vector>

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
struct Options {
  // `piac --explain-overloads=file:line`: each call of an overloaded or
  // generic function on this line (0 for none) explains which candidates
  // it had, which it removed and why, and which it chose (ADR 0035).
  unsigned explainLine = 0;
  std::vector<syntax::Diagnostic> *explanations = nullptr;
  // The program's text, which a box over a concept reads its
  // requirements' contracts from (ADR 0046).
  std::string_view source;
  // The triple code is generated for, which picks the model of the
  // built-in theory `Target` (ADR 0049); empty for the host's.
  std::string triple;
};

mlir::OwningOpRef<mlir::ModuleOp> generate(const syntax::Node &program,
                                           std::string_view filename,
                                           mlir::MLIRContext &ctx,
                                           syntax::Diagnostics &diags,
                                           const Options &options = {});

}  // namespace pia::irgen

#endif  // PIA_IRGEN_IRGEN_H
