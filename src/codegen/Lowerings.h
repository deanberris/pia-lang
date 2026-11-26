// Lowerings written in Pia (ADR 0065, step 1): a function marked
// `@lower("mlir")` keeps its Pia body for the verifier, and codegen puts the
// MLIR in its place. docs/codegen.md, "Lowerings written in Pia", describes
// the splices and the passes.
//
// IRGen checks the attribute and marks the function (`pia.lower`, the text;
// `pia.lower_at`, where the attribute is; `pia.lower_name` on each
// argument). After lowerToCore, applyLowerings splices the core values and
// types into the text, parses it with MLIR's own parser, and replaces the
// body. In this step every lowering is trusted, so each one is listed in
// `--trust-report` and in the object's certificate.

#ifndef PIA_CODEGEN_LOWERINGS_H
#define PIA_CODEGEN_LOWERINGS_H

#include <string>
#include <vector>

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LLVM.h"

namespace mlir {
class OpPassManager;
} // namespace mlir

namespace pia::codegen {

// One lowering, as the trust report and the certificate record it.
struct Lowering {
  std::string function;         // the function's symbol
  std::string where;            // the attribute, as file:line:col
  std::string text;             // the MLIR after splicing
  std::string hash;             // SHA-256 of `text`, lowercase hex
  std::vector<std::string> ops; // the ops `text` uses, sorted, no duplicates
};

// Loads the dialects a lowering's MLIR may use: linalg, tensor,
// bufferization, transform and affine, besides those lowerToCore produces.
void loadLoweringDialects(mlir::MLIRContext &ctx);

// Replaces the body of each function marked `pia.lower` with its MLIR form,
// once lowerToCore has given every argument its core type. `$name` becomes
// the argument for the parameter `name` and `$name.type` its type. The text
// is parsed as the body of a function with the same signature, followed by
// `return` when the function returns nothing, and verified. Then the MLIR
// may write, free or pass to an op of unknown effects only the buffers of
// `out` and `inout` parameters (the operand-effect check). An error is
// reported at the attribute with MLIR's message, and returns failure.
//
// With `enabled` false (`piac --lower=off`) every body stays and only the
// marks are removed. Each lowering applied is appended to `applied` when it
// is given, and the module is marked so that lowerToLLVM runs the passes
// below.
mlir::LogicalResult applyLowerings(mlir::ModuleOp module, bool enabled,
                                   std::vector<Lowering> *applied = nullptr);

// The lowerings of a module that has not been compiled yet, such as one the
// verifier has just proved: applyLowerings on a copy, after eraseContracts
// and lowerToCore. Errors are reported as applyLowerings reports them.
mlir::FailureOr<std::vector<Lowering>> describeLowerings(mlir::ModuleOp module);

// The splice-and-parse check, and the operand-effect check, before
// anything is proved (ADR 0065, step 2): applyLowerings on a copy, so an
// error in a lowering's MLIR is reported at the attribute whatever piac
// was asked to do. A module that lowerToCore cannot compile yet is not
// checked here; codegen reports why if it is compiled.
mlir::LogicalResult checkLowerings(mlir::ModuleOp module);

// Whether applyLowerings replaced a body in `module`, and so lowerToLLVM
// needs addLoweringPasses. Clears the mark.
bool takeLoweredMark(mlir::ModuleOp module);

// The passes that take what lowerings produce to the dialects lowerToLLVM
// already lowers: linalg to loops, then memref's reshapes to plain
// descriptors (expand-strided-metadata) and affine to arith and scf.
void addLoweringPasses(mlir::OpPassManager &pm);

} // namespace pia::codegen

#endif // PIA_CODEGEN_LOWERINGS_H
