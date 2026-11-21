// Codegen v0 (milestone M6): from verified pia IR to an object file.
// docs/codegen.md describes the lowering, the C ABI and the limits.
//
// The stages run in this order, and piac can stop after any of them:
//
//   eraseContracts   drop pia_contract ops and everything only they use
//   lowerToCore      pia to arith, scf, memref and func
//   lowerToLLVM      core dialects to the llvm dialect, plus C entry points
//   translate        llvm dialect to an optimised LLVM module
//   emitObject       LLVM module to an object file (or assembly)

#ifndef PIA_CODEGEN_CODEGEN_H
#define PIA_CODEGEN_CODEGEN_H

#include <memory>
#include <string>

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LLVM.h"

namespace llvm {
class LLVMContext;
class Module;
class raw_pwrite_stream;
}  // namespace llvm

namespace pia::codegen {

struct Options {
  std::string triple = "arm64-apple-macosx14.0.0";
  std::string cpu = "apple-m1";
  unsigned optLevel = 2;
};

// Loads every dialect the lowering produces into `ctx`.
void loadDialects(mlir::MLIRContext &ctx);

// Removes contracts once they are proved, with the values only they use.
void eraseContracts(mlir::ModuleOp module);

// Lowers pia types and ops. Reports an error at each op v0 cannot lower.
mlir::LogicalResult lowerToCore(mlir::ModuleOp module);

// Lowers to the llvm dialect. Each public function becomes an internal
// function and a C-callable entry point with the source name (codegen.md,
// "C ABI").
mlir::LogicalResult lowerToLLVM(mlir::ModuleOp module);

// Translates to LLVM IR for the target and optimises it. Returns null and
// sets `error` on failure.
std::unique_ptr<llvm::Module> translate(mlir::ModuleOp module,
                                        llvm::LLVMContext &llvmCtx,
                                        const Options &options,
                                        std::string &error);

// Writes an object file, or assembly. Returns false and sets `error` on
// failure.
bool emitObject(llvm::Module &module, const Options &options,
                llvm::raw_pwrite_stream &os, std::string &error,
                bool assembly = false);

}  // namespace pia::codegen

#endif  // PIA_CODEGEN_CODEGEN_H
