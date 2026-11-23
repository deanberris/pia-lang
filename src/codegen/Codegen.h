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
#include <vector>

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Support/LLVM.h"

namespace llvm {
class LLVMContext;
class Module;
class raw_pwrite_stream;
}  // namespace llvm

namespace pia::codegen {

// The targets piac compiles for (ADR 0049). The default is the host piac
// was built for, and `--target` and `--cpu` choose another. Bazel always
// passes both, from the platform it builds for (tools/piac/targets.bzl).
inline constexpr const char *kAppleSiliconTriple = "arm64-apple-macosx14.0.0";
inline constexpr const char *kAppleSiliconCpu = "apple-m1";
inline constexpr const char *kLinuxX86Triple = "x86_64-unknown-linux-gnu";
inline constexpr const char *kLinuxX86Cpu = "x86-64-v3";

struct Options {
#if defined(__x86_64__) && defined(__linux__)
  std::string triple = kLinuxX86Triple;
  std::string cpu = kLinuxX86Cpu;
#else
  std::string triple = kAppleSiliconTriple;
  std::string cpu = kAppleSiliconCpu;
#endif
  unsigned optLevel = 2;
  // Witness symbols (docs/abi.md, Layer 1): one byte each, defined for
  // every interface the module provides and referenced for every interface
  // it imports, so a link or load against a module whose interface hash
  // differs fails with an undefined `pia$w$...` symbol.
  std::vector<std::string> providedWitnesses, requiredWitnesses;
  // The object's certificate (src/cert/Certificate.h), encoded, put in the
  // target's certificate section. Empty writes none.
  std::string certificate;
};

// The witness symbol of interface `iface` of `module`, whose canonical
// artifact is `text`: `pia$w$<module>$<iface>$<hash>`, the module's dots
// spelled '$', with the first 128 bits of the text's SHA-256 in lowercase
// base32 (docs/abi.md).
std::string witnessSymbol(const std::string &module, const std::string &iface,
                          llvm::StringRef text);

// Loads every dialect the lowering produces into `ctx`.
void loadDialects(mlir::MLIRContext &ctx);

// Removes contracts once they are proved, with the values only they use.
void eraseContracts(mlir::ModuleOp module);

// Lowers pia types and ops. Reports an error at each op v0 cannot lower.
mlir::LogicalResult lowerToCore(mlir::ModuleOp module);

// Lowers to the llvm dialect. Each public function becomes an internal
// function and a C-callable entry point with the source name (codegen.md,
// "C ABI"). With `exportsOnly`, as when piac compiles a module, only the
// functions a module exports get entry points (ADR 0039): with their C
// name from an `@abi(c)` interface, or mangled with the module's path,
// `pia$Pixels$blend`. Every other function stays internal.
mlir::LogicalResult lowerToLLVM(mlir::ModuleOp module,
                                bool exportsOnly = false);

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
