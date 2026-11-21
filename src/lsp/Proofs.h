// The deep check behind pia-lsp's proof diagnostics (ADR 0021): IRGen's
// type errors and the verifier's goals for one document. The interface has
// no MLIR types, so the server builds without LLVM; Proofs.cpp, in the
// `proofs` target, implements it with IRGen and the verifier.

#ifndef PIA_LSP_PROOFS_H
#define PIA_LSP_PROOFS_H

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace pia::lsp {

struct Goal {
  enum class Status { Proved, Failed, Skipped };
  Status status = Status::Skipped;
  uint32_t line = 0;    // 1-based
  uint32_t column = 0;  // 1-based, in bytes
  std::string kind;     // "nooverflow", "inbounds", "ensures", ...
  std::string claim;    // "'+' does not overflow u8"
  std::string method;   // "intervals", "smt", ... or why it failed/skipped
  std::vector<std::pair<std::string, std::string>> counterexample;
};

struct CompileError {
  uint32_t line = 0;    // 1-based
  uint32_t column = 0;  // 1-based, in bytes
  std::string message;
};

struct ProofReport {
  std::vector<CompileError> errors;  // from Sema and IRGen
  std::vector<Goal> goals;           // empty when there are errors
};

// Lowers and verifies `source`. `path` names the file in locations.
using ProofChecker = std::function<ProofReport(std::string_view source,
                                               const std::string &path)>;

// The checker built on IRGen and the verifier, with a per-goal timeout.
ProofReport checkProofs(std::string_view source, const std::string &path,
                        unsigned timeoutMs);

}  // namespace pia::lsp

#endif  // PIA_LSP_PROOFS_H
