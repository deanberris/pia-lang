// Verifier v0 (milestone M5): proves the obligations of a lowered module.
// docs/verifier.md describes the obligations, the encoding and its limits.

#ifndef PIA_VERIFY_VERIFIER_H
#define PIA_VERIFY_VERIFIER_H

#include <string>
#include <vector>

#include "dialect/ContractDialect.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Location.h"

namespace pia::verify {

enum class Status { Proved, Failed, Skipped };

struct ModelValue {
  std::string name;   // a parameter name, or a label such as "result"
  std::string value;  // decimal, or true/false
};

struct Outcome {
  Status status = Status::Skipped;
  contract::ObligationKind kind = contract::ObligationKind::assert_;
  std::string where;   // "file:line:col"
  std::string function;  // the enclosing function's symbol name
  std::string claim;   // what must hold, e.g. "'+' does not overflow u8"
  std::string method;  // "intervals" or "smt" when proved, else the reason
  std::vector<ModelValue> counterexample;
  unsigned long long cost = 0;  // Z3's resource count, with reportCost
};

struct Options {
  unsigned timeoutMs = 10000;  // per obligation, wall clock
  // Z3's deterministic resource limit per obligation; 0 for none. Unlike
  // the timeout, it does not depend on how busy the machine is.
  unsigned rlimit = 0;
  bool reportCost = false;     // record each query's resource use
  bool dumpSmt = false;        // print each query's SMT-LIB to stderr
};

// Checks every function in `module`, in order, and marks each op whose
// obligations all hold with `pia.proved = "intervals"` or `"smt"`. It first
// replaces record values with their fields (transforms/ScalarizeRecords.h),
// so the module afterwards has no records.
std::vector<Outcome> verifyModule(mlir::ModuleOp module,
                                  const Options &options = {});

// "file:line:col" for the innermost file location in `loc`.
std::string formatLoc(mlir::Location loc);

}  // namespace pia::verify

#endif  // PIA_VERIFY_VERIFIER_H
