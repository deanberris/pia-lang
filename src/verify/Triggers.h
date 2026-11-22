#ifndef PIA_VERIFY_TRIGGERS_H
#define PIA_VERIFY_TRIGGERS_H

#include <set>
#include <string>
#include <vector>

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"

namespace pia::verify {

// One trigger of an axiom (ADR 0036): terms of its contracts, calls of
// theory functions, that together mention every parameter. When the
// solver meets an instance of the terms, it instantiates the axiom there.
struct Trigger {
  std::vector<mlir::Value> terms;  // values in the axiom's function
  std::string text;                // as written: "Lip.seq f g"
  std::set<std::string> functions; // every theory function in the terms
};

struct AxiomTriggers {
  std::vector<Trigger> triggers;
  std::string error;  // why there is none, when `triggers` is empty
};

// The theory a function belongs to (its `pia.theory` attribute), or "".
std::string theoryOf(mlir::func::FuncOp f);

// An axiom's triggers: those `@trigger` sets, or else every smallest term
// that mentions all its parameters. Each trigger is a separate pattern, so
// any of them instantiates the axiom. An axiom with no parameters needs
// none. A term qualifies when it is a call of a theory function whose
// arguments are parameters, constants or such calls.
AxiomTriggers axiomTriggers(mlir::ModuleOp module, mlir::func::FuncOp axiom);

}  // namespace pia::verify

#endif  // PIA_VERIFY_TRIGGERS_H
