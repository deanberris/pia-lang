// Solver strategies (ADR 0036): `@solver(...)` on a theory, lemma or
// function names how Z3 solves its goals, as `check-sat-using` would.

#ifndef PIA_VERIFY_STRATEGY_H
#define PIA_VERIFY_STRATEGY_H

#include <optional>
#include <string>

#include "z3++.h"

namespace pia::verify {

// Why `strategy` is not a Z3 strategy the verifier can run, or nothing.
// A strategy is a tactic's name, such as `nlsat`, or a combination in
// SMT-LIB's syntax for `check-sat-using`: `(then simplify smt)`,
// `(or-else nlsat smt)`, `(par-or a b)`, `(par-then a b)`, `(repeat t n)`,
// `(try-for t ms)` and `(using-params t :key value ...)` (ADR 0036). It
// affects how fast a goal is proved, never whether it is.
std::optional<std::string> checkStrategy(const std::string &strategy);

// A solver for `strategy`: Z3's default when it is empty, or one made
// from its tactics. Throws std::runtime_error for an invalid strategy.
z3::solver solverFor(z3::context &ctx, const std::string &strategy);

}  // namespace pia::verify

#endif  // PIA_VERIFY_STRATEGY_H
