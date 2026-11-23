#ifndef PIA_IRGEN_TARGET_H
#define PIA_IRGEN_TARGET_H

#include <map>
#include <string>
#include <string_view>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// The source of the built-in theory `Target` and its models, one per
// target (ADR 0049, section 3), as written in src/irgen/Target.pia.
std::string_view targetTheorySource();

// The model of `Target` for `triple`, such as "x86_64_linux" for
// x86_64-unknown-linux-gnu, or "" if Pia has no model for it. An empty
// triple means the host's.
std::string targetModelFor(std::string_view triple);

// Whether `program` names `Target`, as `Target.x` or a type `Target.t`, or
// marks an item `@target(m)`, and does not define an item `Target` itself.
bool usesTargetTheory(const syntax::Node &program);

// Puts the theory `Target` and the model for `triple` in front of
// `program`'s items, both marked "builtin": flattenTheories neither checks
// their names against the program's nor proves the model again, since
// tests/verify/target_theory.pia proves every model once, when the
// compiler is tested.
//
// It also handles `@target(m)` on a function (ADR 0049): the function is
// compiled only for the target whose model is `m`, and is removed from the
// program for any other. Only a function that is `@target(m)` itself may
// use it, on every target, so code that compiles for one target does not
// fail to compile for another. Each kept `@target(m)` function goes in
// `targetOf`, function -> m, so that its proofs see m's values.
//
// Returns false, with an error, if Pia has no model for `triple` or an
// `@target` is wrong.
bool addTargetTheory(syntax::Node &program, std::string_view triple,
                     syntax::Diagnostics &diags,
                     std::map<std::string, std::string> *targetOf = nullptr);

} // namespace pia::irgen

#endif // PIA_IRGEN_TARGET_H
