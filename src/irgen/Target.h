#ifndef PIA_IRGEN_TARGET_H
#define PIA_IRGEN_TARGET_H

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

// Whether `program` names `Target`, as `Target.x` or a type `Target.t`,
// and does not define an item of that name itself.
bool usesTargetTheory(const syntax::Node &program);

// Puts the theory `Target` and the model for `triple` in front of
// `program`'s items, both marked "builtin": flattenTheories neither checks
// their names against the program's nor proves the model again, since
// tests/verify/target_theory.pia proves every model once, when the
// compiler is tested. Returns false, with an error, if Pia has no model
// for `triple`.
bool addTargetTheory(syntax::Node &program, std::string_view triple,
                     syntax::Diagnostics &diags);

} // namespace pia::irgen

#endif // PIA_IRGEN_TARGET_H
