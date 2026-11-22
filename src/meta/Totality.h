// The totality check for type-level metaprograms (ADR 0035, "Constraints
// are total"). A metaprogram that a type or a `where` predicate calls must
// terminate, so which overloads survive a call never depends on a step
// budget.

#ifndef PIA_META_TOTALITY_H
#define PIA_META_TOTALITY_H

#include <functional>
#include <optional>
#include <set>
#include <string>

#include "syntax/Syntax.h"

namespace pia::meta {

// Checks the `let meta` item on its own: it calls no impure builtin, its
// local functions do not recurse, it refers to itself only by calling
// itself, and every such call is on a strictly smaller argument in one
// parameter position they share. An argument is smaller when it is a
// component of the parameter: `element p`, an element of `field_types p`
// or of `type_args p` as `map` or `fold` hands it to a lambda, a name that
// a `match` on `p` binds below its top (`e` in `[e]` or `option e`), or a
// component of one of those.
//
// The other metaprograms it names go to `callees`, for the caller to check
// in turn: `isGlobal` says whether a name is a top-level metaprogram. The
// reason it is not total, or nothing.
std::optional<std::string> checkOwnTotality(
    const syntax::Node &item,
    const std::function<bool(const std::string &)> &isGlobal,
    std::set<std::string> &callees);

}  // namespace pia::meta

#endif  // PIA_META_TOTALITY_H
