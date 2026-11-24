#ifndef PIA_SYNTAX_RECTYPES_H
#define PIA_SYNTAX_RECTYPES_H

// Recursive types (ADR 0047, step 1): which type items of a program refer
// to themselves, directly or through each other. Sema checks the rules on
// them, and the lint `needless_rec` flags a `let rec` type that is in no
// cycle.

#include <set>
#include <string>
#include <vector>

#include "syntax/Syntax.h"

namespace pia::syntax {

// A type item: `let t = type ...`, or a generic one, `let t = let (a :
// type) => type ...`. Its body, the `type ...`, and its type parameters.
struct TypeItem {
  const Node *item = nullptr;
  const Node *body = nullptr;  // the TypeValue
  std::vector<std::string> params;
  bool rec = false;            // declared `let rec`
};

// The program's type items, in order.
std::vector<TypeItem> typeItems(const Node &program);

// The names of the type items each type item mentions in its body.
std::set<std::string> typeMentions(const TypeItem &t,
                                   const std::set<std::string> &names);

// The groups of type items that refer to themselves: each strongly
// connected component of the mentions graph with a cycle, a single type
// that names itself or several that name each other.
std::vector<std::vector<const TypeItem *>> typeCycles(
    const std::vector<TypeItem> &items);

} // namespace pia::syntax

#endif // PIA_SYNTAX_RECTYPES_H
