// The Pia parser: recursive descent, with precedence climbing over the
// operator table for binary operators. It implements the phrase grammar and
// the disambiguation rules in docs/grammar.md (ADR 0019).

#ifndef PIA_SYNTAX_PARSER_H
#define PIA_SYNTAX_PARSER_H

#include <functional>
#include <map>
#include <string>
#include <string_view>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::syntax {

// How a binary operator binds: its precedence level (1 binds loosest) and
// associativity. A level may have one decimal place, `prec 6.5`, so `level`
// holds tenths: 65. Operators are declared by `let meta operator` items
// (ADR 0008); the standard ones live in the prelude.
struct Fixity {
  enum class Assoc { Left, Right, None };
  int level = 0;
  Assoc assoc = Assoc::Left;
  bool operator==(const Fixity &o) const {
    return level == o.level && assoc == o.assoc;
  }
};
using OperatorTable = std::map<std::string, Fixity, std::less<>>;

// The source of the prelude every program imports (src/syntax/Prelude.cpp).
std::string_view preludeSource();

// The fixities the prelude declares.
const OperatorTable &preludeOperators();

// Adds the fixity of every top-level `let meta operator` in `program` to
// `table`. A later declaration of an operator replaces an earlier one.
void collectOperators(const Node &program, OperatorTable &table);

// Parses a whole file into a Program node. On a syntax error the parser
// reports it, skips to the next top-level item and carries on, so one run
// reports every broken item. Check `diags.hasErrors()` before using the tree.
// Binary operators take their fixity from `operators`; one missing from it
// gets a level from its first character, as in OCaml (docs/grammar.md).
// Every comment is kept, attached to the node it describes (ADR 0029). With
// `literate`, the source is a `.pia.md` file: Markdown prose, with code in
// fenced `pia` blocks.
NodePtr parseProgram(std::string_view source, Diagnostics &diags,
                     const OperatorTable &operators, bool literate = false);

// The same, with the prelude's operators and those the program declares:
// when it declares any, it is parsed again with them.
NodePtr parseProgram(std::string_view source, Diagnostics &diags,
                     bool literate = false);

// Parses a sequence of contract clauses (`requires ...`, `ensures ...`) on
// their own, as in a design-doc fragment. Returns a Contracts node.
NodePtr parseContractFragment(std::string_view source, Diagnostics &diags);

// `@solver(...)` on a theory (ADR 0036) applies to each of its members
// that has no `@solver` of its own: it is copied into their attributes.
void applyTheoryAttrs(Node &theory, const Node &attrs);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_PARSER_H
