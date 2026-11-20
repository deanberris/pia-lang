// The Pia parser: recursive descent, with precedence climbing over the
// operator table for binary operators. It implements the phrase grammar and
// the disambiguation rules in docs/grammar.md (ADR 0019).

#ifndef PIA_SYNTAX_PARSER_H
#define PIA_SYNTAX_PARSER_H

#include <string_view>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::syntax {

// Parses a whole file into a Program node. On a syntax error the parser
// reports it, skips to the next top-level item and carries on, so one run
// reports every broken item. Check `diags.hasErrors()` before using the tree.
NodePtr parseProgram(std::string_view source, Diagnostics &diags);

// Parses a sequence of contract clauses (`requires ...`, `ensures ...`) on
// their own, as in a design-doc fragment. Returns a Contracts node.
NodePtr parseContractFragment(std::string_view source, Diagnostics &diags);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_PARSER_H
