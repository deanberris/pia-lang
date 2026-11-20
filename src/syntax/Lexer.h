// The Pia lexer: the lexical grammar of docs/grammar.md, including the
// adjacency rules (`name<`, `name{`, `. `) and the column-1 layout rule.

#ifndef PIA_SYNTAX_LEXER_H
#define PIA_SYNTAX_LEXER_H

#include <string_view>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Token.h"

namespace pia::syntax {

// Tokenizes the whole buffer. The result always ends with an Eof token.
// Errors are reported to `diags`; lexing stops at the first one.
std::vector<Token> tokenize(std::string_view source, Diagnostics &diags);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_LEXER_H
