// The Pia lexer: the lexical grammar of docs/grammar.md, including the
// adjacency rules (`name<`, `name{`, `. `) and the column-1 layout rule.

#ifndef PIA_SYNTAX_LEXER_H
#define PIA_SYNTAX_LEXER_H

#include <string_view>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Token.h"

namespace pia::syntax {

struct LexOptions {
  // Read the buffer as a literate `.pia.md` file: Markdown prose, with code
  // only in fenced `pia` blocks (ADR 0029).
  bool literate = false;
  // Where to keep the comments (and, in a literate file, the prose). Null
  // drops them.
  std::vector<RawComment> *comments = nullptr;
};

// Tokenizes the whole buffer. The result always ends with an Eof token.
// Errors are reported to `diags`; lexing stops at the first one.
std::vector<Token> tokenize(std::string_view source, Diagnostics &diags,
                            const LexOptions &options = {});

// Whether a file name names a literate Pia file (`*.pia.md`).
bool isLiterateFileName(std::string_view path);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_LEXER_H
