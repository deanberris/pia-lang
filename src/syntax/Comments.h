// Comments as syntax (ADR 0029): the parser attaches every comment the lexer
// kept to the node it describes, and the meta engine reads them.

#ifndef PIA_SYNTAX_COMMENTS_H
#define PIA_SYNTAX_COMMENTS_H

#include <string>
#include <string_view>
#include <vector>

#include "syntax/Syntax.h"
#include "syntax/Token.h"

namespace pia::syntax {

// Attaches each comment in `comments` to a node of `root`, as a Comment node
// in that node's `comments`. `tokens` is the token stream `root` was parsed
// from and `source` its text. The rules are in docs/grammar.md, "Comments
// in the syntax tree".
void attachComments(Node &root, const std::vector<Token> &tokens,
                    const std::vector<RawComment> &comments,
                    std::string_view source);

// A Comment node's style ("line", "block", "doc" or "prose") and place
// ("leading", "trailing" or "detached").
std::string commentStyle(const Node &comment);
std::string commentPlace(const Node &comment);

// A new Comment node.
NodePtr makeComment(SourceLoc loc, std::string text, std::string_view style,
                    std::string_view place);

// The text of the doc and prose comments leading `node`, joined by blank
// lines; empty when there are none.
std::string docText(const Node &node);

} // namespace pia::syntax

#endif // PIA_SYNTAX_COMMENTS_H
