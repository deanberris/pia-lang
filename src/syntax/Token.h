// Tokens produced by the Pia lexer. The kinds and their spellings follow
// docs/grammar.md and the reference lexer in grammar/pia_lexer.py.

#ifndef PIA_SYNTAX_TOKEN_H
#define PIA_SYNTAX_TOKEN_H

#include <cstdint>
#include <string>
#include <string_view>

namespace pia::syntax {

// A digit separator in a number literal: `1_000_000` or `1'000'000`
// (docs/grammar.md). Every reader of a literal's text skips both.
inline bool isDigitSeparator(char c) { return c == '_' || c == '\''; }

struct SourceLoc {
  uint32_t line = 0;   // 1-based
  uint32_t column = 0; // 1-based
  uint32_t offset = 0; // byte offset into the buffer
};

// One row per group of token kinds; clang-format would reflow the table.
// clang-format off
#define PIA_TOKEN_KINDS(X)                                                     \
  /* keywords */                                                               \
  X(Let) X(Rec) X(Meta) X(In) X(Type) X(Of) X(Where) X(If) X(Then) X(Else)     \
  X(Match) X(With) X(For) X(Spread) X(While) X(Step) X(Do) X(Done) X(Spec)     \
  X(Lemma)                                                                     \
  X(Requires) X(Reads) X(Ensures) X(Invariant) X(Decreases) X(Assert) X(Assume)         \
  X(Forall) X(Exists) X(Interface) X(Sig) X(Module) X(Struct) X(End)           \
  X(Import) X(Operator) X(True) X(False) X(Borrowed) X(Moved) X(Out)           \
  X(Inout) X(Fixed) X(Mutable) X(Handle) X(Defer) X(As)                        \
  /* names and literals */                                                     \
  X(Ident) X(Int) X(Float) X(String) X(QIdent) X(SpliceIdent) X(SpliceOpen)    \
  X(QuoteOpen) X(Attr) X(AttrOpen) X(TargsOpen) X(TargsClose) X(LBraceAdj)     \
  X(Hole)                                                                      \
  /* punctuation */                                                            \
  X(LParen) X(RParen) X(LBracket) X(RBracket) X(LBrace) X(RBrace)              \
  X(DotLBracket) X(Comma) X(Colon) X(Semi) X(Sep) X(Dot) X(QDot) X(DotDot)     \
  /* operators with fixed meaning */                                           \
  X(Arrow) X(FatArrow) X(LArrow) X(Eq) X(Bar)                                  \
  /* operators whose precedence comes from the operator table */               \
  X(Op)                                                                        \
  X(Eof)
// clang-format on

enum class TokenKind : uint8_t {
#define PIA_TOKEN_ENUM(name) name,
  PIA_TOKEN_KINDS(PIA_TOKEN_ENUM)
#undef PIA_TOKEN_ENUM
};

const char *tokenKindName(TokenKind kind);

struct Token {
  TokenKind kind = TokenKind::Eof;
  std::string_view text; // points into the source buffer
  SourceLoc loc;
};

// A comment, as the lexer found it (docs/grammar.md, "Whitespace and
// comments"; ADR 0029). The parser attaches each one to a syntax node.
struct RawComment {
  enum class Style : uint8_t { Line, Block, Doc, Prose };
  Style style = Style::Block;
  std::string text;        // the content without its delimiters, trimmed
  SourceLoc loc;           // where it starts
  uint32_t end = 0;        // byte offset just past it
  uint32_t endLine = 0;    // the line it ends on
  bool ownLine = false;    // only whitespace before it on its first line
  size_t tokensBefore = 0; // how many tokens the lexer had produced
};

const char *commentStyleName(RawComment::Style style);

} // namespace pia::syntax

#endif // PIA_SYNTAX_TOKEN_H
