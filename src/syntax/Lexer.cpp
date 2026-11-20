#include "syntax/Lexer.h"

#include <cctype>
#include <string>
#include <unordered_map>

namespace pia::syntax {

const char *tokenKindName(TokenKind kind) {
  switch (kind) {
#define PIA_TOKEN_NAME(name) \
  case TokenKind::name:      \
    return #name;
    PIA_TOKEN_KINDS(PIA_TOKEN_NAME)
#undef PIA_TOKEN_NAME
  }
  return "?";
}

void Diagnostics::print(std::ostream &os, std::string_view filename,
                        std::string_view source) const {
  for (const Diagnostic &d : errors_) {
    os << filename << ":" << d.loc.line << ":" << d.loc.column
       << ": error: " << d.message << "\n";
    size_t start = d.loc.offset;
    while (start > 0 && start <= source.size() && source[start - 1] != '\n')
      --start;
    size_t end = source.find('\n', start);
    if (end == std::string_view::npos) end = source.size();
    if (start <= source.size()) {
      os << "  " << source.substr(start, end - start) << "\n  ";
      for (uint32_t i = 1; i < d.loc.column; ++i) os << ' ';
      os << "^\n";
    }
  }
}

namespace {

const std::unordered_map<std::string_view, TokenKind> &keywords() {
  static const std::unordered_map<std::string_view, TokenKind> table = {
      {"let", TokenKind::Let},         {"rec", TokenKind::Rec},
      {"meta", TokenKind::Meta},       {"in", TokenKind::In},
      {"type", TokenKind::Type},       {"of", TokenKind::Of},
      {"where", TokenKind::Where},     {"if", TokenKind::If},
      {"then", TokenKind::Then},       {"else", TokenKind::Else},
      {"match", TokenKind::Match},     {"with", TokenKind::With},
      {"for", TokenKind::For},         {"spread", TokenKind::Spread},
      {"while", TokenKind::While},     {"do", TokenKind::Do},
      {"done", TokenKind::Done},       {"requires", TokenKind::Requires},
      {"ensures", TokenKind::Ensures}, {"invariant", TokenKind::Invariant},
      {"decreases", TokenKind::Decreases},
      {"assert", TokenKind::Assert},   {"assume", TokenKind::Assume},
      {"forall", TokenKind::Forall},   {"exists", TokenKind::Exists},
      {"interface", TokenKind::Interface},
      {"sig", TokenKind::Sig},         {"module", TokenKind::Module},
      {"struct", TokenKind::Struct},   {"end", TokenKind::End},
      {"import", TokenKind::Import},   {"operator", TokenKind::Operator},
      {"true", TokenKind::True},       {"false", TokenKind::False},
      {"borrowed", TokenKind::Borrowed},
      {"moved", TokenKind::Moved},     {"out", TokenKind::Out},
      {"inout", TokenKind::Inout},     {"fixed", TokenKind::Fixed},
      {"mutable", TokenKind::Mutable},
      // Alphanumeric operators in the bootstrap table.
      {"mod", TokenKind::Op},
  };
  return table;
}

bool isIdentStart(char c) {
  return std::isalpha(static_cast<unsigned char>(c)) || c == '_';
}
bool isIdentChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '\'';
}
bool isDigit(char c) { return std::isdigit(static_cast<unsigned char>(c)); }
bool isOperatorChar(char c) {
  return std::string_view("+-*/<>=|&^~!%?").find(c) != std::string_view::npos;
}

bool isItemStarter(TokenKind k) {
  switch (k) {
    case TokenKind::Let: case TokenKind::Interface: case TokenKind::Module:
    case TokenKind::Import: case TokenKind::Ident: case TokenKind::QIdent:
    case TokenKind::SpliceIdent: case TokenKind::SpliceOpen:
    case TokenKind::QuoteOpen: case TokenKind::Int: case TokenKind::Float:
    case TokenKind::String: case TokenKind::LParen: case TokenKind::LBracket:
      return true;
    default:
      return false;
  }
}

bool isOpener(TokenKind k) {
  switch (k) {
    case TokenKind::LParen: case TokenKind::LBracket: case TokenKind::LBrace:
    case TokenKind::LBraceAdj: case TokenKind::QuoteOpen:
    case TokenKind::SpliceOpen: case TokenKind::AttrOpen:
    case TokenKind::DotLBracket: case TokenKind::TargsOpen:
    case TokenKind::Sig: case TokenKind::Struct: case TokenKind::Do:
      return true;
    default:
      return false;
  }
}

bool isCloser(TokenKind k) {
  switch (k) {
    case TokenKind::RParen: case TokenKind::RBracket: case TokenKind::RBrace:
    case TokenKind::TargsClose: case TokenKind::End: case TokenKind::Done:
      return true;
    default:
      return false;
  }
}

class Lexer {
 public:
  Lexer(std::string_view src, Diagnostics &diags) : src_(src), diags_(diags) {}

  std::vector<Token> run() {
    while (!failed_) {
      skipTrivia();
      if (failed_) break;
      if (pos_ >= src_.size()) break;
      lexToken();
    }
    if (!failed_ && !targs_.empty()) {
      error(openers_[targs_.back() - 1],
            "'<' straight after a name opens type arguments, and this list "
            "is never closed; write 'a < b', with spaces, for less-than");
    } else if (!failed_ && depth_ != 0) {
      const Token &open = out_[openerIndex_.back()];
      error(open.loc, "'" + std::string(open.text) + "' is never closed");
    }
    Token eof;
    eof.kind = TokenKind::Eof;
    eof.loc = here();
    out_.push_back(eof);
    return std::move(out_);
  }

 private:
  char peek(size_t k = 0) const {
    return pos_ + k < src_.size() ? src_[pos_ + k] : '\0';
  }

  SourceLoc here() const {
    return {line_, static_cast<uint32_t>(pos_ - lineStart_ + 1),
            static_cast<uint32_t>(pos_)};
  }

  void advance(size_t n = 1) {
    for (size_t i = 0; i < n && pos_ < src_.size(); ++i) {
      if (src_[pos_] == '\n') {
        ++line_;
        lineStart_ = pos_ + 1;
      }
      ++pos_;
    }
  }

  void error(SourceLoc loc, std::string msg) {
    diags_.error(loc, std::move(msg));
    failed_ = true;
  }

  void skipTrivia() {
    for (;;) {
      char c = peek();
      if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
        advance();
      } else if (c == '(' && peek(1) == '*') {
        SourceLoc start = here();
        int depth = 0;
        for (;;) {
          if (pos_ >= src_.size()) {
            error(start, "unterminated comment");
            return;
          }
          if (peek() == '(' && peek(1) == '*') {
            ++depth;
            advance(2);
          } else if (peek() == '*' && peek(1) == ')') {
            advance(2);
            if (--depth == 0) break;
          } else {
            advance();
          }
        }
      } else {
        return;
      }
    }
  }

  void push(TokenKind kind, SourceLoc start) {
    Token t;
    t.kind = kind;
    t.loc = start;
    t.text = src_.substr(start.offset, pos_ - start.offset);
    if (kind != TokenKind::Sep && start.column == 1 && depth_ == 0 &&
        !out_.empty() && isItemStarter(kind) &&
        out_.back().kind != TokenKind::Sep) {
      Token sep;
      sep.kind = TokenKind::Sep;
      sep.loc = start;
      out_.push_back(sep);
    }
    if (isOpener(kind)) {
      ++depth_;
      openers_.push_back(start);
      openerIndex_.push_back(out_.size());
    } else if (isCloser(kind)) {
      if (depth_ == 0) {
        error(start, "'" + std::string(t.text) + "' has nothing to close");
        return;
      }
      --depth_;
      openers_.pop_back();
      openerIndex_.pop_back();
      while (!targs_.empty() && targs_.back() > depth_) targs_.pop_back();
    }
    out_.push_back(t);
  }

  void lexNumber(SourceLoc start) {
    TokenKind kind = TokenKind::Int;
    char base = static_cast<char>(std::tolower(static_cast<unsigned char>(peek(1))));
    if (peek() == '0' && (base == 'x' || base == 'b' || base == 'o')) {
      std::string_view digits = base == 'x'   ? "0123456789abcdefABCDEF_"
                                : base == 'b' ? "01_"
                                              : "01234567_";
      advance(2);
      while (peek() != '\0' && digits.find(peek()) != std::string_view::npos)
        advance();
    } else {
      while (isDigit(peek()) || peek() == '_') advance();
      if (peek() == '.' && isDigit(peek(1))) {
        kind = TokenKind::Float;
        advance();
        while (isDigit(peek()) || peek() == '_') advance();
      }
      if ((peek() == 'e' || peek() == 'E') &&
          (isDigit(peek(1)) ||
           ((peek(1) == '+' || peek(1) == '-') && isDigit(peek(2))))) {
        kind = TokenKind::Float;
        advance(2);
        while (isDigit(peek())) advance();
      }
    }
    // Type suffix: 42u8, 1i64, 0.5f32, 3usize.
    if ((peek() == 'u' || peek() == 'i' || peek() == 'f') &&
        (isDigit(peek(1)) || src_.substr(pos_ + 1, 4) == "size")) {
      advance();
      while (isIdentChar(peek())) advance();
    }
    if (isIdentChar(peek())) {
      error(here(), "malformed number literal");
      return;
    }
    push(kind, start);
  }

  void lexToken() {
    SourceLoc start = here();
    char c = peek();

    if (isIdentStart(c)) {
      while (isIdentChar(peek())) advance();
      std::string_view word = src_.substr(start.offset, pos_ - start.offset);
      TokenKind kind = TokenKind::Ident;
      auto it = keywords().find(word);
      if (it != keywords().end()) kind = it->second;
      if (word == "step" && !forHeaders_.empty() &&
          forHeaders_.back() == depth_)
        kind = TokenKind::Step;
      if (kind == TokenKind::For || kind == TokenKind::Spread) {
        forHeaders_.push_back(depth_);
      } else if (kind == TokenKind::Do && !forHeaders_.empty() &&
                 forHeaders_.back() == depth_) {
        forHeaders_.pop_back();
      }
      push(kind, start);
      if (kind == TokenKind::Ident) {
        if (peek() == '<' && peek(1) != '-' && peek(1) != '=') {
          SourceLoc s = here();
          advance();
          push(TokenKind::TargsOpen, s);
          targs_.push_back(depth_);
        } else if (peek() == '{') {
          SourceLoc s = here();
          advance();
          push(TokenKind::LBraceAdj, s);
        }
      }
      return;
    }

    if (isDigit(c)) {
      lexNumber(start);
      return;
    }

    if (c == '"') {
      advance();
      while (peek() != '"') {
        if (peek() == '\0' || peek() == '\n') {
          error(start, "unterminated string literal");
          return;
        }
        if (peek() == '\\') advance();
        advance();
      }
      advance();
      push(TokenKind::String, start);
      return;
    }

    if (c == '`') {
      advance();
      if (peek() == '(') {
        advance();
        push(TokenKind::QuoteOpen, start);
      } else if (isIdentStart(peek())) {
        while (isIdentChar(peek())) advance();
        push(TokenKind::QIdent, start);
      } else {
        error(start, "expected '(' or an identifier after '`'");
      }
      return;
    }

    if (c == '$') {
      advance();
      if (peek() == '(') {
        advance();
        push(TokenKind::SpliceOpen, start);
      } else if (isIdentStart(peek())) {
        while (isIdentChar(peek())) advance();
        push(TokenKind::SpliceIdent, start);
      } else {
        error(start, "expected '(' or an identifier after '$'");
      }
      return;
    }

    if (c == '@') {
      advance();
      if (!isIdentStart(peek())) {
        error(start, "expected an attribute name after '@'");
        return;
      }
      while (isIdentChar(peek())) advance();
      if (peek() == '(') {
        advance();
        push(TokenKind::AttrOpen, start);
      } else {
        push(TokenKind::Attr, start);
      }
      return;
    }

    if (c == '.') {
      if (peek(1) == '.' && peek(2) == '.') {
        advance(3);
        push(TokenKind::Hole, start);
      } else if (peek(1) == '.') {
        advance(2);
        push(TokenKind::DotDot, start);
      } else if (peek(1) == '[') {
        advance(2);
        push(TokenKind::DotLBracket, start);
      } else if (peek(1) == '\0' || peek(1) == ' ' || peek(1) == '\t' ||
                 peek(1) == '\r' || peek(1) == '\n') {
        // A dot followed by whitespace ends quantifier binders.
        advance();
        push(TokenKind::QDot, start);
      } else {
        advance();
        push(TokenKind::Dot, start);
      }
      return;
    }

    if (isOperatorChar(c)) {
      if (c == '>' && !targs_.empty() && targs_.back() == depth_) {
        advance();
        targs_.pop_back();
        push(TokenKind::TargsClose, start);
        return;
      }
      while (isOperatorChar(peek())) advance();
      std::string_view op = src_.substr(start.offset, pos_ - start.offset);
      TokenKind kind = TokenKind::Op;
      if (op == "->") kind = TokenKind::Arrow;
      else if (op == "=>") kind = TokenKind::FatArrow;
      else if (op == "<-") kind = TokenKind::LArrow;
      else if (op == "=") kind = TokenKind::Eq;
      else if (op == "|") kind = TokenKind::Bar;
      push(kind, start);
      return;
    }

    switch (c) {
      case ';':
        if (peek(1) == ';') {
          advance(2);
          Token sep;
          sep.kind = TokenKind::Sep;
          sep.loc = start;
          sep.text = src_.substr(start.offset, 2);
          out_.push_back(sep);
        } else {
          advance();
          push(TokenKind::Semi, start);
        }
        return;
      case '(': advance(); push(TokenKind::LParen, start); return;
      case ')': advance(); push(TokenKind::RParen, start); return;
      case '[': advance(); push(TokenKind::LBracket, start); return;
      case ']': advance(); push(TokenKind::RBracket, start); return;
      case '{': advance(); push(TokenKind::LBrace, start); return;
      case '}': advance(); push(TokenKind::RBrace, start); return;
      case ',': advance(); push(TokenKind::Comma, start); return;
      case ':': advance(); push(TokenKind::Colon, start); return;
      default:
        break;
    }
    error(start, std::string("unexpected character '") + c + "'");
  }

  std::string_view src_;
  Diagnostics &diags_;
  std::vector<Token> out_;
  size_t pos_ = 0;
  uint32_t line_ = 1;
  size_t lineStart_ = 0;
  int depth_ = 0;
  std::vector<SourceLoc> openers_;   // location of each open bracket
  std::vector<size_t> openerIndex_;  // its index in out_
  std::vector<int> targs_;       // depth just inside each open `name<`
  std::vector<int> forHeaders_;  // depth of each open `for`/`spread` header
  bool failed_ = false;
};

}  // namespace

std::vector<Token> tokenize(std::string_view source, Diagnostics &diags) {
  return Lexer(source, diags).run();
}

}  // namespace pia::syntax
