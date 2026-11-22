// Front-end analysis of one document for pia-lsp (ADR 0021): syntax
// diagnostics, document symbols, name resolution for hover and
// go-to-definition, and completion candidates. It uses only src/syntax, so
// it builds without LLVM.

#ifndef PIA_LSP_ANALYSIS_H
#define PIA_LSP_ANALYSIS_H

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Lint.h"
#include "syntax/Syntax.h"

namespace pia::lsp {

// A half-open byte range in the document.
struct Range {
  uint32_t begin = 0;
  uint32_t end = 0;
};

// An LSP position: 0-based line and UTF-16 code unit within the line.
struct Position {
  uint32_t line = 0;
  uint32_t character = 0;
};

// Maps between byte offsets, the compiler's 1-based line and byte column,
// and LSP positions.
class TextIndex {
 public:
  explicit TextIndex(std::string_view text);
  Position position(uint32_t offset) const;
  uint32_t offset(Position pos) const;
  // From a 1-based line and 1-based byte column, clamped to the text.
  uint32_t offsetOfLineColumn(uint32_t line, uint32_t column) const;
  uint32_t size() const { return static_cast<uint32_t>(text_.size()); }

 private:
  std::string_view text_;
  std::vector<uint32_t> lineStarts_;
};

enum class Severity { Error = 1, Warning = 2, Information = 3, Hint = 4 };

struct Diag {
  Range range;
  Severity severity = Severity::Error;
  std::string source;  // "pia", "pia-lint" or "pia-verify"
  std::string code;    // a goal kind for proof diagnostics, a lint name, or empty
  std::string message;
};

// LSP SymbolKind values used here.
enum class SymbolKind {
  Module = 2,
  Class = 5,
  Method = 6,
  Interface = 11,
  Function = 12,
  Variable = 13,
  Constant = 14,
  Operator = 25,
};

struct Symbol {
  std::string name;
  SymbolKind kind = SymbolKind::Variable;
  std::string detail;  // a one-line signature
  Range range;         // the whole item
  Range selection;     // the name
  std::vector<Symbol> children;
};

// What a name refers to.
struct Binding {
  std::string name;
  std::string role;     // "function", "value", "type", "parameter", ...
  Range nameRange;      // where it is bound
  std::string snippet;  // its definition as written, for hover
};

// The identifier or operator token around `offset`, or an empty range
// starting at `offset`.
Range tokenAt(std::string_view text, uint32_t offset);

// Byte range of the token that starts at `offset`, for diagnostics.
Range tokenFrom(std::string_view text, uint32_t offset);

class Analysis {
 public:
  // With `literate`, the text is a `.pia.md` file (ADR 0029).
  explicit Analysis(std::string text, bool literate = false);
  Analysis(const Analysis &) = delete;
  Analysis &operator=(const Analysis &) = delete;

  const std::string &text() const { return text_; }
  const TextIndex &index() const { return index_; }
  bool parsed() const { return !diags_.hasErrors(); }
  const syntax::Node *tree() const { return tree_.get(); }

  // Syntax errors, with the range of the token each one points at, then
  // the lints (ADR 0037) as warnings with source "pia-lint".
  std::vector<Diag> diagnostics() const;

  // The lints of a document that parses; empty otherwise.
  const std::vector<syntax::Lint> &lints() const { return lints_; }

  // Top-level items, with interface members and module items as children.
  std::vector<Symbol> symbols() const;

  // The binding of the name at `offset`, if it is a name and resolves.
  std::optional<Binding> resolve(uint32_t offset) const;

  // The binding of the name at `offset` and every use that resolves to it,
  // in order. Empty when the name does not resolve.
  std::vector<Range> references(uint32_t offset) const;

  // Names worth offering at `offset`: the top-level definitions, and the
  // parameters of the item that contains `offset`.
  std::vector<Binding> completions(uint32_t offset) const;

 private:
  std::string text_;
  TextIndex index_;
  syntax::Diagnostics diags_;
  syntax::NodePtr tree_;
  std::vector<syntax::Lint> lints_;
};

// Reserved words, for completion.
const std::vector<std::string_view> &keywords();

}  // namespace pia::lsp

#endif  // PIA_LSP_ANALYSIS_H
