// Diagnostics with source locations, printed with a caret under the column.

#ifndef PIA_SYNTAX_DIAGNOSTICS_H
#define PIA_SYNTAX_DIAGNOSTICS_H

#include <ostream>
#include <string>
#include <string_view>
#include <vector>

#include "syntax/Token.h"

namespace pia::syntax {

struct Diagnostic {
  SourceLoc loc;
  std::string message;
};

class Diagnostics {
 public:
  void error(SourceLoc loc, std::string message) {
    errors_.push_back({loc, std::move(message)});
  }
  bool hasErrors() const { return !errors_.empty(); }
  const std::vector<Diagnostic> &errors() const { return errors_; }
  // How many errors there are, and dropping those after the first `n`:
  // for work whose errors only mean it cannot be done (ADR 0043).
  size_t count() const { return errors_.size(); }
  void truncate(size_t n) {
    if (n < errors_.size()) errors_.resize(n);
  }

  // Prints "file:line:col: error: message", the source line, and a caret.
  void print(std::ostream &os, std::string_view filename,
             std::string_view source) const;

 private:
  std::vector<Diagnostic> errors_;
};

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_DIAGNOSTICS_H
