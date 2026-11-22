// Lints: opinions about idiomatic Pia (ADR 0036, docs/idioms.md).
//
// A lint is a warning, never an error. Each one names a better way to say
// the same thing, and most carry a fix: text edits that a language server
// offers as a quick fix. They read only the syntax tree, so piac and
// pia-lsp share them without LLVM.
//
// A function opts out of a lint with `@allow(<name>)` on its return
// annotation, and piac turns lints off with --no-lint or --no-lint=<name>.

#ifndef PIA_SYNTAX_LINT_H
#define PIA_SYNTAX_LINT_H

#include <cstdint>
#include <ostream>
#include <string>
#include <string_view>
#include <vector>

#include "syntax/Syntax.h"

namespace pia::syntax {

// Replace the bytes [begin, end) of the source with `text`.
struct TextEdit {
  uint32_t begin = 0;
  uint32_t end = 0;
  std::string text;
};

struct Lint {
  std::string name;     // such as "range_requires"
  SourceLoc loc;        // where the warning points
  uint32_t end = 0;     // byte offset one past the flagged text
  std::string message;
  std::string fixTitle;          // empty when there is no fix
  std::vector<TextEdit> edits;   // in source order, not overlapping
  bool preferred = true;         // whether the fix is safe to apply blindly
};

// Every lint name, in the order docs/idioms.md lists them.
const std::vector<std::string_view> &lintNames();

// The lints for a parsed program. `source` is the text it was parsed from.
std::vector<Lint> lint(const Node &program, std::string_view source);

// Prints "file:line:col: warning: message [name]", the source line and a
// caret, like Diagnostics::print, then the fix if there is one.
void printLint(std::ostream &os, const Lint &l, std::string_view filename,
               std::string_view source);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_LINT_H
