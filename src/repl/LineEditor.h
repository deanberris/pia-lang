// A small line editor for the terminal REPL: cursor movement, the usual
// Emacs keys and history, with no dependency on readline or libedit.
// When standard input is not a terminal it just reads lines.

#ifndef PIA_REPL_LINEEDITOR_H
#define PIA_REPL_LINEEDITOR_H

#include <optional>
#include <string>
#include <vector>

namespace pia::repl {

class LineEditor {
 public:
  // History is loaded from and saved to `historyFile`, if it is not empty.
  explicit LineEditor(std::string historyFile = "");
  ~LineEditor();

  // Reads one line, without its newline. Returns nullopt at end of input
  // (Ctrl-D on an empty line). Ctrl-C abandons the line and returns "",
  // and sets interrupted().
  std::optional<std::string> read(const std::string &prompt);

  bool interrupted() const { return interrupted_; }

  // Adds a cell to the history (Up and Down step through it).
  void remember(const std::string &entry);

  static bool isTerminal();

 private:
  std::optional<std::string> readRaw(const std::string &prompt);

  std::string historyFile_;
  std::vector<std::string> history_;
  bool interrupted_ = false;
};

}  // namespace pia::repl

#endif  // PIA_REPL_LINEEDITOR_H
