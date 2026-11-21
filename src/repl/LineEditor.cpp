#include "repl/LineEditor.h"

#include <termios.h>
#include <unistd.h>

#include <cstdio>
#include <fstream>
#include <iostream>

namespace pia::repl {

namespace {

constexpr size_t kHistoryLimit = 1000;

// Puts the terminal in raw mode for as long as it lives.
class RawMode {
 public:
  RawMode() {
    if (tcgetattr(STDIN_FILENO, &saved_) != 0) return;
    termios raw = saved_;
    raw.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
    raw.c_cflag |= CS8;
    raw.c_lflag &= ~(ECHO | ICANON | IEXTEN | ISIG);
    raw.c_cc[VMIN] = 1;
    raw.c_cc[VTIME] = 0;
    ok_ = tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw) == 0;
  }
  ~RawMode() {
    if (ok_) tcsetattr(STDIN_FILENO, TCSAFLUSH, &saved_);
  }
  bool ok() const { return ok_; }

 private:
  termios saved_{};
  bool ok_ = false;
};

int readByte() {
  unsigned char c;
  ssize_t n = ::read(STDIN_FILENO, &c, 1);
  return n == 1 ? c : -1;
}

void write(const std::string &s) {
  ssize_t ignored = ::write(STDOUT_FILENO, s.data(), s.size());
  (void)ignored;
}

// History entries are stored one per line, with newlines as "\n" and
// backslashes doubled.
std::string escape(const std::string &s) {
  std::string out;
  for (char c : s) {
    if (c == '\\') out += "\\\\";
    else if (c == '\n') out += "\\n";
    else out += c;
  }
  return out;
}

std::string unescape(const std::string &s) {
  std::string out;
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] == '\\' && i + 1 < s.size()) {
      out += s[i + 1] == 'n' ? '\n' : s[i + 1];
      ++i;
    } else {
      out += s[i];
    }
  }
  return out;
}

}  // namespace

LineEditor::LineEditor(std::string historyFile)
    : historyFile_(std::move(historyFile)) {
  if (historyFile_.empty()) return;
  std::ifstream in(historyFile_);
  std::string line;
  while (std::getline(in, line))
    if (!line.empty()) history_.push_back(unescape(line));
}

LineEditor::~LineEditor() {
  if (historyFile_.empty() || !isTerminal()) return;
  std::ofstream out(historyFile_, std::ios::trunc);
  size_t first = history_.size() > kHistoryLimit ? history_.size() - kHistoryLimit : 0;
  for (size_t i = first; i < history_.size(); ++i) out << escape(history_[i]) << "\n";
}

bool LineEditor::isTerminal() {
  return isatty(STDIN_FILENO) && isatty(STDOUT_FILENO);
}

void LineEditor::remember(const std::string &entry) {
  if (entry.empty()) return;
  if (!history_.empty() && history_.back() == entry) return;
  history_.push_back(entry);
}

std::optional<std::string> LineEditor::read(const std::string &prompt) {
  interrupted_ = false;
  if (isTerminal()) {
    std::cout.flush();
    std::optional<std::string> line = readRaw(prompt);
    if (line || interrupted_) return line;
  }
  std::string line;
  if (!std::getline(std::cin, line)) return std::nullopt;
  return line;
}

std::optional<std::string> LineEditor::readRaw(const std::string &prompt) {
  RawMode raw;
  if (!raw.ok()) return std::nullopt;
  std::string buf;
  size_t pos = 0;
  // Up and Down step through the history. A recalled multi-line cell is
  // edited as one line, with its newlines turned into spaces.
  size_t hist = history_.size();
  std::string pending;  // the line being typed before stepping into history

  auto refresh = [&] {
    std::string shown = buf;
    for (char &c : shown)
      if (c == '\n') c = ' ';
    std::string out = "\r" + prompt + shown + "\x1b[K";
    size_t back = buf.size() - pos;
    if (back) out += "\x1b[" + std::to_string(back) + "D";
    write(out);
  };
  auto setLine = [&](const std::string &s) {
    buf = s;
    for (char &c : buf)
      if (c == '\n') c = ' ';
    pos = buf.size();
  };

  refresh();
  for (;;) {
    int c = readByte();
    if (c < 0) return std::nullopt;
    switch (c) {
      case '\r':
      case '\n':
        write("\r\n");
        return buf;
      case 3:  // Ctrl-C
        write("^C\r\n");
        interrupted_ = true;
        return std::string();
      case 4:  // Ctrl-D
        if (buf.empty()) {
          write("\r\n");
          return std::nullopt;
        }
        if (pos < buf.size()) buf.erase(pos, 1);
        break;
      case 127:
      case 8:  // Backspace
        if (pos > 0) buf.erase(--pos, 1);
        break;
      case 1: pos = 0; break;            // Ctrl-A
      case 5: pos = buf.size(); break;   // Ctrl-E
      case 2: if (pos) --pos; break;     // Ctrl-B
      case 6: if (pos < buf.size()) ++pos; break;  // Ctrl-F
      case 11: buf.erase(pos); break;    // Ctrl-K
      case 21:                           // Ctrl-U
        buf.erase(0, pos);
        pos = 0;
        break;
      case 23: {                         // Ctrl-W
        size_t start = pos;
        while (start > 0 && buf[start - 1] == ' ') --start;
        while (start > 0 && buf[start - 1] != ' ') --start;
        buf.erase(start, pos - start);
        pos = start;
        break;
      }
      case 12:                           // Ctrl-L
        write("\x1b[H\x1b[2J");
        break;
      case 16:                           // Ctrl-P
      case 14: {                         // Ctrl-N
        bool up = c == 16;
        if (up && hist > 0) {
          if (hist == history_.size()) pending = buf;
          setLine(history_[--hist]);
        } else if (!up && hist < history_.size()) {
          ++hist;
          setLine(hist == history_.size() ? pending : history_[hist]);
        }
        break;
      }
      case 27: {  // escape sequences: arrows, Home, End, Delete
        int a = readByte();
        if (a == 'b' || a == 'f') {  // Alt-B, Alt-F: by word
          if (a == 'b') {
            while (pos > 0 && buf[pos - 1] == ' ') --pos;
            while (pos > 0 && buf[pos - 1] != ' ') --pos;
          } else {
            while (pos < buf.size() && buf[pos] == ' ') ++pos;
            while (pos < buf.size() && buf[pos] != ' ') ++pos;
          }
          break;
        }
        if (a != '[' && a != 'O') break;
        int b = readByte();
        if (b >= '0' && b <= '9') {
          int tilde = readByte();
          if (tilde != '~') break;
          if (b == '1' || b == '7') pos = 0;
          if (b == '4' || b == '8') pos = buf.size();
          if (b == '3' && pos < buf.size()) buf.erase(pos, 1);
          break;
        }
        switch (b) {
          case 'A':
            if (hist > 0) {
              if (hist == history_.size()) pending = buf;
              setLine(history_[--hist]);
            }
            break;
          case 'B':
            if (hist < history_.size()) {
              ++hist;
              setLine(hist == history_.size() ? pending : history_[hist]);
            }
            break;
          case 'C': if (pos < buf.size()) ++pos; break;
          case 'D': if (pos) --pos; break;
          case 'H': pos = 0; break;
          case 'F': pos = buf.size(); break;
          default: break;
        }
        break;
      }
      default:
        if (c >= 32 || c == '\t') {
          buf.insert(pos++, 1, c == '\t' ? ' ' : static_cast<char>(c));
        }
        break;
    }
    refresh();
  }
}

}  // namespace pia::repl
