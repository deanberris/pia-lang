#include "cert/Advisory.h"

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <sstream>

#include "llvm/ADT/Twine.h"
#include "llvm/Support/ErrorHandling.h"

namespace pia::cert {

namespace {

// A TOML value of the kinds advisories use.
struct Value {
  enum Kind { String, Array, Table } kind = String;
  std::string string;
  std::vector<std::string> array;
  std::vector<std::pair<std::string, Value>> table;
};

class Parser {
public:
  explicit Parser(std::string_view text) : text(text) {}

  // Each top-level `key = value`, in order, or false with `error` set.
  bool parse(std::vector<std::pair<std::string, Value>> &out) {
    while (true) {
      skip(/*newlines=*/true);
      if (at >= text.size())
        return true;
      std::string key;
      Value value;
      if (!keyValue(key, value))
        return false;
      out.emplace_back(std::move(key), std::move(value));
      skip(/*newlines=*/false);
      if (at < text.size() && text[at] != '\n')
        return fail("expected the end of the line after '" + key + "'");
    }
  }

  std::string error;

private:
  std::string_view text;
  size_t at = 0;
  unsigned line = 1;

  bool fail(const std::string &message) {
    error = "line " + std::to_string(line) + ": " + message;
    return false;
  }

  // Skips blanks and comments, and line ends too when `newlines`.
  void skip(bool newlines) {
    while (at < text.size()) {
      char ch = text[at];
      if (ch == ' ' || ch == '\t' || ch == '\r') {
        ++at;
      } else if (ch == '#') {
        while (at < text.size() && text[at] != '\n')
          ++at;
      } else if (ch == '\n' && newlines) {
        ++at;
        ++line;
      } else {
        return;
      }
    }
  }

  bool keyValue(std::string &key, Value &value) {
    size_t start = at;
    while (at < text.size() &&
           (std::isalnum(static_cast<unsigned char>(text[at])) ||
            text[at] == '_' || text[at] == '-'))
      ++at;
    if (at == start)
      return fail("expected a key");
    key = std::string(text.substr(start, at - start));
    skip(/*newlines=*/false);
    if (at >= text.size() || text[at] != '=')
      return fail("expected '=' after '" + key + "'");
    ++at;
    skip(/*newlines=*/false);
    return parseValue(value);
  }

  bool parseString(std::string &out) {
    ++at; // the opening quote
    while (at < text.size() && text[at] != '"') {
      char ch = text[at++];
      if (ch == '\n')
        return fail("a string ends at the end of its line");
      if (ch != '\\') {
        out += ch;
        continue;
      }
      if (at >= text.size())
        break;
      char escaped = text[at++];
      switch (escaped) {
      case 'n':
        out += '\n';
        break;
      case 't':
        out += '\t';
        break;
      case '"':
      case '\\':
        out += escaped;
        break;
      default:
        return fail(std::string("unknown escape '\\") + escaped + "'");
      }
    }
    if (at >= text.size())
      return fail("a string is not closed");
    ++at; // the closing quote
    return true;
  }

  bool parseValue(Value &value) {
    if (at >= text.size())
      return fail("expected a value");
    if (text[at] == '"') {
      value.kind = Value::String;
      return parseString(value.string);
    }
    if (text[at] == '[') {
      value.kind = Value::Array;
      ++at;
      while (true) {
        skip(/*newlines=*/true);
        if (at < text.size() && text[at] == ']') {
          ++at;
          return true;
        }
        if (at >= text.size() || text[at] != '"')
          return fail("an array holds only strings here");
        std::string element;
        if (!parseString(element))
          return false;
        value.array.push_back(std::move(element));
        skip(/*newlines=*/true);
        if (at < text.size() && text[at] == ',')
          ++at;
        else if (at >= text.size() || text[at] != ']')
          return fail("expected ',' or ']' in an array");
      }
    }
    if (text[at] == '{') {
      value.kind = Value::Table;
      ++at;
      while (true) {
        skip(/*newlines=*/false);
        if (at < text.size() && text[at] == '}') {
          ++at;
          return true;
        }
        std::string key;
        Value inner;
        if (!keyValue(key, inner))
          return false;
        value.table.emplace_back(std::move(key), std::move(inner));
        skip(/*newlines=*/false);
        if (at < text.size() && text[at] == ',')
          ++at;
        else if (at >= text.size() || text[at] != '}')
          return fail("expected ',' or '}' in an inline table");
      }
    }
    return fail("expected a string, an array or an inline table");
  }
};

// The range in a `{ introduced = "...", fixed = "..." }` table.
bool readRange(const Value &v, const std::string &what, Range &r,
               std::string &error) {
  if (v.kind != Value::Table) {
    error = what + " must be a table with introduced and fixed";
    return false;
  }
  for (const auto &[key, inner] : v.table) {
    if (inner.kind != Value::String ||
        (key != "introduced" && key != "fixed")) {
      error = what + " has an unknown entry '" + key + "'";
      return false;
    }
    (key == "introduced" ? r.introduced : r.fixed) = inner.string;
  }
  if (r.introduced.empty()) {
    error = what + " names no introduced version";
    return false;
  }
  return true;
}

// A version split into its release numbers and, for a piac build between
// releases, the commit count after `+`.
struct Parts {
  std::vector<std::string> release;
  std::optional<unsigned long> commits;
};

Parts split(std::string_view v) {
  Parts p;
  size_t plus = v.find('+');
  std::string_view release = v.substr(0, plus);
  if (plus != std::string_view::npos) {
    std::string_view build = v.substr(plus + 1);
    std::string_view count = build.substr(0, build.find('.'));
    if (!count.empty() &&
        count.find_first_not_of("0123456789") == std::string_view::npos &&
        count.size() < 18)
      p.commits = std::stoul(std::string(count));
  }
  size_t start = 0;
  while (start <= release.size()) {
    size_t dot = release.find('.', start);
    if (dot == std::string_view::npos)
      dot = release.size();
    p.release.emplace_back(release.substr(start, dot - start));
    start = dot + 1;
  }
  return p;
}

// Compares two release components, as numbers when both are.
int comparePart(const std::string &a, const std::string &b) {
  bool numbers = !a.empty() && !b.empty() &&
                 a.find_first_not_of("0123456789") == std::string::npos &&
                 b.find_first_not_of("0123456789") == std::string::npos;
  if (!numbers)
    return a.compare(b);
  std::string x = a.substr(std::min(a.find_first_not_of('0'), a.size() - 1));
  std::string y = b.substr(std::min(b.find_first_not_of('0'), b.size() - 1));
  if (x.size() != y.size())
    return x.size() < y.size() ? -1 : 1;
  return x.compare(y);
}

std::string join(const std::vector<std::string> &items) {
  std::string out;
  for (const std::string &s : items)
    out += (out.empty() ? "" : ",") + s;
  return out;
}

// The advisories compiled in: `kBuiltin`, one string per file, then
// nullptr.
#include "src/cert/Advisories.inc"

} // namespace

std::optional<Advisory> parseAdvisory(std::string_view text,
                                      std::string &error) {
  Parser parser(text);
  std::vector<std::pair<std::string, Value>> entries;
  if (!parser.parse(entries)) {
    error = parser.error;
    return std::nullopt;
  }
  Advisory a;
  auto string = [&](const std::string &key, const Value &v, std::string &into) {
    if (v.kind != Value::String) {
      error = "'" + key + "' must be a string";
      return false;
    }
    into = v.string;
    return true;
  };
  auto strings = [&](const std::string &key, const Value &v,
                     std::vector<std::string> &into) {
    if (v.kind != Value::Array) {
      error = "'" + key + "' must be an array of strings";
      return false;
    }
    into = v.array;
    return true;
  };
  for (const auto &[key, v] : entries) {
    bool ok = true;
    if (key == "id") {
      ok = string(key, v, a.id);
    } else if (key == "summary") {
      ok = string(key, v, a.summary);
    } else if (key == "severity") {
      ok = string(key, v, a.severity);
    } else if (key == "fixed_by") {
      ok = string(key, v, a.fixedBy);
    } else if (key == "engines") {
      ok = strings(key, v, a.engines);
    } else if (key == "lean") {
      ok = strings(key, v, a.lean);
    } else if (key == "piac") {
      a.piac.emplace();
      ok = readRange(v, "piac", *a.piac, error);
    } else if (key == "solver") {
      if (v.kind != Value::Table) {
        error = "'solver' must be a table of solver ranges";
        return std::nullopt;
      }
      for (const auto &[name, range] : v.table) {
        Range r;
        if (!readRange(range, "solver." + name, r, error))
          return std::nullopt;
        a.solvers.emplace_back(name, r);
      }
    } else {
      error = "unknown key '" + key + "'";
      return std::nullopt;
    }
    if (!ok)
      return std::nullopt;
  }
  if (a.id.rfind("PIA-", 0) != 0) {
    error = "the advisory's id must start with PIA-";
    return std::nullopt;
  }
  if (a.summary.empty()) {
    error = a.id + " has no summary";
    return std::nullopt;
  }
  if (a.severity != "unsound" && a.severity != "incomplete") {
    error = a.id + ": severity must be \"unsound\" or \"incomplete\"";
    return std::nullopt;
  }
  if (!a.piac && a.solvers.empty() && a.lean.empty()) {
    error = a.id + " names no piac range, solver range or Lean proof";
    return std::nullopt;
  }
  return a;
}

std::vector<Advisory> builtinAdvisories() {
  std::vector<Advisory> out;
  for (const char *text : kBuiltin) {
    if (!text) // the list ends with nullptr, so it is never empty
      break;
    std::string error;
    std::optional<Advisory> a = parseAdvisory(text, error);
    // The files are checked by tests/cert, so a bad one is a build bug.
    if (!a)
      llvm::report_fatal_error(
          llvm::Twine("malformed advisory compiled in: " + error));
    out.push_back(std::move(*a));
  }
  return out;
}

bool readAdvisories(const std::string &dir, std::vector<Advisory> &into,
                    std::string &error) {
  std::error_code ec;
  std::vector<std::filesystem::path> files;
  for (const auto &entry : std::filesystem::directory_iterator(dir, ec))
    if (entry.path().extension() == ".toml")
      files.push_back(entry.path());
  if (ec) {
    error = dir + ": " + ec.message();
    return false;
  }
  std::sort(files.begin(), files.end());
  for (const std::filesystem::path &file : files) {
    std::ifstream in(file);
    std::stringstream text;
    text << in.rdbuf();
    std::optional<Advisory> a = parseAdvisory(text.str(), error);
    if (!a) {
      error = file.string() + ": " + error;
      return false;
    }
    auto same = std::find_if(into.begin(), into.end(),
                             [&](const Advisory &b) { return b.id == a->id; });
    if (same != into.end())
      *same = std::move(*a);
    else
      into.push_back(std::move(*a));
  }
  return true;
}

int compareVersions(std::string_view a, std::string_view b) {
  Parts x = split(a), y = split(b);
  // Builds on main are totally ordered by their commit count.
  if (x.commits && y.commits && *x.commits != *y.commits)
    return *x.commits < *y.commits ? -1 : 1;
  size_t n = std::max(x.release.size(), y.release.size());
  for (size_t i = 0; i < n; ++i) {
    std::string p = i < x.release.size() ? x.release[i] : "0";
    std::string q = i < y.release.size() ? y.release[i] : "0";
    if (int c = comparePart(p, q))
      return c;
  }
  // A release comes before the builds that follow it.
  if (x.commits.has_value() != y.commits.has_value())
    return x.commits ? 1 : -1;
  return 0;
}

bool inRange(std::string_view version, const Range &r) {
  if (compareVersions(version, r.introduced) < 0)
    return false;
  return r.fixed.empty() || compareVersions(version, r.fixed) < 0;
}

std::optional<std::string> matches(const Certificate &c, const Advisory &a) {
  if (a.severity != "unsound")
    return std::nullopt;
  std::string why;
  if (a.piac && !c.prover.empty() && c.prover != "dev" &&
      inRange(c.prover, *a.piac))
    why = "was proved by piac " + c.prover;
  for (const auto &[name, range] : a.solvers) {
    if (!why.empty())
      break;
    for (const Solver &s : c.solvers)
      if (s.name == name && inRange(s.version, range)) {
        why = "was proved with " + s.name + " " + s.version;
        break;
      }
  }
  if (why.empty())
    return std::nullopt;
  if (a.engines.empty())
    return why;
  // A certificate that does not list its engines may have used any.
  if (!c.engines)
    return why + ", and its certificate does not say which proof engines "
                 "it used";
  std::vector<std::string> used;
  for (const std::string &e : a.engines)
    if (std::find(c.engines->begin(), c.engines->end(), e) != c.engines->end())
      used.push_back(e);
  if (used.empty())
    return std::nullopt;
  return why + ", and its proofs used " + join(used);
}

} // namespace pia::cert
