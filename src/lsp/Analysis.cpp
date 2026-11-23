#include "lsp/Analysis.h"

#include <algorithm>
#include <functional>

#include "syntax/Comments.h"
#include "syntax/Lexer.h"
#include "syntax/Lint.h"
#include "syntax/Parser.h"

namespace pia::lsp {

using syntax::Node;
using syntax::NodeKind;
using N = syntax::NodeKind;

// ------------------------------------------------------------ TextIndex

TextIndex::TextIndex(std::string_view text) : text_(text) {
  lineStarts_.push_back(0);
  for (uint32_t i = 0; i < text.size(); ++i)
    if (text[i] == '\n')
      lineStarts_.push_back(i + 1);
}

namespace {

// Bytes in the UTF-8 sequence that starts with `lead`.
uint32_t utf8Length(unsigned char lead) {
  if (lead < 0x80)
    return 1;
  if ((lead >> 5) == 0x6)
    return 2;
  if ((lead >> 4) == 0xE)
    return 3;
  if ((lead >> 3) == 0x1E)
    return 4;
  return 1; // a stray continuation byte counts as one
}

} // namespace

Position TextIndex::position(uint32_t offset) const {
  offset = std::min<uint32_t>(offset, text_.size());
  auto it = std::upper_bound(lineStarts_.begin(), lineStarts_.end(), offset);
  uint32_t line = static_cast<uint32_t>(it - lineStarts_.begin()) - 1;
  uint32_t character = 0;
  for (uint32_t i = lineStarts_[line]; i < offset;) {
    uint32_t len = utf8Length(static_cast<unsigned char>(text_[i]));
    character += len == 4 ? 2 : 1;
    i += len;
  }
  return {line, character};
}

uint32_t TextIndex::offset(Position pos) const {
  if (pos.line >= lineStarts_.size())
    return size();
  uint32_t i = lineStarts_[pos.line];
  uint32_t units = 0;
  while (i < text_.size() && text_[i] != '\n' && units < pos.character) {
    uint32_t len = utf8Length(static_cast<unsigned char>(text_[i]));
    units += len == 4 ? 2 : 1;
    i = std::min<uint32_t>(i + len, size());
  }
  return i;
}

uint32_t TextIndex::offsetOfLineColumn(uint32_t line, uint32_t column) const {
  if (line == 0)
    return 0;
  if (line > lineStarts_.size())
    return size();
  uint32_t start = lineStarts_[line - 1];
  uint32_t end = line < lineStarts_.size() ? lineStarts_[line] : size();
  return std::min(start + (column > 0 ? column - 1 : 0), end);
}

// ------------------------------------------------------------ tokens

namespace {

bool identStart(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' ||
         static_cast<unsigned char>(c) >= 0x80;
}
bool identChar(char c) {
  return identStart(c) || (c >= '0' && c <= '9') || c == '\'';
}
bool opChar(char c) {
  return std::string_view("+-*/%<>=!&|^~@.:?").find(c) !=
         std::string_view::npos;
}

} // namespace

Range tokenAt(std::string_view text, uint32_t offset) {
  uint32_t n = static_cast<uint32_t>(text.size());
  offset = std::min(offset, n);
  auto grow = [&](auto pred) {
    uint32_t b = offset, e = offset;
    while (b > 0 && pred(text[b - 1]))
      --b;
    while (e < n && pred(text[e]))
      ++e;
    return Range{b, e};
  };
  if (offset < n && identChar(text[offset]))
    return grow(identChar);
  if (offset > 0 && identChar(text[offset - 1]))
    return grow(identChar);
  if (offset < n && opChar(text[offset]))
    return grow(opChar);
  if (offset > 0 && opChar(text[offset - 1]))
    return grow(opChar);
  return {offset, offset};
}

Range tokenFrom(std::string_view text, uint32_t offset) {
  uint32_t n = static_cast<uint32_t>(text.size());
  if (offset >= n)
    return {n, n};
  uint32_t e = offset;
  if (identChar(text[e])) {
    while (e < n && identChar(text[e]))
      ++e;
  } else if (opChar(text[e])) {
    while (e < n && opChar(text[e]))
      ++e;
  } else if (text[e] != '\n') {
    e += utf8Length(static_cast<unsigned char>(text[e]));
  }
  return {offset, std::min(e, n)};
}

const std::vector<std::string_view> &keywords() {
  static const std::vector<std::string_view> words = {
      "let",     "rec",       "meta",      "in",      "type",     "of",
      "where",   "if",        "then",      "else",    "match",    "with",
      "for",     "spread",    "while",     "do",      "done",     "requires",
      "ensures", "invariant", "decreases", "assert",  "assume",   "forall",
      "exists",  "interface", "sig",       "module",  "struct",   "end",
      "import",  "operator",  "true",      "false",   "borrowed", "moved",
      "out",     "inout",     "fixed",     "mutable", "mod",      "step",
      "handle",  "defer",     "as"};
  return words;
}

// ------------------------------------------------------------ helpers

namespace {

// The first occurrence of `name` as a whole word at or after `from`.
uint32_t findWord(std::string_view text, uint32_t from, std::string_view name) {
  if (name.empty())
    return from;
  size_t pos = from;
  while ((pos = text.find(name, pos)) != std::string_view::npos) {
    bool before = pos == 0 || !identChar(text[pos - 1]);
    size_t end = pos + name.size();
    bool after = end >= text.size() || !identChar(text[end]);
    if (before && after)
      return static_cast<uint32_t>(pos);
    pos = end;
  }
  return from;
}

std::string_view rtrim(std::string_view s) {
  while (!s.empty() && (s.back() == ' ' || s.back() == '\t' ||
                        s.back() == '\n' || s.back() == '\r'))
    s.remove_suffix(1);
  return s;
}

// At most `maxLines` lines of `s`, with "..." when cut.
std::string capLines(std::string_view s, int maxLines) {
  int lines = 0;
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] == '\n' && ++lines == maxLines)
      return std::string(rtrim(s.substr(0, i))) + "\n  ...";
  }
  return std::string(s);
}

// The first line of `s`, for symbol details.
std::string firstLine(std::string_view s) {
  size_t nl = s.find('\n');
  return std::string(rtrim(s.substr(0, nl)));
}

// Smallest source offset in a subtree (a node's own loc can lie after its
// first child's, as for a binary operator).
uint32_t startOf(const Node &n) {
  uint32_t best = n.loc.offset;
  bool any = n.loc.line != 0;
  for (const auto &k : n.kids) {
    if (!k || k->kind == N::None)
      continue;
    uint32_t s = startOf(*k);
    if (!any || s < best)
      best = s;
    any = true;
  }
  return best;
}

// Where the defined name of a `let`, `interface`, `module` or `val` is.
uint32_t nameOffset(std::string_view text, const Node &n) {
  return findWord(text, n.loc.offset, n.text);
}

const Node *kid(const Node &n, size_t i) {
  return i < n.kids.size() ? n.kids[i].get() : nullptr;
}

bool hasParams(const Node &let) {
  const Node *ps = kid(let, 0);
  return ps && ps->kind == N::Params && !ps->kids.empty();
}

// A `let`'s text up to its body: the name, parameters, return annotation
// and contracts, as written.
std::string letHeader(std::string_view text, const Node &let) {
  const Node *body = kid(let, 3);
  uint32_t begin = let.loc.offset;
  uint32_t end = body ? startOf(*body) : begin;
  if (end <= begin || end > text.size())
    return "let " + let.text;
  std::string_view s = rtrim(text.substr(begin, end - begin));
  if (!s.empty() && s.back() == '=')
    s = rtrim(s.substr(0, s.size() - 1));
  return capLines(s, 12);
}

// A parameter as written: from its name to the `)` that closes its group.
std::string paramText(std::string_view text, const Node &p) {
  if (p.kids.empty())
    return p.text;
  uint32_t i = p.loc.offset;
  int depth = 0;
  for (; i < text.size(); ++i) {
    char c = text[i];
    if (c == '(' || c == '[' || c == '{')
      ++depth;
    if (c == ')' || c == ']' || c == '}') {
      if (depth == 0)
        break;
      --depth;
    }
    if (c == '\n' && depth == 0)
      break;
  }
  return std::string(rtrim(text.substr(p.loc.offset, i - p.loc.offset)));
}

std::string fence(std::string_view code) {
  return "```pia\n" + std::string(code) + "\n```";
}

// ------------------------------------------------------------ resolution

class Resolver {
public:
  Resolver(std::string_view text, uint32_t target)
      : text_(text), target_(target) {}

  std::optional<Binding> run(const Node &program) {
    scopes_.emplace_back();
    for (const auto &item : program.kids)
      if (item && item->kind == N::LetItem)
        bindLet(*item);
    for (const auto &item : program.kids)
      if (item)
        walk(*item);
    return found_;
  }

  // Every name in the program with the binding it resolves to.
  static std::vector<std::pair<Range, Binding>> uses(std::string_view text,
                                                     const Node &program) {
    Resolver r(text, UINT32_MAX);
    std::vector<std::pair<Range, Binding>> out;
    r.uses_ = &out;
    r.run(program);
    return out;
  }

  // Binds every top-level name, then the parameters of the item around
  // `target`, into `out`.
  static void visible(std::string_view text, const Node &program,
                      uint32_t target, std::vector<Binding> &out) {
    Resolver r(text, target);
    const Node *around = nullptr;
    for (const auto &item : program.kids) {
      if (!item || item->kind != N::LetItem)
        continue;
      out.push_back(r.letBinding(*item));
      if (item->loc.offset <= target)
        around = item.get();
    }
    if (!around)
      return;
    if (const Node *ps = kid(*around, 0))
      for (const auto &p : ps->kids)
        if (p->kind == N::Param)
          out.push_back(r.paramBinding(*p));
  }

private:
  using Scope = std::vector<Binding>;

  Binding letBinding(const Node &let) {
    Binding b;
    b.name = let.text;
    const Node *body = kid(let, 3);
    if (hasParams(let))
      b.role = "function";
    else if (body && body->kind == N::TypeValue)
      b.role = "type";
    else
      b.role = let.kind == N::LetIn ? "local" : "value";
    uint32_t at = nameOffset(text_, let);
    b.nameRange = {at, at + static_cast<uint32_t>(let.text.size())};
    if (b.role == "type" && body) {
      // A type is its definition: show the whole thing.
      uint32_t begin = let.loc.offset;
      uint32_t end = static_cast<uint32_t>(text_.size());
      size_t next = text_.find("\nlet ", begin);
      if (next != std::string_view::npos)
        end = static_cast<uint32_t>(next);
      b.snippet = fence(capLines(rtrim(text_.substr(begin, end - begin)), 15));
    } else {
      b.snippet = fence(letHeader(text_, let));
    }
    // Its doc comment, or the literate prose before it (ADR 0029).
    std::string doc = syntax::docText(let);
    if (!doc.empty())
      b.snippet += "\n" + doc;
    return b;
  }

  Binding paramBinding(const Node &p) {
    Binding b;
    b.name = p.text;
    b.role = "parameter";
    b.nameRange = {p.loc.offset,
                   p.loc.offset + static_cast<uint32_t>(p.text.size())};
    b.snippet = fence("(parameter) " + paramText(text_, p));
    return b;
  }

  // `result`, the name a function's contracts use for its return value.
  // It has no name in the source, so its range is empty.
  Binding resultBinding(const Node &ret, const Node &contracts) {
    Binding r;
    r.name = "result";
    r.role = "result";
    r.nameRange = {ret.loc.offset, ret.loc.offset};
    uint32_t end = std::max(contracts.loc.offset, ret.loc.offset);
    r.snippet = fence(
        "(result) result " +
        std::string(rtrim(text_.substr(ret.loc.offset, end - ret.loc.offset))));
    return r;
  }

  Binding simple(const Node &n, std::string role) {
    Binding b;
    b.name = n.text;
    b.role = role;
    b.nameRange = {n.loc.offset,
                   n.loc.offset + static_cast<uint32_t>(n.text.size())};
    b.snippet = fence("(" + role + ") " + n.text);
    return b;
  }

  void bind(Binding b) {
    if (!found_ && b.nameRange.begin <= target_ && target_ < b.nameRange.end)
      found_ = b;
    scopes_.back().push_back(std::move(b));
  }

  void bindLet(const Node &let) { bind(letBinding(let)); }

  // The innermost binding of `name`, searching from the latest scope
  // outwards so that a local hides a top-level name.
  const Binding *innermost(const std::string &name) const {
    for (auto s = scopes_.rbegin(); s != scopes_.rend(); ++s)
      for (auto it = s->rbegin(); it != s->rend(); ++it)
        if (it->name == name)
          return &*it;
    return nullptr;
  }

  void lookup(const Node &name) {
    if (found_)
      return;
    uint32_t b = name.loc.offset;
    uint32_t e = b + static_cast<uint32_t>(name.text.size());
    // Collecting every use ignores the target.
    if (!uses_ && (target_ < b || target_ >= e))
      return;
    const Binding *binding = innermost(name.text);
    if (!binding)
      return;
    if (uses_)
      uses_->emplace_back(Range{b, e}, *binding);
    else
      found_ = *binding;
  }

  // Binds the variables of a pattern in the current scope.
  void bindPattern(const Node &p, const std::string &role) {
    if (p.kind == N::PVar) {
      bind(simple(p, role));
      return;
    }
    if (p.kind == N::PField && p.kids.empty()) {
      bind(simple(p, role));
      return;
    }
    if (p.kind == N::PAs)
      bind(simple(p, role));
    for (const auto &k : p.kids) {
      if (!k)
        continue;
      // In `(x : t)` only `x` binds; the type is an ordinary expression.
      if (p.kind == N::PTyped && k.get() != p.kids[0].get())
        walk(*k);
      else
        bindPattern(*k, role);
    }
  }

  void push() { scopes_.emplace_back(); }
  void pop() { scopes_.pop_back(); }

  void walkLet(const Node &let, bool topLevel) {
    bool rec = let.flags.find("rec") != std::string::npos;
    if (!topLevel && rec)
      bindLet(let);
    push(); // the parameters
    if (const Node *ps = kid(let, 0))
      for (const auto &p : ps->kids) {
        if (p->kind != N::Param)
          continue;
        for (const auto &k : p->kids)
          walk(*k); // the annotation
        bind(paramBinding(*p));
      }
    const Node *ret = kid(let, 1);
    if (ret && ret->kind == N::RetAnnot)
      walk(*ret);
    if (const Node *cs = kid(let, 2)) {
      // `result` is in scope in the contracts only.
      push();
      if (ret && ret->kind == N::RetAnnot)
        scopes_.back().push_back(resultBinding(*ret, *cs));
      walk(*cs);
      pop();
    }
    if (const Node *value = kid(let, 3))
      walk(*value);
    pop();
    if (!topLevel && !rec)
      bindLet(let);
    if (let.kind == N::LetIn)
      if (const Node *body = kid(let, 4))
        walk(*body);
  }

  void walk(const Node &n) {
    if (found_)
      return;
    switch (n.kind) {
    case N::LetItem:
      walkLet(n, /*topLevel=*/scopes_.size() == 1);
      return;
    case N::LetIn: {
      push();
      walkLet(n, false);
      pop();
      return;
    }
    case N::Name:
      lookup(n);
      return;
    case N::Lambda: {
      push();
      for (const auto &k : n.kids) {
        if (k->kind == N::LParam) {
          for (size_t i = 1; i < k->kids.size(); ++i)
            walk(*k->kids[i]);
          if (!k->kids.empty())
            bindPattern(*k->kids[0], "parameter");
        } else {
          walk(*k);
        }
      }
      pop();
      return;
    }
    case N::For:
    case N::Spread: {
      if (const Node *it = kid(n, 1))
        walk(*it);
      push();
      if (const Node *pat = kid(n, 0))
        bindPattern(*pat, "loop variable");
      for (size_t i = 2; i < n.kids.size(); ++i)
        walk(*n.kids[i]);
      pop();
      return;
    }
    case N::Quantifier: {
      push();
      for (const auto &k : n.kids) {
        if (k->kind == N::Binder || k->kind == N::RangeBinder) {
          for (const auto &t : k->kids)
            walk(*t);
          bind(simple(*k, "bound variable"));
        } else {
          walk(*k);
        }
      }
      pop();
      return;
    }
    case N::Arm: {
      push();
      if (const Node *pat = kid(n, 0))
        bindPattern(*pat, "pattern variable");
      for (size_t i = 1; i < n.kids.size(); ++i)
        walk(*n.kids[i]);
      pop();
      return;
    }
    case N::Module:
    case N::Interface: {
      push();
      for (const auto &k : n.kids)
        if (k->kind == N::LetItem)
          bindLet(*k);
      for (const auto &k : n.kids) {
        if (k->kind == N::LetItem)
          walkLet(*k, /*topLevel=*/true);
        else
          walk(*k);
      }
      pop();
      return;
    }
    default:
      for (const auto &k : n.kids)
        if (k)
          walk(*k);
    }
  }

  std::string_view text_;
  uint32_t target_;
  std::vector<Scope> scopes_;
  std::optional<Binding> found_;
  std::vector<std::pair<Range, Binding>> *uses_ = nullptr;
};

// ------------------------------------------------------------ symbols

Range itemRange(std::string_view text, const Node &n, uint32_t end) {
  uint32_t begin = n.loc.offset;
  if (end < begin)
    end = begin;
  std::string_view s = rtrim(text.substr(begin, end - begin));
  return {begin, begin + static_cast<uint32_t>(s.size())};
}

void collectSymbols(std::string_view text, const Node &parent, uint32_t end,
                    std::vector<Symbol> &out) {
  for (size_t i = 0; i < parent.kids.size(); ++i) {
    const Node &n = *parent.kids[i];
    uint32_t next = end;
    for (size_t j = i + 1; j < parent.kids.size(); ++j)
      if (parent.kids[j]->loc.line != 0) {
        next = parent.kids[j]->loc.offset;
        break;
      }
    Symbol s;
    s.name = n.text;
    s.range = itemRange(text, n, next);
    uint32_t at = nameOffset(text, n);
    s.selection = {at, at + static_cast<uint32_t>(n.text.size())};
    switch (n.kind) {
    case N::LetItem: {
      const Node *body = kid(n, 3);
      if (hasParams(n))
        s.kind = SymbolKind::Function;
      else if (body && body->kind == N::TypeValue)
        s.kind = SymbolKind::Class;
      else
        s.kind = SymbolKind::Constant;
      s.detail = firstLine(letHeader(text, n));
      if (s.detail.rfind("let ", 0) == 0)
        s.detail = s.detail.substr(4);
      break;
    }
    case N::Interface:
      s.kind = SymbolKind::Interface;
      collectSymbols(text, n, next, s.children);
      break;
    case N::Module:
      s.kind = SymbolKind::Module;
      collectSymbols(text, n, next, s.children);
      break;
    case N::SigVal:
      s.kind = SymbolKind::Method;
      s.detail =
          firstLine(text.substr(s.range.begin, s.range.end - s.range.begin));
      break;
    case N::SigType:
      s.kind = SymbolKind::Class;
      break;
    case N::MetaOperator:
      s.kind = SymbolKind::Operator;
      if (size_t at = text.find(n.text, n.loc.offset);
          at != std::string_view::npos)
        s.selection = {static_cast<uint32_t>(at),
                       static_cast<uint32_t>(at + n.text.size())};
      break;
    default:
      continue;
    }
    if (s.name.empty())
      continue;
    out.push_back(std::move(s));
  }
}

} // namespace

// ------------------------------------------------------------ Analysis

namespace {

// Offsets where a top-level item may start: lines whose first character
// begins a name, outside comments and strings (the column-1 layout rule of
// docs/grammar.md).
std::vector<uint32_t> itemStarts(std::string_view text) {
  std::vector<uint32_t> starts;
  int comment = 0;
  bool string = false;
  bool lineStart = true;
  for (uint32_t i = 0; i < text.size(); ++i) {
    char c = text[i];
    if (lineStart && comment == 0 && !string && identStart(c))
      starts.push_back(i);
    lineStart = c == '\n';
    if (comment == 0 && !string && c == '\\') {
      // A line comment: skip to its end (ADR 0029).
      while (i + 1 < text.size() && text[i + 1] != '\n')
        ++i;
      continue;
    }
    if (string) {
      if (c == '\\')
        ++i;
      else if (c == '"')
        string = false;
    } else if (c == '(' && i + 1 < text.size() && text[i + 1] == '*') {
      ++comment;
      ++i;
    } else if (comment > 0 && c == '*' && i + 1 < text.size() &&
               text[i + 1] == ')') {
      --comment;
      ++i;
    } else if (comment == 0 && c == '"') {
      string = true;
    }
  }
  return starts;
}

// When the whole file does not parse, parses each top-level item on its own
// so hover, definitions and the outline keep working while the user types.
// Text outside the item becomes spaces, which keeps every offset, line and
// column. Items that do not parse on their own are left out.
syntax::NodePtr parseItemByItem(std::string_view text) {
  auto program = syntax::makeNode(N::Program, syntax::SourceLoc{1, 1, 0});
  std::vector<uint32_t> starts = itemStarts(text);
  if (starts.size() > 2000)
    return program; // too costly; give up
  for (size_t i = 0; i < starts.size(); ++i) {
    uint32_t b = starts[i];
    uint32_t e = i + 1 < starts.size() ? starts[i + 1]
                                       : static_cast<uint32_t>(text.size());
    std::string masked(text);
    for (uint32_t j = 0; j < masked.size(); ++j)
      if ((j < b || j >= e) && masked[j] != '\n')
        masked[j] = ' ';
    syntax::Diagnostics diags;
    syntax::NodePtr part = syntax::parseProgram(masked, diags);
    if (diags.hasErrors() || !part)
      continue;
    for (auto &item : part->kids)
      program->add(std::move(item));
  }
  return program;
}

} // namespace

Analysis::Analysis(std::string text, bool literate)
    : text_(std::move(text)), index_(text_) {
  tree_ = syntax::parseProgram(text_, diags_, literate);
  if (diags_.hasErrors())
    tree_ = parseItemByItem(literate ? syntax::literateCode(text_) : text_);
  else
    lints_ = syntax::lint(*tree_, text_);
}

std::vector<Diag> Analysis::diagnostics() const {
  std::vector<Diag> out;
  for (const syntax::Diagnostic &d : diags_.errors()) {
    Diag diag;
    uint32_t at = d.loc.line == 0 ? 0 : d.loc.offset;
    diag.range = tokenFrom(text_, at);
    diag.source = "pia";
    diag.message = d.message;
    out.push_back(std::move(diag));
  }
  for (const syntax::Lint &l : lints_) {
    Diag diag;
    diag.range = {l.loc.offset, std::max(l.end, l.loc.offset + 1)};
    diag.severity = Severity::Warning;
    diag.source = "pia-lint";
    diag.code = l.name;
    diag.message = l.message;
    out.push_back(std::move(diag));
  }
  return out;
}

std::vector<Symbol> Analysis::symbols() const {
  std::vector<Symbol> out;
  if (tree_)
    collectSymbols(text_, *tree_, static_cast<uint32_t>(text_.size()), out);
  return out;
}

std::optional<Binding> Analysis::resolve(uint32_t offset) const {
  if (!tree_)
    return std::nullopt;
  Range tok = tokenAt(text_, offset);
  if (tok.begin == tok.end)
    return std::nullopt;
  return Resolver(text_, tok.begin).run(*tree_);
}

std::vector<Range> Analysis::references(uint32_t offset) const {
  std::vector<Range> out;
  std::optional<Binding> b = resolve(offset);
  if (!b || b->nameRange.end == b->nameRange.begin)
    return out;
  out.push_back(b->nameRange);
  for (const auto &[use, binding] : Resolver::uses(text_, *tree_))
    if (binding.nameRange.begin == b->nameRange.begin &&
        binding.name == b->name)
      out.push_back(use);
  std::sort(out.begin(), out.end(),
            [](Range x, Range y) { return x.begin < y.begin; });
  out.erase(std::unique(out.begin(), out.end(),
                        [](Range x, Range y) { return x.begin == y.begin; }),
            out.end());
  return out;
}

std::vector<Binding> Analysis::completions(uint32_t offset) const {
  std::vector<Binding> out;
  if (tree_)
    Resolver::visible(text_, *tree_, offset, out);
  return out;
}

} // namespace pia::lsp
