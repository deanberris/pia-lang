#include "syntax/Comments.h"

#include <algorithm>
#include <limits>

namespace pia::syntax {
namespace {

using K = TokenKind;

bool opens(K k) {
  switch (k) {
  case K::LParen:
  case K::LBracket:
  case K::LBrace:
  case K::LBraceAdj:
  case K::QuoteOpen:
  case K::SpliceOpen:
  case K::AttrOpen:
  case K::DotLBracket:
  case K::TargsOpen:
  case K::Sig:
  case K::Struct:
  case K::Do:
    return true;
  default:
    return false;
  }
}

bool closes(K k) {
  switch (k) {
  case K::RParen:
  case K::RBracket:
  case K::RBrace:
  case K::TargsClose:
  case K::End:
  case K::Done:
    return true;
  default:
    return false;
  }
}

// Nodes a comment never attaches to: the program, and the nodes that only
// group others, where a reader means the first thing in the group.
bool isTarget(NodeKind k) {
  switch (k) {
  case NodeKind::None:
  case NodeKind::Program:
  case NodeKind::Sequence:
  case NodeKind::Params:
  case NodeKind::Contracts:
  case NodeKind::Attrs:
  case NodeKind::LoopAnnots:
  case NodeKind::Modifiers:
  case NodeKind::Paths:
  case NodeKind::Variants:
  case NodeKind::Comment:
    return false;
  default:
    return true;
  }
}

// A comment after one of these, at the end of a line, is about what comes
// next: `= \ the default`, `` `( (** doc *) ``, `do \ each tile`.
bool leadsIn(K k) {
  switch (k) {
  case K::Eq:
  case K::Arrow:
  case K::FatArrow:
  case K::LArrow:
  case K::Then:
  case K::Else:
  case K::With:
  case K::Bar:
    return true;
  default:
    return opens(k);
  }
}

constexpr size_t kNone = std::numeric_limits<size_t>::max();

class Attacher {
public:
  Attacher(Node &root, const std::vector<Token> &tokens, std::string_view src)
      : root_(root), src_(src) {
    for (const Token &t : tokens)
      if (t.kind != K::Sep && t.kind != K::Eof)
        toks_.push_back(&t);
    match_.assign(toks_.size(), kNone);
    std::vector<size_t> stack;
    for (size_t r = 0; r < toks_.size(); ++r) {
      if (opens(toks_[r]->kind)) {
        stack.push_back(r);
      } else if (closes(toks_[r]->kind) && !stack.empty()) {
        match_[stack.back()] = r;
        stack.pop_back();
      }
    }
    walk(root_, 0);
  }

  void attach(const RawComment &c) {
    size_t next = firstAtOrAfter(c.end);
    size_t prev = firstAtOrAfter(c.loc.offset);
    prev = prev == 0 ? kNone : prev - 1;
    bool hasNext = next < toks_.size();
    Node *target = nullptr;
    const char *place = "leading";

    bool trailing = prev != kNone && !c.ownLine &&
                    !leadsIn(toks_[prev]->kind) &&
                    c.style != RawComment::Style::Prose &&
                    (!hasNext || toks_[next]->loc.line > c.endLine);
    if (trailing) {
      place = "trailing";
      target = endingAt(prev);
    } else if (hasNext) {
      target = startingAt(next);
      // Markdown puts a blank line before a fence, so prose always leads the
      // code block after it.
      if (target && c.style != RawComment::Style::Prose &&
          blankLineBetween(c.end, toks_[next]->loc.offset))
        place = "detached";
    }
    if (!target && hasNext && prev != kNone) {
      // The innermost node around the comment.
      const Extent *best = nullptr;
      for (const Extent &e : extents_)
        if (e.start <= prev && e.end >= next &&
            (!best || e.depth > best->depth))
          best = &e;
      if (best)
        target = best->node;
      if (!c.ownLine)
        place = "trailing";
    }
    if (!target) {
      target = &root_;
      place = "detached";
    }
    target->comments.push_back(
        makeComment(c.loc, c.text, commentStyleName(c.style), place));
  }

private:
  struct Extent {
    Node *node;
    int depth;
    size_t start, end; // indexes into toks_
  };

  // The node a trailing comment after token `prev` describes: the
  // outermost node that ends there and starts on the same line, so
  // `let x = f y (* why *)` describes the `let` and not `y`; failing that,
  // the innermost node that ends there. Separators before the comment are
  // looked past.
  Node *endingAt(size_t prev) const {
    size_t p = prev;
    while (p > 0 && (toks_[p]->kind == K::Semi || toks_[p]->kind == K::Comma ||
                     toks_[p]->kind == K::In))
      --p;
    const Extent *best = nullptr;
    uint32_t line = toks_[p]->loc.line;
    for (const Extent &e : extents_)
      if (e.end == p && toks_[e.start]->loc.line == line &&
          (!best || e.depth < best->depth))
        best = &e;
    if (best)
      return best->node;
    for (const Extent &e : extents_)
      if (e.end == p && (!best || e.depth > best->depth))
        best = &e;
    return best ? best->node : nullptr;
  }

  // The node a leading comment before token `next` describes: the
  // outermost node that starts there, looking past opening brackets that no
  // node starts at.
  Node *startingAt(size_t next) const {
    for (size_t q = next; q < toks_.size(); ++q) {
      const Extent *best = nullptr;
      for (const Extent &e : extents_)
        if (e.start == q && (!best || e.depth < best->depth))
          best = &e;
      if (best)
        return best->node;
      if (toks_[q]->kind != K::LParen && toks_[q]->kind != K::LBracket)
        return nullptr;
    }
    return nullptr;
  }

  size_t firstAtOrAfter(uint32_t offset) const {
    auto it = std::lower_bound(
        toks_.begin(), toks_.end(), offset,
        [](const Token *t, uint32_t o) { return t->loc.offset < o; });
    return static_cast<size_t>(it - toks_.begin());
  }

  bool blankLineBetween(uint32_t from, uint32_t to) const {
    bool sawNewline = false;
    for (uint32_t i = from; i < to && i < src_.size(); ++i) {
      char ch = src_[i];
      if (ch == '\n') {
        if (sawNewline)
          return true;
        sawNewline = true;
      } else if (ch != ' ' && ch != '\t' && ch != '\r') {
        sawNewline = false;
      }
    }
    return false;
  }

  // The tokens a node spans: from its first token to its last, including
  // the closing brackets of anything it opens. Returns false for a node
  // with no position.
  bool walk(Node &n, int depth, size_t *startOut = nullptr,
            size_t *endOut = nullptr) {
    size_t start = kNone, end = 0;
    if (n.kind != NodeKind::None && n.kind != NodeKind::Program &&
        n.loc.line != 0 && !toks_.empty()) {
      size_t own = std::min(firstAtOrAfter(n.loc.offset), toks_.size() - 1);
      start = end = own;
    }
    for (NodePtr &k : n.kids) {
      size_t s, e;
      if (walk(*k, depth + 1, &s, &e)) {
        start = std::min(start, s);
        end = std::max(end, e);
      }
    }
    if (start == kNone)
      return false;
    for (size_t r = start; r <= end; ++r)
      if (match_[r] != kNone && match_[r] > end)
        end = match_[r];
    if (isTarget(n.kind))
      extents_.push_back({&n, depth, start, end});
    if (startOut)
      *startOut = start;
    if (endOut)
      *endOut = end;
    return true;
  }

  Node &root_;
  std::string_view src_;
  std::vector<const Token *> toks_;
  std::vector<size_t> match_;
  std::vector<Extent> extents_;
};

} // namespace

void attachComments(Node &root, const std::vector<Token> &tokens,
                    const std::vector<RawComment> &comments,
                    std::string_view source) {
  if (comments.empty())
    return;
  Attacher a(root, tokens, source);
  for (const RawComment &c : comments)
    a.attach(c);
}

NodePtr makeComment(SourceLoc loc, std::string text, std::string_view style,
                    std::string_view place) {
  auto n = makeNode(NodeKind::Comment, loc, std::move(text));
  n->flags = std::string(style) + " " + std::string(place);
  return n;
}

std::string commentStyle(const Node &comment) {
  return comment.flags.substr(0, comment.flags.find(' '));
}

std::string commentPlace(const Node &comment) {
  size_t sp = comment.flags.find(' ');
  return sp == std::string::npos ? "" : comment.flags.substr(sp + 1);
}

std::string docText(const Node &node) {
  std::string out;
  for (const NodePtr &c : node.comments) {
    std::string style = commentStyle(*c);
    if ((style != "doc" && style != "prose") || commentPlace(*c) != "leading")
      continue;
    if (!out.empty())
      out += "\n\n";
    out += c->text;
  }
  return out;
}

} // namespace pia::syntax
