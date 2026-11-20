#include "syntax/Syntax.h"

namespace pia::syntax {

const char *nodeKindName(NodeKind kind) {
  switch (kind) {
#define PIA_NODE_NAME(name) \
  case NodeKind::name:      \
    return #name;
    PIA_NODE_KINDS(PIA_NODE_NAME)
#undef PIA_NODE_NAME
  }
  return "?";
}

NodePtr makeNode(NodeKind kind, SourceLoc loc, std::string text) {
  auto n = std::make_unique<Node>();
  n->kind = kind;
  n->loc = loc;
  n->text = std::move(text);
  return n;
}

namespace {

void writeQuoted(std::ostream &os, const std::string &s) {
  os << '"';
  for (char c : s) {
    if (c == '"' || c == '\\') os << '\\';
    if (c == '\n') {
      os << "\\n";
      continue;
    }
    os << c;
  }
  os << '"';
}

void dumpAt(std::ostream &os, const Node &n, int indent) {
  for (int i = 0; i < indent; ++i) os << "  ";
  os << '(' << nodeKindName(n.kind);
  if (!n.text.empty()) {
    os << ' ';
    writeQuoted(os, n.text);
  }
  if (!n.flags.empty()) os << " [" << n.flags << ']';
  if (n.kids.empty()) {
    os << ")\n";
    return;
  }
  os << '\n';
  for (const NodePtr &k : n.kids) dumpAt(os, *k, indent + 1);
  for (int i = 0; i < indent; ++i) os << "  ";
  os << ")\n";
}

}  // namespace

void dump(std::ostream &os, const Node &node) { dumpAt(os, node, 0); }

}  // namespace pia::syntax
