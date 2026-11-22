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

NodePtr clone(const Node &node) {
  auto n = std::make_unique<Node>();
  n->kind = node.kind;
  n->text = node.text;
  n->flags = node.flags;
  n->loc = node.loc;
  for (const NodePtr &kid : node.kids) n->kids.push_back(clone(*kid));
  for (const NodePtr &c : node.comments) n->comments.push_back(clone(*c));
  return n;
}

bool isConceptItem(const Node &item) {
  if (item.kind != NodeKind::LetItem || item.kids.size() < 4 ||
      item.flags.find("meta") == std::string::npos)
    return false;
  const Node &ret = *item.kids[1];
  return ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
         ret.kids[0]->kind == NodeKind::Annot &&
         ret.kids[0]->kids[1]->kind == NodeKind::TypeName &&
         ret.kids[0]->kids[1]->text == "concept";
}

bool isTypeLevelMetaItem(const Node &item) {
  if (item.kind != NodeKind::LetItem || item.kids.size() < 4 ||
      item.flags.find("meta") == std::string::npos || isConceptItem(item))
    return false;
  const Node &params = *item.kids[0];
  if (params.kids.empty()) return false;
  for (const NodePtr &p : params.kids)
    if (p->kind != NodeKind::Param || p->kids.empty() ||
        p->kids[0]->kind != NodeKind::Annot ||
        p->kids[0]->kids[1]->kind != NodeKind::TypeKind)
      return false;
  const Node &ret = *item.kids[1];
  if (ret.kind != NodeKind::RetAnnot || ret.kids.empty() ||
      ret.kids[0]->kind != NodeKind::Annot)
    return false;
  const Node &t = *ret.kids[0]->kids[1];
  return t.kind == NodeKind::TypeKind ||
         (t.kind == NodeKind::TypeName && t.text == "bool");
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

void dumpAt(std::ostream &os, const Node &n, int indent, bool comments) {
  for (int i = 0; i < indent; ++i) os << "  ";
  os << '(' << nodeKindName(n.kind);
  if (!n.text.empty()) {
    os << ' ';
    writeQuoted(os, n.text);
  }
  if (!n.flags.empty()) os << " [" << n.flags << ']';
  if (n.kids.empty() && (!comments || n.comments.empty())) {
    os << ")\n";
    return;
  }
  os << '\n';
  if (comments)
    for (const NodePtr &c : n.comments) dumpAt(os, *c, indent + 1, comments);
  for (const NodePtr &k : n.kids) dumpAt(os, *k, indent + 1, comments);
  for (int i = 0; i < indent; ++i) os << "  ";
  os << ")\n";
}

}  // namespace

void dump(std::ostream &os, const Node &node, bool comments) {
  dumpAt(os, node, 0, comments);
}

}  // namespace pia::syntax
