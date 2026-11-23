#include "irgen/Memory.h"

#include <functional>
#include <vector>

#include "meta/Expand.h"
#include "syntax/Parser.h"

namespace pia::irgen {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

std::string_view memoryTheorySource() {
  static const char kSource[] =
#include "irgen/MemorySource.inc"
      ;
  return {kSource, sizeof(kSource) - 1};
}

bool usesMemoryTheory(const Node &program) {
  for (const NodePtr &item : program.kids)
    if (item->text == "Memory" && item->kind != NodeKind::Import)
      return false;
  std::function<bool(const Node &)> uses = [&](const Node &n) {
    if (n.kind == NodeKind::Field && n.kids.size() == 1 &&
        n.kids[0]->kind == NodeKind::Name && n.kids[0]->flags.empty() &&
        n.kids[0]->text == "Memory")
      return true;
    if (n.kind == NodeKind::TypeName && n.text.rfind("Memory.", 0) == 0)
      return true;
    for (const NodePtr &k : n.kids)
      if (uses(*k))
        return true;
    return false;
  };
  return uses(program);
}

bool addMemoryTheory(Node &program, syntax::Diagnostics &diags) {
  // Parsed and expanded on its own, as Target is, so its operators are the
  // prelude's whatever the program declares.
  syntax::Diagnostics own;
  NodePtr theory = syntax::parseProgram(memoryTheorySource(), own);
  if (!own.hasErrors())
    meta::expand(*theory, own);
  if (own.hasErrors()) {
    for (const syntax::Diagnostic &d : own.errors())
      diags.error(program.loc, "internal error in the built-in theory "
                               "'Memory', at line " +
                                   std::to_string(d.loc.line) + ": " +
                                   d.message);
    return false;
  }
  std::vector<NodePtr> items;
  for (NodePtr &item : theory->kids) {
    if (item->kind == NodeKind::Theory || item->kind == NodeKind::Model)
      item->flags = "builtin";
    items.push_back(std::move(item));
  }
  for (NodePtr &item : program.kids)
    items.push_back(std::move(item));
  program.kids = std::move(items);
  return true;
}

} // namespace pia::irgen
