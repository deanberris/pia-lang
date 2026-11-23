#include "irgen/Target.h"

#include <functional>
#include <vector>

#include "meta/Expand.h"
#include "syntax/Parser.h"

namespace pia::irgen {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

std::string_view targetTheorySource() {
  static const char kSource[] =
#include "irgen/TargetSource.inc"
      ;
  return {kSource, sizeof(kSource) - 1};
}

std::string targetModelFor(std::string_view triple) {
  if (triple.empty()) {
#if defined(__x86_64__) && defined(__linux__)
    triple = "x86_64-unknown-linux-gnu";
#else
    triple = "arm64-apple-macosx";
#endif
  }
  auto has = [&](std::string_view part) {
    return triple.find(part) != std::string_view::npos;
  };
  bool arm64 = triple.rfind("arm64", 0) == 0 || triple.rfind("aarch64", 0) == 0;
  if (arm64 && (has("apple") || has("darwin") || has("macos")))
    return "arm64_macos";
  if (triple.rfind("x86_64", 0) == 0 && has("linux") && !has("gnux32"))
    return "x86_64_linux";
  return "";
}

bool usesTargetTheory(const Node &program) {
  for (const NodePtr &item : program.kids)
    if (item->text == "Target" && item->kind != NodeKind::Import)
      return false;
  std::function<bool(const Node &)> uses = [&](const Node &n) {
    if (n.kind == NodeKind::Field && n.kids.size() == 1 &&
        n.kids[0]->kind == NodeKind::Name && n.kids[0]->flags.empty() &&
        n.kids[0]->text == "Target")
      return true;
    if (n.kind == NodeKind::TypeName && n.text.rfind("Target.", 0) == 0)
      return true;
    for (const NodePtr &k : n.kids)
      if (uses(*k))
        return true;
    return false;
  };
  return uses(program);
}

bool addTargetTheory(Node &program, std::string_view triple,
                     syntax::Diagnostics &diags) {
  std::string model = targetModelFor(triple);
  if (model.empty()) {
    diags.error(program.loc,
                "the program uses 'Target', and Pia has no model of it for "
                "the target '" +
                    std::string(triple) +
                    "'; it has models for arm64-apple-macosx and "
                    "x86_64-unknown-linux-gnu (ADR 0049)");
    return false;
  }
  // The theory is parsed and expanded on its own, so its operators are the
  // prelude's whatever the program declares.
  syntax::Diagnostics own;
  NodePtr theory = syntax::parseProgram(targetTheorySource(), own);
  if (!own.hasErrors())
    meta::expand(*theory, own);
  if (own.hasErrors()) {
    for (const syntax::Diagnostic &d : own.errors())
      diags.error(program.loc, "internal error in the built-in theory "
                               "'Target', at line " +
                                   std::to_string(d.loc.line) + ": " +
                                   d.message);
    return false;
  }
  std::vector<NodePtr> items;
  for (NodePtr &item : theory->kids) {
    bool keep = item->kind == NodeKind::Theory ||
                (item->kind == NodeKind::Model && item->text == model);
    if (!keep)
      continue;
    item->flags = "builtin";
    items.push_back(std::move(item));
  }
  for (NodePtr &item : program.kids)
    items.push_back(std::move(item));
  program.kids = std::move(items);
  return true;
}

} // namespace pia::irgen
