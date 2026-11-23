#include "irgen/Target.h"

#include <functional>
#include <map>
#include <set>
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

namespace {

// The `@target(...)` attribute of a function, or null.
Node *targetAttr(Node &item) {
  if (item.kind != NodeKind::LetItem || item.kids.size() < 2)
    return nullptr;
  Node &ret = *item.kids[1];
  if (ret.kind != NodeKind::RetAnnot || ret.kids.size() < 2)
    return nullptr;
  for (NodePtr &a : ret.kids[1]->kids)
    if (a->kind == NodeKind::Attribute && a->text == "target")
      return a.get();
  return nullptr;
}

void removeTargetAttr(Node &item) {
  auto &attrs = item.kids[1]->kids[1]->kids;
  for (auto it = attrs.begin(); it != attrs.end(); ++it)
    if ((*it)->kind == NodeKind::Attribute && (*it)->text == "target") {
      attrs.erase(it);
      return;
    }
}

// The first use in `n` of a top-level name in `names`, or null.
const Node *firstUse(const Node &n,
                     const std::map<std::string, std::string> &names) {
  if (n.kind == NodeKind::Name && (n.flags.empty() || n.flags == "toplevel") &&
      names.count(n.text))
    return &n;
  for (const NodePtr &k : n.kids)
    if (const Node *u = firstUse(*k, names))
      return u;
  return nullptr;
}

} // namespace

bool usesTargetTheory(const Node &program) {
  for (const NodePtr &item : program.kids)
    if (item->text == "Target" && item->kind != NodeKind::Import)
      return false;
  for (const NodePtr &item : program.kids)
    if (targetAttr(*item))
      return true;
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
                     syntax::Diagnostics &diags,
                     std::map<std::string, std::string> *targetOf) {
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
  std::set<std::string> models;
  for (const NodePtr &item : theory->kids)
    if (item->kind == NodeKind::Model)
      models.insert(item->text);

  // Each `@target(m)` function, and the model it is for.
  std::map<std::string, std::string> only;
  for (NodePtr &item : program.kids) {
    Node *attr = targetAttr(*item);
    if (!attr)
      continue;
    std::string m;
    if (attr->kids.size() == 1 && attr->kids[0]->kind == NodeKind::Name)
      m = attr->kids[0]->text;
    if (!models.count(m)) {
      std::string known;
      for (const std::string &k : models)
        known += (known.empty() ? "'" : ", '") + k + "'";
      diags.error(attr->loc,
                  "'@target' names the model of one target: " + known);
      continue;
    }
    only[item->text] = m;
  }
  // Only a function for the same target may use one, on every target, so
  // a program that compiles for one target compiles for the others.
  for (const NodePtr &item : program.kids) {
    auto self = only.find(item->text);
    std::map<std::string, std::string> others;
    for (const auto &[f, m] : only)
      if (f != item->text && (self == only.end() || self->second != m))
        others[f] = m;
    if (const Node *use = firstUse(*item, others))
      diags.error(use->loc, "'" + use->text +
                                "' is compiled only for the target '" +
                                others.at(use->text) +
                                "', so only a function marked '@target(" +
                                others.at(use->text) + ")' may use it");
  }
  if (diags.hasErrors())
    return false;

  std::vector<NodePtr> items;
  for (NodePtr &item : theory->kids) {
    bool keep = item->kind == NodeKind::Theory ||
                (item->kind == NodeKind::Model && item->text == model);
    if (!keep)
      continue;
    item->flags = "builtin";
    items.push_back(std::move(item));
  }
  for (NodePtr &item : program.kids) {
    if (auto t = only.find(item->text); t != only.end()) {
      // Compiled, and proved, only for its own target.
      if (t->second != model)
        continue;
      removeTargetAttr(*item);
      if (targetOf)
        (*targetOf)[item->text] = model;
    }
    items.push_back(std::move(item));
  }
  program.kids = std::move(items);
  return true;
}

} // namespace pia::irgen
