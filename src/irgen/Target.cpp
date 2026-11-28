#include "irgen/Target.h"

#include <functional>
#include <map>
#include <set>
#include <vector>

#include "meta/Expand.h"
#include "sema/Sema.h"
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

// The model `n` tests for, if it is `Target.is m`, or "".
std::string targetIs(const Node &n) {
  if (n.kind != NodeKind::Apply || n.kids.size() != 2)
    return "";
  const Node &f = *n.kids[0], &m = *n.kids[1];
  if (f.kind != NodeKind::Field || f.text != "is" || f.kids.size() != 1 ||
      f.kids[0]->kind != NodeKind::Name || f.kids[0]->text != "Target" ||
      !f.kids[0]->flags.empty() || m.kind != NodeKind::Name)
    return "";
  return m.text;
}

// The first use in `n` of an `@target` function in `only` (function ->
// model) for a model other than `here`, the one `n` is compiled for ("" in
// target-generic code), or null. `if Target.is m then a else b` is folded
// at compile time, so `a` is code for m.
const Node *foreignUse(const Node &n,
                       const std::map<std::string, std::string> &only,
                       const std::string &here) {
  if (n.kind == NodeKind::Name && (n.flags.empty() || n.flags == "toplevel"))
    if (auto f = only.find(n.text); f != only.end() && f->second != here)
      return &n;
  if (n.kind == NodeKind::If && n.kids.size() >= 2)
    if (std::string m = targetIs(*n.kids[0]); !m.empty()) {
      if (const Node *u = foreignUse(*n.kids[1], only, m))
        return u;
      for (size_t i = 2; i < n.kids.size(); ++i)
        if (const Node *u = foreignUse(*n.kids[i], only, here))
          return u;
      return nullptr;
    }
  for (const NodePtr &k : n.kids)
    if (const Node *u = foreignUse(*k, only, here))
      return u;
  return nullptr;
}

// Folds each `Target.is m` to whether `m` is `model`, and each `if` on one
// to its branch for `model`, so the other target's code is never compiled.
void foldTargetIs(NodePtr &n, const std::string &model,
                  const std::set<std::string> &models,
                  syntax::Diagnostics &diags) {
  if (std::string m = targetIs(*n); !m.empty()) {
    if (!models.count(m))
      diags.error(n->kids[1]->loc, "'" + m + "' is not the model of a target");
    n = syntax::makeNode(NodeKind::BoolLit, n->loc,
                         m == model ? "true" : "false");
    return;
  }
  if (n->kind == NodeKind::If && n->kids.size() >= 2)
    if (std::string m = targetIs(*n->kids[0]); !m.empty()) {
      if (!models.count(m))
        diags.error(n->kids[0]->kids[1]->loc,
                    "'" + m + "' is not the model of a target");
      NodePtr branch;
      if (m == model)
        branch = std::move(n->kids[1]);
      else if (n->kids.size() > 2 && n->kids[2]->kind != NodeKind::None)
        branch = std::move(n->kids[2]);
      else
        branch = syntax::makeNode(NodeKind::Unit, n->loc);
      n = std::move(branch);
      foldTargetIs(n, model, models, diags);
      return;
    }
  for (NodePtr &k : n->kids)
    foldTargetIs(k, model, models, diags);
}

} // namespace

std::optional<int64_t> targetModelValue(std::string_view triple,
                                        const std::string &name) {
  std::string model = targetModelFor(triple);
  if (model.empty())
    return std::nullopt;
  // The models' values are literals, read once from the theory's source.
  static const std::map<std::string, std::map<std::string, int64_t>> values =
      [] {
        std::map<std::string, std::map<std::string, int64_t>> out;
        syntax::Diagnostics own;
        NodePtr theory = syntax::parseProgram(targetTheorySource(), own);
        if (own.hasErrors())
          return out;
        for (const NodePtr &item : theory->kids)
          if (item->kind == NodeKind::Model)
            for (const NodePtr &m : item->kids)
              if (m->kids.size() > 3 && m->kids[3]->kind == NodeKind::IntLit)
                if (auto lit = sema::parseIntLiteral(m->kids[3]->text))
                  out[item->text][m->text] = lit->value.getSExtValue();
        return out;
      }();
  auto m = values.find(model);
  if (m == values.end())
    return std::nullopt;
  auto v = m->second.find(name);
  if (v == m->second.end())
    return std::nullopt;
  return v->second;
}

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
  // `usize` is as wide as the model's pointers. Pia's `usize` is 64 bits
  // today, so a model with other pointers needs that to change first.
  for (const NodePtr &item : theory->kids)
    if (item->kind == NodeKind::Model && item->text == model)
      for (const NodePtr &m : item->kids)
        if (m->text == "ptr_bits" && m->kids.size() > 3 &&
            !(m->kids[3]->kind == NodeKind::IntLit &&
              m->kids[3]->text == "64")) {
          diags.error(program.loc,
                      "the model '" + model +
                          "' has pointers that are not 64 bits, and Pia's "
                          "usize is 64 bits (ADR 0049)");
          return false;
        }

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
    std::string here = self == only.end() ? "" : self->second;
    if (const Node *use = foreignUse(*item, only, here)) {
      const std::string &m = only.at(use->text);
      diags.error(use->loc, "'" + use->text +
                                "' is compiled only for the target '" + m +
                                "', so only a function marked '@target(" + m +
                                ")', or the 'then' of 'if Target.is " + m +
                                "', may use it");
    }
  }
  for (NodePtr &item : program.kids)
    foldTargetIs(item, model, models, diags);
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
