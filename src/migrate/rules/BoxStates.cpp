// ADR 0046, a theory of a box's state (Dean, 2026-11-28): every contract
// states the state of each box over a concept in its signature, and a
// call through a box requires it full. Before, a `box C` was full by its
// type, so a signature said nothing of it, and piac now rejects one that
// does not. The rule adds what every such program assumed: `requires full
// b` for a box it takes, and `ensures full b` (or `ensures full result`)
// for a box it hands back. That keeps the old meaning, so the edit is
// safe to apply. A definition that inherits its interface's contract
// (ADR 0077) is not edited, since a contract of its own would end the
// inheritance; the interface's declaration is reported instead, to edit by
// hand.

#include <set>
#include <string>
#include <tuple>
#include <vector>

#include "migrate/rules/Rules.h"

namespace pia::migrate {

namespace {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

bool hasWord(const std::string &mods, const std::string &word) {
  size_t at = 0;
  while ((at = mods.find(word, at)) != std::string::npos) {
    bool start = at == 0 || mods[at - 1] == ' ';
    bool end = at + word.size() == mods.size() || mods[at + word.size()] == ' ';
    if (start && end)
      return true;
    at += word.size();
  }
  return false;
}

// The generic types whose first parameter is `@unsized`, which a concept
// may fill; the library's is `box`.
std::set<std::string> boxTypes(const Node &program) {
  std::set<std::string> out = {"box"};
  for (const NodePtr &item : program.kids)
    if (item->kind == NodeKind::LetItem && item->kids.size() > 3 &&
        item->kids[3]->kind == NodeKind::Lambda &&
        !item->kids[3]->kids.empty() &&
        item->kids[3]->kids[0]->kind == NodeKind::LParam &&
        item->kids[3]->kids[0]->flags == "unsized")
      out.insert(item->text);
  return out;
}

struct Scope {
  std::set<std::string> boxes, concepts, types;
};

// Whether `t` is `box C` for a concept `C`: one defined here, or an
// imported name that is not a type defined here and is capitalised, as
// concepts are.
bool isConceptBox(const Node *t, const Scope &s) {
  if (!t || t->kind != NodeKind::TypeApp || t->kids.size() < 2 ||
      t->kids[0]->kind != NodeKind::TypeName ||
      !s.boxes.count(t->kids[0]->text) ||
      t->kids[1]->kind != NodeKind::TypeName)
    return false;
  const std::string &c = t->kids[1]->text;
  if (s.concepts.count(c))
    return true;
  std::string last =
      c.substr(c.rfind('.') == std::string::npos ? 0 : c.rfind('.') + 1);
  return !s.types.count(c) && !last.empty() && last[0] >= 'A' && last[0] <= 'Z';
}

// Whether a slice or array of `t`s holds boxes over a concept.
bool isConceptBoxes(const Node *t, const Scope &s) {
  return t &&
         (t->kind == NodeKind::SliceType || t->kind == NodeKind::ArrayType) &&
         !t->kids.empty() && isConceptBox(t->kids[0].get(), s);
}

// Whether `n` applies `full` or `unknown` to the box `name` or to an
// element of it, `name.[i]`.
bool statesState(const Node &n, const std::string &name) {
  if (n.kind == NodeKind::Apply && n.kids.size() == 2 &&
      n.kids[0]->kind == NodeKind::Name &&
      (n.kids[0]->text == "full" || n.kids[0]->text == "unknown")) {
    const Node *a = n.kids[1].get();
    if (a->kind == NodeKind::Index && !a->kids.empty())
      a = a->kids[0].get();
    if (a->kind == NodeKind::Name && a->text == name)
      return true;
  }
  for (const NodePtr &k : n.kids)
    if (statesState(*k, name))
      return true;
  return false;
}

bool stated(const Node *contracts, NodeKind kind, const std::string &name) {
  if (!contracts)
    return false;
  for (const NodePtr &c : contracts->kids)
    if (c->kind == kind && statesState(*c, name))
      return true;
  return false;
}

bool mentions(const Node &n, const std::string &name) {
  if (n.text == name)
    return true;
  for (const NodePtr &k : n.kids)
    if (mentions(*k, name))
      return true;
  return false;
}

// The clauses a signature lacks: `requires full b` for each box taken,
// `ensures full b` for each handed back, and `ensures full result`; for a
// slice of boxes, the same of each element, under a `forall` whose name is
// new in `item`, since Pia has no shadowing.
std::vector<std::string>
missing(const std::vector<std::tuple<std::string, std::string, const Node *>>
            &params,
        const Node *result, const Node *contracts, const Scope &s,
        const Node &item) {
  std::vector<std::string> pre, post;
  for (const auto &[name, mods, type] : params) {
    if (isConceptBoxes(type, s)) {
      std::string i = "i";
      for (int n = 1; mentions(item, i); ++n)
        i = "i" + std::to_string(n);
      std::string each = "forall (" + i + " in 0 .. len " + name + "). full " +
                         name + ".[" + i + "]";
      bool out = hasWord(mods, "out");
      if (!out && !stated(contracts, NodeKind::Requires, name))
        pre.push_back("requires " + each);
      if ((out || hasWord(mods, "inout") || hasWord(mods, "mutable")) &&
          !stated(contracts, NodeKind::Ensures, name))
        post.push_back("ensures " + each);
      continue;
    }
    if (!isConceptBox(type, s))
      continue;
    bool out = hasWord(mods, "out");
    if (!out && !stated(contracts, NodeKind::Requires, name))
      pre.push_back("requires full " + name);
    if ((out || hasWord(mods, "inout")) &&
        !stated(contracts, NodeKind::Ensures, name))
      post.push_back("ensures full " + name);
  }
  if (isConceptBox(result, s) &&
      !stated(contracts, NodeKind::Ensures, "result"))
    post.push_back("ensures full result");
  pre.insert(pre.end(), post.begin(), post.end());
  return pre;
}

void find(const Rule &rule, const syntax::Node &program,
          std::string_view source, std::vector<syntax::Lint> &out) {
  Scope s;
  s.boxes = boxTypes(program);
  for (const NodePtr &item : program.kids) {
    if (syntax::isConceptItem(*item))
      s.concepts.insert(item->text);
    else if (item->kind == NodeKind::LetItem)
      s.types.insert(item->text);
  }
  auto message = [&](const std::string &fn,
                     const std::vector<std::string> &clauses) {
    std::string list;
    for (size_t i = 0; i < clauses.size(); ++i)
      list += (i ? ", '" : "'") + clauses[i] + "'";
    return "'" + fn + "' states no state for a box over a concept, which " +
           rule.adr + " requires of every contract; before, a box was full " +
           "by its type. Add " + list;
  };
  std::set<std::string> declared;
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Interface)
      continue;
    for (const NodePtr &k : item->kids) {
      if (k->kind != NodeKind::SigVal || k->kids.size() < 3 ||
          k->kids[0]->kids.size() < 2)
        continue;
      declared.insert(k->text);
      std::vector<std::tuple<std::string, std::string, const Node *>> params;
      const Node *cur = k->kids[0]->kids[1].get();
      for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
        const Node &d = *cur->kids[0];
        if (d.kind == NodeKind::Domain && d.kids.size() > 1)
          params.emplace_back(d.text, d.kids[0]->text, d.kids[1].get());
      }
      std::vector<std::string> clauses =
          missing(params, cur, k->kids[2].get(), s, *k);
      if (clauses.empty())
        continue;
      syntax::Lint l;
      l.name = rule.id;
      l.loc = k->loc;
      l.end = k->loc.offset;
      l.message = message(k->text, clauses);
      out.push_back(std::move(l));
    }
  }
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::LetItem || item->kids.size() < 4 ||
        item->kids[0]->kind != NodeKind::Params)
      continue;
    const Node *ret = nullptr, *contracts = nullptr;
    for (const NodePtr &k : item->kids) {
      if (k->kind == NodeKind::RetAnnot && !k->kids.empty() &&
          k->kids[0]->kind == NodeKind::Annot && k->kids[0]->kids.size() > 1)
        ret = k->kids[0]->kids[1].get();
      if (k->kind == NodeKind::Contracts)
        contracts = k.get();
    }
    bool none = !contracts || contracts->kids.empty();
    if (none && declared.count(item->text))
      continue;
    std::vector<std::tuple<std::string, std::string, const Node *>> params;
    for (const NodePtr &p : item->kids[0]->kids)
      if (p->kind == NodeKind::Param && !p->kids.empty() &&
          p->kids[0]->kind == NodeKind::Annot && p->kids[0]->kids.size() > 1)
        params.emplace_back(p->text, p->kids[0]->kids[0]->text,
                            p->kids[0]->kids[1].get());
    std::vector<std::string> clauses =
        missing(params, ret, contracts, s, *item);
    if (clauses.empty())
      continue;
    // The clauses go on lines of their own before the body's `=`.
    const Node &body = *item->kids.back();
    size_t eq = body.loc.offset;
    while (eq > item->loc.offset && source[eq - 1] != '=')
      --eq;
    if (eq <= item->loc.offset)
      continue;
    --eq;
    size_t lineStart = source.rfind('\n', eq == 0 ? 0 : eq - 1);
    lineStart = lineStart == std::string_view::npos ? 0 : lineStart + 1;
    bool alone =
        source.substr(lineStart, eq - lineStart).find_first_not_of(" \t") ==
        std::string_view::npos;
    std::string lines;
    for (const std::string &c : clauses)
      lines += "  " + c + "\n";
    syntax::TextEdit e;
    if (alone) {
      e.begin = e.end = static_cast<uint32_t>(lineStart);
      e.text = lines;
    } else {
      size_t keep = eq;
      while (keep > lineStart &&
             (source[keep - 1] == ' ' || source[keep - 1] == '\t'))
        --keep;
      e.begin = static_cast<uint32_t>(keep);
      e.end = static_cast<uint32_t>(eq);
      e.text = "\n" + lines;
    }
    syntax::Lint l;
    l.name = rule.id;
    l.loc = item->loc;
    l.end = item->loc.offset;
    l.message = message(item->text, clauses);
    l.fixTitle = "Say the box is full, as it was";
    l.edits.push_back(std::move(e));
    l.preferred = true;
    out.push_back(std::move(l));
  }
}

} // namespace

Rule boxStates() {
  return {"box-states",
          "0.0.0+798",
          "every contract states the state of each box over a concept in its "
          "signature, and a call through a box requires it full",
          "ADR 0046",
          /*inBuilds=*/false,
          find};
}

} // namespace pia::migrate
