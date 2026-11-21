#include "repl/State.h"

#include <algorithm>
#include <functional>

namespace pia::repl {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;
using syntax::makeNode;

bool isStateItem(const Node &item) {
  if (item.kind != NodeKind::LetItem || item.kids.size() < 4) return false;
  if (item.flags.find("meta") != std::string::npos) return false;
  if (!item.kids[0]->kids.empty()) return false;  // parameters
  const Node &ret = *item.kids[1];
  if (ret.kind != NodeKind::RetAnnot || ret.kids.empty() ||
      ret.kids[0]->kind != NodeKind::Annot)
    return false;
  const Node &mods = *ret.kids[0]->kids[0];
  return mods.text.find("mutable") != std::string::npos;
}

namespace {

using Errors = std::vector<std::pair<syntax::SourceLoc, std::string>>;

struct Rewriter {
  std::map<std::string, const StateDecl *> states;
  std::vector<std::string> order;                       // state names
  std::map<std::string, std::vector<std::string>> uses;  // function -> states
  std::set<std::string> unitFns;  // functions written with `()`

  bool plain(const Node &n) const { return n.kind == NodeKind::Name && n.flags.empty(); }

  // `s.[0]`, the state's value.
  NodePtr value(const std::string &s, syntax::SourceLoc loc) const {
    NodePtr i = makeNode(NodeKind::Index, loc);
    i->add(makeNode(NodeKind::Name, loc, s));
    i->add(makeNode(NodeKind::IntLit, loc, "0"));
    return i;
  }

  // Each state becomes its value, and each call of a function that takes
  // state passes it the states it takes, first.
  void refs(NodePtr &n) {
    if (n->kind == NodeKind::Quote) return;  // metaprogram code
    if (n->kind == NodeKind::Apply && !n->kids.empty() && plain(*n->kids[0])) {
      auto u = uses.find(n->kids[0]->text);
      if (u != uses.end() && !u->second.empty()) {
        for (size_t i = 1; i < n->kids.size(); ++i) refs(n->kids[i]);
        std::vector<NodePtr> kids;
        kids.push_back(std::move(n->kids[0]));
        for (const std::string &s : u->second)
          kids.push_back(makeNode(NodeKind::Name, n->loc, s));
        bool unitCall = unitFns.count(kids[0]->text) && n->kids.size() == 2 &&
                        n->kids[1]->kind == NodeKind::Unit;
        if (!unitCall)
          for (size_t i = 1; i < n->kids.size(); ++i) kids.push_back(std::move(n->kids[i]));
        n->kids = std::move(kids);
        return;
      }
    }
    if (plain(*n)) {
      if (states.count(n->text)) {
        n = value(n->text, n->loc);
        return;
      }
      auto u = uses.find(n->text);
      if (u != uses.end() && !u->second.empty() && !unitFns.count(n->text)) {
        NodePtr app = makeNode(NodeKind::Apply, n->loc);
        syntax::SourceLoc loc = n->loc;
        app->add(std::move(n));
        for (const std::string &s : u->second)
          app->add(makeNode(NodeKind::Name, loc, s));
        n = std::move(app);
        return;
      }
    }
    for (NodePtr &k : n->kids) refs(k);
  }

  // The states `n` names, the states it assigns, and the other names.
  void scan(const Node &n, std::set<std::string> &used, std::set<std::string> &written,
            std::set<std::string> &names) const {
    if (n.kind == NodeKind::Quote) return;
    if (plain(n)) {
      if (states.count(n.text))
        used.insert(n.text);
      else
        names.insert(n.text);
    }
    if (n.kind == NodeKind::Assign && !n.kids.empty() && plain(*n.kids[0]) &&
        states.count(n.kids[0]->text))
      written.insert(n.kids[0]->text);
    for (const NodePtr &k : n.kids) scan(*k, used, written, names);
  }

  NodePtr param(const StateDecl &d) const {
    NodePtr p = makeNode(NodeKind::Param, d.loc, d.name);
    NodePtr a = makeNode(NodeKind::Annot, d.loc);
    a->add(makeNode(NodeKind::Modifiers, d.loc, "borrowed inout mutable"));
    NodePtr arr = makeNode(NodeKind::ArrayType, d.loc);
    arr->add(syntax::clone(*d.type));
    arr->add(makeNode(NodeKind::IntLit, d.loc, "1"));
    a->add(std::move(arr));
    a->add(makeNode(NodeKind::None, d.loc));
    p->add(std::move(a));
    return p;
  }

  void rewrite(Node &item, const std::vector<std::string> &states, bool writes) {
    Node &params = *item.kids[0];
    std::vector<NodePtr> ps;
    for (const std::string &s : states) ps.push_back(param(*this->states.at(s)));
    bool unit = params.kids.size() == 1 && params.kids[0]->kind == NodeKind::ParamUnit;
    if (!unit)
      for (NodePtr &k : params.kids) ps.push_back(std::move(k));
    params.kids = std::move(ps);

    Node &contracts = *item.kids[2];
    for (NodePtr &k : contracts.kids) refs(k);
    refs(item.kids[3]);
    std::vector<NodePtr> before, after;
    for (const std::string &s : states) {
      const StateDecl &d = *this->states.at(s);
      if (d.invariant) {
        NodePtr inv = syntax::clone(*d.invariant);
        refs(inv);
        // At the invariant, so a failure points at what it breaks.
        NodePtr r = makeNode(NodeKind::Requires, d.invariant->loc);
        r->add(syntax::clone(*inv));
        before.push_back(std::move(r));
        NodePtr e = makeNode(NodeKind::Ensures, d.invariant->loc);
        e->add(std::move(inv));
        after.push_back(std::move(e));
      }
      if (!writes) {
        NodePtr same = makeNode(NodeKind::Binary, item.loc, "=");
        same->add(value(s, item.loc));
        NodePtr old = makeNode(NodeKind::Apply, item.loc);
        old->add(makeNode(NodeKind::Name, item.loc, "old"));
        old->add(value(s, item.loc));
        same->add(std::move(old));
        NodePtr e = makeNode(NodeKind::Ensures, item.loc);
        e->add(std::move(same));
        after.push_back(std::move(e));
      }
    }
    for (NodePtr &k : contracts.kids) before.push_back(std::move(k));
    for (NodePtr &k : after) before.push_back(std::move(k));
    contracts.kids = std::move(before);

    // Between calls the invariants hold, and so at the top of every loop.
    std::vector<NodePtr> invs;
    for (const std::string &s : states) {
      const StateDecl &d = *this->states.at(s);
      if (!d.invariant) continue;
      NodePtr inv = syntax::clone(*d.invariant);
      refs(inv);
      invs.push_back(std::move(inv));
    }
    if (!invs.empty()) loops(*item.kids[3], invs);
  }

  void loops(Node &n, const std::vector<NodePtr> &invs) const {
    if (n.kind == NodeKind::Quote) return;
    if (n.kind == NodeKind::For || n.kind == NodeKind::While)
      for (NodePtr &k : n.kids)
        if (k->kind == NodeKind::LoopAnnots)
          for (const NodePtr &inv : invs) {
            NodePtr i = makeNode(NodeKind::Invariant, inv->loc);
            i->add(syntax::clone(*inv));
            k->kids.insert(k->kids.begin(), std::move(i));
          }
    for (NodePtr &k : n.kids) loops(*k, invs);
  }
};

// Replaces `old name` by `with`; says whether there was one.
bool replaceOld(NodePtr &n, const std::string &name, const std::function<NodePtr()> &with) {
  if (n->kind == NodeKind::Quote) return false;
  if (n->kind == NodeKind::Apply && n->kids.size() == 2 &&
      n->kids[0]->kind == NodeKind::Name && n->kids[0]->text == "old" &&
      n->kids[1]->kind == NodeKind::Name && n->kids[1]->flags.empty() &&
      n->kids[1]->text == name) {
    n = with();
    return true;
  }
  bool any = false;
  for (NodePtr &k : n->kids) any |= replaceOld(k, name, with);
  return any;
}

// Replaces `name` by `result`, for an invariant read as a postcondition.
void toResult(Node &n, const std::string &name) {
  if (n.kind == NodeKind::Name && n.flags.empty() && n.text == name) n.text = "result";
  for (NodePtr &k : n.kids) toResult(*k, name);
}

}  // namespace

StateUse rewriteState(Node &program, const std::vector<Node *> &extra,
                      const std::function<bool(const Node &)> &isNew, Errors &errors) {
  StateUse out;
  Rewriter rw;

  // The states, each replaced by its initial value's function, or dropped
  // when it keeps its value.
  for (auto it = program.kids.begin(); it != program.kids.end();) {
    NodePtr &k = *it;
    if (!isStateItem(*k)) {
      ++it;
      continue;
    }
    StateDecl d;
    d.name = k->text;
    d.loc = k->loc;
    d.type = syntax::clone(*k->kids[1]->kids[0]->kids[1]);
    for (NodePtr &c : k->kids[2]->kids) {
      if (c->kind == NodeKind::Invariant && !d.invariant)
        d.invariant = syntax::clone(*c->kids[0]);
      else
        errors.emplace_back(c->loc, "a state takes one 'invariant', and no other contract");
    }
    if (!isNew(*k)) {
      out.states.push_back(std::move(d));
      it = program.kids.erase(it);
      continue;
    }
    NodePtr init = makeNode(NodeKind::LetItem, k->loc, kInitPrefix + d.name);
    init->add(makeNode(NodeKind::Params, k->loc));
    NodePtr ret = makeNode(NodeKind::RetAnnot, k->loc);
    NodePtr annot = makeNode(NodeKind::Annot, k->loc);
    annot->add(makeNode(NodeKind::Modifiers, k->loc));
    annot->add(syntax::clone(*d.type));
    annot->add(makeNode(NodeKind::None, k->loc));
    ret->add(std::move(annot));
    ret->add(makeNode(NodeKind::Attrs, k->loc));
    init->add(std::move(ret));
    NodePtr cs = makeNode(NodeKind::Contracts, k->loc);
    if (d.invariant) {
      NodePtr e = makeNode(NodeKind::Ensures, d.invariant->loc);
      NodePtr inv = syntax::clone(*d.invariant);
      toResult(*inv, d.name);
      e->add(std::move(inv));
      cs->add(std::move(e));
    }
    init->add(std::move(cs));
    // `old count` is the value of the definition this one replaces.
    const Node *previous = nullptr;
    for (Node *e : extra)
      if (isStateItem(*e) && e->text == d.name) previous = e;
    const char *oldName = "__pia_old";
    NodePtr body = std::move(k->kids[3]);
    syntax::SourceLoc at = k->loc;
    d.migrates = replaceOld(body, d.name, [&] {
      NodePtr i = makeNode(NodeKind::Index, at);
      i->add(makeNode(NodeKind::Name, at, oldName));
      i->add(makeNode(NodeKind::IntLit, at, "0"));
      return i;
    });
    if (d.migrates && !previous) {
      errors.emplace_back(k->loc, "'old " + d.name + "' is the value of the '" + d.name +
                                      "' this definition replaces, but there is none; "
                                      "use :redef");
    } else if (d.migrates) {
      // (__pia_old : borrowed in [T_old; 1]) requires the old invariant.
      NodePtr p = makeNode(NodeKind::Param, k->loc, oldName);
      NodePtr pa = makeNode(NodeKind::Annot, k->loc);
      pa->add(makeNode(NodeKind::Modifiers, k->loc, "borrowed in"));
      NodePtr arr = makeNode(NodeKind::ArrayType, k->loc);
      arr->add(syntax::clone(*previous->kids[1]->kids[0]->kids[1]));
      arr->add(makeNode(NodeKind::IntLit, k->loc, "1"));
      pa->add(std::move(arr));
      pa->add(makeNode(NodeKind::None, k->loc));
      p->add(std::move(pa));
      init->kids[0]->add(std::move(p));
      for (const NodePtr &c : previous->kids[2]->kids) {
        if (c->kind != NodeKind::Invariant) continue;
        NodePtr inv = syntax::clone(*c->kids[0]);
        std::function<void(NodePtr &)> toOld = [&](NodePtr &n) {
          if (n->kind == NodeKind::Name && n->flags.empty() && n->text == d.name) {
            NodePtr i = makeNode(NodeKind::Index, n->loc);
            i->add(makeNode(NodeKind::Name, n->loc, oldName));
            i->add(makeNode(NodeKind::IntLit, n->loc, "0"));
            n = std::move(i);
            return;
          }
          for (NodePtr &kid : n->kids) toOld(kid);
        };
        toOld(inv);
        NodePtr r = makeNode(NodeKind::Requires, c->loc);
        r->add(std::move(inv));
        init->kids[2]->kids.insert(init->kids[2]->kids.begin(), std::move(r));
      }
    }
    init->add(std::move(body));
    k = std::move(init);
    out.states.push_back(std::move(d));
    ++it;
  }
  for (const StateDecl &d : out.states) {
    rw.states[d.name] = &d;
    rw.order.push_back(d.name);
  }

  std::vector<Node *> items;
  for (NodePtr &k : program.kids)
    if (k->kind == NodeKind::LetItem && k->flags.find("meta") == std::string::npos)
      items.push_back(k.get());
  for (Node *n : items) {
    for (const NodePtr &c : n->kids[2]->kids)
      if (c->kind == NodeKind::Invariant)
        errors.emplace_back(c->loc, "'invariant' belongs to a state, such as "
                                    "'let count : mutable u32 = 0 invariant count <= 9'");
    const Node &ps = *n->kids[0];
    if (ps.kids.size() == 1 && ps.kids[0]->kind == NodeKind::ParamUnit)
      rw.unitFns.insert(n->text);
  }
  if (rw.order.empty()) return out;

  // What each definition uses and writes, directly and through calls.
  struct Facts {
    std::set<std::string> used, written, names;
  };
  std::map<std::string, Facts> facts;
  auto factsOf = [&](const Node &n) {
    Facts f;
    rw.scan(*n.kids[2], f.used, f.written, f.names);
    rw.scan(*n.kids[3], f.used, f.written, f.names);
    return f;
  };
  for (Node *n : items) facts[n->text] = factsOf(*n);
  for (const StateDecl &d : out.states) {
    if (!facts.count(kInitPrefix + d.name)) continue;  // kept, checked before
    const Facts &f = facts[kInitPrefix + d.name];
    bool calls = false;
    for (const std::string &m : f.names)
      if (facts.count(m) && !facts[m].used.empty()) calls = true;
    if (!f.used.empty() || calls)
      errors.emplace_back(d.loc, "the initial value of '" + d.name +
                                     "' cannot use state; it is computed once, "
                                     "before anything runs");
    if (d.invariant) {
      std::set<std::string> used, written, names;
      rw.scan(*d.invariant, used, written, names);
      for (const std::string &s : used)
        if (s != d.name)
          errors.emplace_back(d.invariant->loc, "the invariant of '" + d.name +
                                                    "' can name only '" + d.name + "'");
    }
  }
  for (bool changed = true; changed;) {
    changed = false;
    for (auto &[name, f] : facts)
      for (const std::string &m : f.names) {
        auto g = facts.find(m);
        if (g == facts.end() || g->first == name) continue;
        for (const std::string &s : g->second.used) changed |= f.used.insert(s).second;
        for (const std::string &s : g->second.written) changed |= f.written.insert(s).second;
      }
  }
  auto inOrder = [&](const std::set<std::string> &used) {
    std::vector<std::string> v;
    for (const std::string &s : rw.order)
      if (used.count(s)) v.push_back(s);
    return v;
  };
  for (auto &[name, f] : facts) {
    if (f.used.empty()) continue;
    rw.uses[name] = inOrder(f.used);
    if (!f.written.empty()) out.writes.insert(name);
  }

  // Rewrite. An old version uses what its own body names, plus what the
  // current definitions it calls use.
  std::vector<std::pair<Node *, std::pair<std::vector<std::string>, bool>>> todo;
  for (Node *n : items) {
    auto u = rw.uses.find(n->text);
    todo.push_back({n, {u == rw.uses.end() ? std::vector<std::string>() : u->second,
                        out.writes.count(n->text) > 0}});
  }
  for (Node *n : extra) {
    if (n->kind != NodeKind::LetItem || isStateItem(*n)) continue;
    Facts f = factsOf(*n);
    for (const std::string &m : f.names) {
      auto g = facts.find(m);
      if (g == facts.end() || m == n->text) continue;
      f.used.insert(g->second.used.begin(), g->second.used.end());
      f.written.insert(g->second.written.begin(), g->second.written.end());
    }
    todo.push_back({n, {inOrder(f.used), !f.written.empty()}});
  }
  for (auto &[n, w] : todo) {
    if (w.first.empty()) {
      // It takes no state, but may still call what does (it cannot:
      // calling a function that uses state is using it), or name a state
      // in a quote; nothing to do.
      continue;
    }
    rw.rewrite(*n, w.first, w.second);
  }
  out.uses = rw.uses;
  for (const std::string &f : rw.unitFns)
    if (rw.uses.count(f)) out.unitFns.insert(f);
  return out;
}

}  // namespace pia::repl
