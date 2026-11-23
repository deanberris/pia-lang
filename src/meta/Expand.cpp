#include "meta/Expand.h"

#include <algorithm>
#include <functional>
#include <iterator>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "meta/Interpreter.h"
#include "meta/Totality.h"
#include "syntax/Parser.h"

namespace pia::meta {

using syntax::clone;
using syntax::Diagnostics;
using syntax::makeNode;
using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;
using syntax::SourceLoc;

namespace {

bool isMetaItem(const Node &item) {
  return item.kind == NodeKind::MetaOperator ||
         (item.kind == NodeKind::LetItem &&
          item.flags.find("meta") != std::string::npos);
}

bool isTypeItem(const Node &item) {
  return item.kind == NodeKind::LetItem && item.kids.size() > 3 &&
         item.kids[3]->kind == NodeKind::TypeValue;
}

const Node &preludeProgram() {
  static const NodePtr prelude = [] {
    Diagnostics diags;
    return syntax::parseProgram(syntax::preludeSource(), diags,
                                syntax::preludeOperators());
  }();
  return *prelude;
}

// The type names that resolve without a definition (docs/irgen.md, "Types").
bool isBuiltinType(const std::string &name) {
  static const std::set<std::string> names = {
      "u8", "u16", "u32", "u64", "i8",   "i16", "i32",
      "i64", "usize", "isize", "bool", "unit",
  };
  return names.count(name);
}

// A metaprogram that asked for a type that is not defined yet.
struct Waiting {
  std::string what;  // "@derive(eq) on 'pixel'" or "the call of 'gen'"
  std::string type;
  SourceLoc loc;
};

class Expander {
 public:
  Expander(Node &program, Diagnostics &diags, const Options &options)
      : program_(program),
        diags_(diags),
        options_(options),
        interp_([this](const std::string &t) {
          // A qualified name is an imported type, which the import has
          // already resolved: it is defined before expansion starts.
          return isBuiltinType(t) || types_.count(t) ||
                 t.find('.') != std::string::npos;
        }) {
    interp_.setLive(options.live);
  }

  void run() {
    declare(preludeProgram());
    declare(program_);
    for (unsigned pass = 1;; ++pass) {
      size_t errors = diags_.errors().size();
      producers_.clear();
      producerLoc_ = program_.loc;
      waiting_.clear();
      types_.clear();
      for (const NodePtr &item : program_.kids)
        if (isTypeItem(*item)) types_.insert(item->text);
      bool changed = runPass();
      if (diags_.errors().size() != errors) break;
      if (!changed) {
        for (const Waiting &w : waiting_)
          diags_.error(w.loc, w.what + " needs the type '" + w.type +
                                  "', which is never defined");
        break;
      }
      if (pass > options_.maxCycles) {
        std::string names;
        for (const std::string &p : producers_)
          names += (names.empty() ? "" : ", ") + p;
        diags_.error(producerLoc_,
                     "metaprograms did not reach a fixed point within " +
                         std::to_string(options_.maxCycles) +
                         " passes (--meta-cycles); still producing code: " +
                         names);
        break;
      }
    }
    std::vector<NodePtr> kept;
    for (NodePtr &item : program_.kids)
      // A concept stays: the compiler checks types against it (ADR 0034).
      // So does a type-level metaprogram, which types and `where`
      // predicates call (ADR 0035).
      if (!isMetaItem(*item) || syntax::isConceptItem(*item) ||
          syntax::isTypeLevelMetaItem(*item))
        kept.push_back(std::move(item));
    program_.kids = std::move(kept);
  }

 private:
  void declare(const Node &program) {
    for (const NodePtr &item : program.kids) {
      if (item->kind == NodeKind::MetaOperator) {
        if (item->kids[1]->kind != NodeKind::None) {
          diags_.error(item->loc, "operators declared for a type are not "
                                  "supported yet");
          continue;
        }
        operators_[item->text] = item.get();
        closures_.erase(item->text);
      } else if (isMetaItem(*item)) {
        interp_.define(*item);
        metaItems_[item->text] = item.get();
      }
    }
  }

  void produced(const std::string &who, SourceLoc at) {
    if (producers_.empty()) producerLoc_ = at;
    producers_.insert(who);
  }

  // One pass over the items that exist when it starts. Code a metaprogram
  // generates is expanded in the next pass.
  bool runPass() {
    bool changed = false;
    std::vector<NodePtr> out;
    std::vector<NodePtr> items = std::move(program_.kids);
    program_.kids.clear();
    // `listing ()` sees the items as this pass found them. They stay alive
    // until the pass ends.
    std::vector<const Node *> listing;
    for (const NodePtr &item : items) listing.push_back(item.get());
    interp_.setListing(std::move(listing), &program_);
    for (NodePtr &item : items) {
      if (isMetaItem(*item)) {
        // A concept's laws and contracts are code the compiler checks, so
        // their operators expand like any other code's.
        if (syntax::isConceptItem(*item)) changed |= expandOperators(item);
        out.push_back(std::move(item));
        continue;
      }
      // `let theory T = gen args` (ADR 0036, step 5).
      if (item->kind == NodeKind::Theory && item->flags == "call") {
        std::vector<NodePtr> generated;
        if (runTheoryCall(*item, generated)) {
          changed = true;
          for (NodePtr &g : generated) out.push_back(std::move(g));
        } else {
          out.push_back(std::move(item));
        }
        continue;
      }
      if (const Node *callee = metaCall(*item)) {
        std::vector<NodePtr> generated;
        if (runCall(*item, *callee, generated)) {
          changed = true;
          // The call's comments move to the first item it made.
          if (!generated.empty()) moveComments(*item, *generated[0]);
          for (NodePtr &g : generated) out.push_back(std::move(g));
        } else {
          out.push_back(std::move(item));
        }
        continue;
      }
      std::vector<NodePtr> generated;
      if (isTypeItem(*item)) changed |= liftPayloads(*item, out);
      if (isTypeItem(*item)) changed |= runDerives(*item, generated);
      // `@by(t)` on a lemma, at the top level or in a theory (ADR 0036,
      // step 6), before its operators expand, so the tactic sees the goal
      // as written.
      if (item->kind == NodeKind::LetItem) changed |= runTactic(*item);
      if (item->kind == NodeKind::Theory && item->flags != "call")
        for (NodePtr &m : item->kids)
          if (m->kind == NodeKind::LetItem) changed |= runTactic(*m);
      changed |= expandOperators(item);
      out.push_back(std::move(item));
      for (NodePtr &g : generated) out.push_back(std::move(g));
    }
    program_.kids = std::move(out);
    interp_.setListing({}, &program_);
    return changed;
  }

  // Comments survive the code they were attached to being replaced
  // (ADR 0029).
  static void moveComments(Node &from, Node &to) {
    to.comments.insert(to.comments.begin(),
                       std::make_move_iterator(from.comments.begin()),
                       std::make_move_iterator(from.comments.end()));
    from.comments.clear();
  }

  // The callee of a top-level metaprogram call such as `gen 4`, or null.
  const Node *metaCall(const Node &item) {
    if (item.kind != NodeKind::ExprItem) return nullptr;
    const Node &e = *item.kids[0];
    const Node &head = e.kind == NodeKind::Apply ? *e.kids[0] : e;
    if (head.kind == NodeKind::Name && interp_.isMeta(head.text)) return &head;
    return nullptr;
  }

  // Adds the items a metaprogram produced to `out`.
  bool takeItems(const ValuePtr &v, SourceLoc at, const std::string &who,
                 std::vector<NodePtr> &out) {
    if (v->kind == Value::Kind::Unit) return true;
    // A list of items, such as one test per generated case (ADR 0056).
    if (v->kind == Value::Kind::List) {
      for (const ValuePtr &x : v->list)
        if (!takeItems(x, at, who, out))
          return false;
      return true;
    }
    if (v->kind == Value::Kind::Syntax && v->syntax) {
      const Node &n = *v->syntax;
      if (n.kind == NodeKind::Program) {
        for (const NodePtr &k : n.kids) out.push_back(clone(*k));
        return true;
      }
      if (n.kind == NodeKind::LetItem || n.kind == NodeKind::Theory ||
          n.kind == NodeKind::Model) {
        out.push_back(clone(n));
        return true;
      }
      // A call of another metaprogram runs in the next pass.
      auto call = makeNode(NodeKind::ExprItem, at);
      call->add(clone(n));
      if (metaCall(*call)) {
        out.push_back(std::move(call));
        return true;
      }
    }
    diags_.error(at, who + " must produce items");
    return false;
  }

  bool runCall(const Node &item, const Node &callee,
               std::vector<NodePtr> &out) {
    std::string who = "the metaprogram '" + callee.text + "'";
    try {
      interp_.setSite(item.loc);
      ValuePtr v = interp_.eval(*item.kids[0]);
      produced(callee.text, item.loc);
      return takeItems(v, item.loc, who, out);
    } catch (const Deferred &d) {
      waiting_.push_back({"the call of '" + callee.text + "'", d.type,
                          item.loc});
    } catch (const MetaError &e) {
      diags_.error(e.loc, who + " failed: " + e.message);
    }
    return false;
  }

  // `let theory T = gen args`: runs the metaprogram `gen`, which must be
  // total and pure, since what it returns becomes hypotheses of proofs
  // (ADR 0035, ADR 0036). It returns one theory, under any name, and any
  // number of models of it and other items. The theory is named T and
  // the models' theory is T. One argument tuple builds one theory: a
  // second `let theory U` with the same call names the same theory.
  bool runTheoryCall(const Node &item, std::vector<NodePtr> &out) {
    const Node &call = *item.kids[0];
    const Node &head = call.kind == NodeKind::Apply ? *call.kids[0] : call;
    if (head.kind != NodeKind::Name || !interp_.isMeta(head.text)) {
      diags_.error(call.loc, "a theory is a 'sig ... end', or a call of a "
                             "metaprogram that builds one");
      return false;
    }
    std::string who = "the metaprogram '" + head.text + "'";
    if (std::optional<std::string> why = notTotal(head.text)) {
      diags_.error(call.loc, "'" + head.text + "' builds a theory, so it must "
                             "terminate and be pure, but " + *why);
      return false;
    }
    // The instance: the generator and its arguments, as written.
    std::string key = instanceKey(call);
    if (auto it = instances_.find(key); it != instances_.end()) {
      auto alias = makeNode(NodeKind::Theory, item.loc, item.text);
      alias->flags = "alias";
      alias->add(makeNode(NodeKind::TypeName, item.loc, it->second));
      out.push_back(std::move(alias));
      produced(who, item.loc);
      return true;
    }
    std::vector<NodePtr> items;
    try {
      interp_.setSite(item.loc);
      ValuePtr v = interp_.eval(call);
      produced(head.text, item.loc);
      if (v->kind == Value::Kind::List) {
        for (const ValuePtr &e : v->list)
          if (!takeItems(e, item.loc, who, items)) return false;
      } else if (!takeItems(v, item.loc, who, items)) {
        return false;
      }
    } catch (const Deferred &d) {
      waiting_.push_back({"the theory '" + item.text + "'", d.type, item.loc});
      return false;
    } catch (const MetaError &e) {
      diags_.error(e.loc, who + " failed: " + e.message);
      return false;
    }
    std::string built;
    for (NodePtr &g : items)
      if (g->kind == NodeKind::Theory) {
        if (!built.empty()) {
          diags_.error(item.loc, who + " must build one theory, and it "
                                 "built '" + built + "' and '" + g->text + "'");
          return false;
        }
        built = g->text;
        g->text = item.text;
        g->loc = item.loc;
        // `let theory T @solver(...) = gen args` (ADR 0036, step 6).
        if (item.kids.size() > 1 && item.kids[1]->kind == NodeKind::Attrs)
          syntax::applyTheoryAttrs(*g, *item.kids[1]);
      }
    if (built.empty()) {
      diags_.error(item.loc, who + " must build a theory, a 'let theory ... "
                             "= sig ... end'");
      return false;
    }
    for (NodePtr &g : items)
      if (g->kind == NodeKind::Model && !g->kids.empty() &&
          g->kids[0]->text == built)
        g->kids[0]->text = item.text;
    instances_[key] = item.text;
    for (NodePtr &g : items) out.push_back(std::move(g));
    return true;
  }

  static std::string instanceKey(const Node &n) {
    std::string out = syntax::nodeKindName(n.kind);
    out += "(" + n.text;
    for (const NodePtr &k : n.kids) out += " " + instanceKey(*k);
    return out + ")";
  }

  // Why the metaprogram `name` may not terminate or is impure, through the
  // metaprograms it calls; nothing when it is total.
  std::optional<std::string> notTotal(const std::string &name) {
    std::map<std::string, int> state;  // 1 visiting, 2 done
    std::function<std::optional<std::string>(const std::string &)> visit =
        [&](const std::string &n) -> std::optional<std::string> {
      auto it = metaItems_.find(n);
      if (it == metaItems_.end()) return std::nullopt;
      state[n] = 1;
      std::set<std::string> callees;
      if (std::optional<std::string> why = checkOwnTotality(
              *it->second,
              [&](const std::string &c) { return metaItems_.count(c) > 0; },
              callees)) {
        if (n == name) return why;
        return "it calls '" + n + "', which may not terminate: " + *why;
      }
      for (const std::string &c : callees) {
        if (state[c] == 1)
          return std::string("it is mutually recursive with '") + c +
                 "', which is not supported yet";
        if (state[c] == 0)
          if (std::optional<std::string> why = visit(c)) return why;
      }
      state[n] = 2;
      return std::nullopt;
    };
    return visit(name);
  }

  static bool hasWord(const std::string &flags, const char *word) {
    size_t pos = 0;
    std::string w = word;
    while (pos <= flags.size()) {
      size_t end = flags.find(' ', pos);
      if (end == std::string::npos) end = flags.size();
      if (flags.compare(pos, end - pos, w) == 0) return true;
      pos = end + 1;
    }
    return false;
  }

  // `@by(t args)` on a lemma runs the tactic `t`, a metaprogram, on the
  // lemma's goal and the arguments (ADR 0036, step 6). The goal is the
  // lemma itself, read with `hypotheses`, `conclusion` and `params`; in
  // the arguments, the lemma's parameters stand for themselves. The
  // tactic returns proof steps, which go before the lemma's body and are
  // proved like hand-written ones: lemma calls, `assert`s, case splits
  // (`if`), quantifier instances, and `fuel n`, which is not code but
  // asks for `@fuel(n)` on the lemma. So a tactic can make a proof
  // possible, or faster, but never wrong. It must be total and pure, by
  // the rules for type-level metaprograms (ADR 0035).
  bool runTactic(Node &item) {
    if (item.kids.size() < 4 || item.kids[1]->kind != NodeKind::RetAnnot ||
        item.kids[1]->kids.size() < 2)
      return false;
    Node &attrs = *item.kids[1]->kids[1];
    NodePtr by;
    for (auto it = attrs.kids.begin(); it != attrs.kids.end(); ++it)
      if ((*it)->text == "by") {
        by = std::move(*it);
        attrs.kids.erase(it);
        break;
      }
    if (!by) return false;
    if (!hasWord(item.flags, "lemma")) {
      diags_.error(by->loc, "@by applies only to a lemma: a tactic writes "
                            "the steps of a proof");
      return true;
    }
    if (by->kids.size() != 1) {
      diags_.error(by->loc, "@by takes one tactic, applied to its "
                            "arguments, as in @by(induction n)");
      return true;
    }
    const Node &e = *by->kids[0];
    const Node &head = e.kind == NodeKind::Apply ? *e.kids[0] : e;
    if (head.kind != NodeKind::Name || !interp_.isMeta(head.text)) {
      diags_.error(by->loc, "a tactic is a 'let meta' that takes a goal and "
                            "returns proof steps, and '" +
                                (head.kind == NodeKind::Name ? head.text
                                                             : std::string("this")) +
                                "' is not one");
      return true;
    }
    std::string who = "the tactic '" + head.text + "'";
    if (std::optional<std::string> why = notTotal(head.text)) {
      diags_.error(by->loc, "'" + head.text + "' is a tactic, so it must "
                            "terminate and be pure, but " + *why);
      return true;
    }
    std::vector<std::pair<std::string, ValuePtr>> bindings;
    bindings.emplace_back("goal#", Interpreter::syntaxValue(clone(item)));
    for (const NodePtr &p : item.kids[0]->kids)
      if (p->kind == NodeKind::Param)
        bindings.emplace_back(p->text, Interpreter::syntaxValue(
                                           makeNode(NodeKind::Name, p->loc, p->text)));
    auto call = makeNode(NodeKind::Apply, by->loc);
    call->add(clone(head));
    call->add(makeNode(NodeKind::Name, by->loc, "goal#"));
    if (e.kind == NodeKind::Apply)
      for (size_t i = 1; i < e.kids.size(); ++i) call->add(clone(*e.kids[i]));
    ValuePtr v;
    try {
      interp_.setSite(by->loc);
      v = interp_.evalWith(*call, bindings);
      produced(head.text, by->loc);
    } catch (const Deferred &d) {
      diags_.error(by->loc, who + " needs the type '" + d.type + "'");
      return true;
    } catch (const MetaError &err) {
      diags_.error(err.loc, who + " failed: " + err.message);
      return true;
    }
    std::vector<ValuePtr> steps;
    if (v->kind == Value::Kind::List)
      steps = v->list;
    else if (v->kind != Value::Kind::Unit)
      steps.push_back(v);
    std::vector<NodePtr> code;
    for (const ValuePtr &step : steps) {
      if (step->kind != Value::Kind::Syntax || !step->syntax ||
          step->syntax->kind == NodeKind::Program ||
          step->syntax->kind == NodeKind::LetItem) {
        diags_.error(by->loc, who + " must return proof steps, which are "
                              "expressions, not " +
                                  std::string(step->kind == Value::Kind::Syntax &&
                                                      step->syntax
                                                  ? syntax::nodeKindName(step->syntax->kind)
                                                  : Interpreter::kindName(step->kind)));
        return true;
      }
      const Node &n = *step->syntax;
      // `fuel n`: a hint, not code.
      if (n.kind == NodeKind::Apply && n.kids.size() == 2 &&
          n.kids[0]->kind == NodeKind::Name && n.kids[0]->text == "fuel" &&
          n.kids[1]->kind == NodeKind::IntLit) {
        NodePtr fuel;
        for (NodePtr &a : attrs.kids)
          if (a->text == "fuel") fuel = clone(*a);
        attrs.kids.erase(std::remove_if(attrs.kids.begin(), attrs.kids.end(),
                                        [](const NodePtr &a) { return a->text == "fuel"; }),
                         attrs.kids.end());
        auto hint = makeNode(NodeKind::Attribute, by->loc, "fuel");
        const Node *keep = n.kids[1].get();
        if (fuel && fuel->kids.size() == 1 &&
            fuel->kids[0]->kind == NodeKind::IntLit &&
            std::stoll(fuel->kids[0]->text) > std::stoll(keep->text))
          keep = fuel->kids[0].get();
        hint->add(clone(*keep));
        attrs.add(std::move(hint));
        continue;
      }
      code.push_back(clone(n));
    }
    NodePtr body = std::move(item.kids[3]);
    for (auto it = code.rbegin(); it != code.rend(); ++it) {
      auto seq = makeNode(NodeKind::Sequence, (*it)->loc);
      seq->add(std::move(*it));
      seq->add(std::move(body));
      body = std::move(seq);
    }
    item.kids[3] = std::move(body);
    return true;
  }

  // `| Circle of { r : u16 }`: a constructor's record payload becomes a
  // record type of its own, `shape_Circle`, defined just before the
  // variant, and the payload names it. Its fields keep their attributes,
  // for the variant's derives to read (ADR 0045, step 5).
  bool liftPayloads(Node &item, std::vector<NodePtr> &out) {
    Node &body = *item.kids[3]->kids[0];
    if (body.kind != NodeKind::Variants) return false;
    bool changed = false;
    for (NodePtr &c : body.kids) {
      if (c->kids.empty() || c->kids[0]->kind != NodeKind::RecordType)
        continue;
      std::string name = item.text + "_" + c->text;
      auto rec = makeNode(NodeKind::LetItem, c->kids[0]->loc, name);
      rec->flags = "payload";
      rec->add(makeNode(NodeKind::Params, c->loc));
      rec->add(makeNode(NodeKind::None, c->loc));
      rec->add(makeNode(NodeKind::Contracts, c->loc));
      auto value = makeNode(NodeKind::TypeValue, c->loc);
      value->add(std::move(c->kids[0]));
      value->add(makeNode(NodeKind::Attrs, c->loc));
      value->add(makeNode(NodeKind::None, c->loc));
      rec->add(std::move(value));
      c->kids[0] = makeNode(NodeKind::TypeName, c->loc, name);
      payloadOf_[name] = item.text;
      lifted_[name] = rec.get();
      types_.insert(name);
      out.push_back(std::move(rec));
      changed = true;
    }
    return changed;
  }

  // Runs each `@derive(x)` on a type item through `derive_x`.
  bool runDerives(Node &item, std::vector<NodePtr> &out) {
    Node &attrs = *item.kids[3]->kids[1];
    // What each derive is given: the item as written, taken before the
    // loop below moves its attributes, so an attribute before @derive is
    // still there for the derive to read.
    NodePtr given = clone(item);
    bool changed = false;
    std::vector<NodePtr> keptAttrs;
    for (NodePtr &attr : attrs.kids) {
      if (attr->text != "derive") {
        keptAttrs.push_back(std::move(attr));
        continue;
      }
      std::vector<NodePtr> keptArgs;
      for (NodePtr &arg : attr->kids) {
        if (arg->kind != NodeKind::Name) {
          diags_.error(arg->loc, "@derive takes the names of derives");
          continue;
        }
        std::string fn = "derive_" + arg->text;
        std::string what = "@derive(" + arg->text + ") on '" + item.text + "'";
        if (!interp_.isMeta(fn)) {
          diags_.error(arg->loc, "there is no metaprogram '" + fn + "' for " +
                                     what);
          continue;
        }
        try {
          interp_.setSite(attr->loc);
          Node callee;
          callee.kind = NodeKind::Name;
          callee.text = fn;
          ValuePtr f = interp_.eval(callee);
          ValuePtr v = interp_.apply(f, {Interpreter::syntaxValue(clone(*given))});
          produced(fn, attr->loc);
          takeItems(v, attr->loc, what, out);
          derived_[item.text].insert(arg->text);
          changed = true;
        } catch (const Deferred &d) {
          waiting_.push_back({what, d.type, arg->loc});
          keptArgs.push_back(std::move(arg));
        } catch (const MetaError &e) {
          diags_.error(e.loc, what + " failed: " + e.message);
          // Its attributes were for it, so they are not reported again.
          derived_[item.text].insert(arg->text);
        }
      }
      if (!keptArgs.empty()) {
        attr->kids = std::move(keptArgs);
        keptAttrs.push_back(std::move(attr));
      }
    }
    attrs.kids = std::move(keptAttrs);
    changed |= settleAttrs(item);
    return changed;
  }

  // A derive's own attributes, such as @json(name = "x") on a field, are
  // for it to read (ADR 0045, step 3). Once it has run they leave the
  // type, its fields and its constructors, so that nothing else sees
  // them, and an attribute on a field or a constructor that no derive of
  // the type reads is an error rather than silently ignored.
  bool settleAttrs(Node &item) {
    std::set<std::string> pending;
    for (const NodePtr &attr : item.kids[3]->kids[1]->kids)
      if (attr->text == "derive")
        for (const NodePtr &arg : attr->kids) pending.insert(arg->text);
    // A lifted payload record's attributes are for its variant's derives,
    // which settle them with the variant's own.
    if (payloadOf_.count(item.text)) return false;
    const std::set<std::string> &done = derived_[item.text];
    bool changed = false;
    auto settle = [&](Node &attrs, const std::string *member) {
      std::vector<NodePtr> kept;
      for (NodePtr &a : attrs.kids) {
        if (a->text == "derive" || pending.count(a->text)) {
          kept.push_back(std::move(a));
        } else if (done.count(a->text)) {
          changed = true;
        } else if (member) {
          diags_.error(a->loc, "the attribute @" + a->text + " on '" +
                                   *member + "' is read by no derive of '" +
                                   item.text + "'; add @derive(" + a->text +
                                   ") to the type, or remove it");
          changed = true;
        } else {
          kept.push_back(std::move(a));
        }
      }
      attrs.kids = std::move(kept);
    };
    settle(*item.kids[3]->kids[1], nullptr);
    Node &body = *item.kids[3]->kids[0];
    if (body.kind == NodeKind::RecordType || body.kind == NodeKind::Variants)
      for (NodePtr &m : body.kids)
        for (NodePtr &k : m->kids)
          if (k->kind == NodeKind::Attrs) settle(*k, &m->text);
    if (body.kind == NodeKind::Variants)
      for (NodePtr &c : body.kids)
        if (auto r = lifted_.find(item.text + "_" + c->text); r != lifted_.end())
          for (NodePtr &f : r->second->kids[3]->kids[0]->kids)
            for (NodePtr &k : f->kids)
              if (k->kind == NodeKind::Attrs) settle(*k, &f->text);
    return changed;
  }

  // Replaces each binary operator by its expansion, innermost first.
  bool expandOperators(NodePtr &slot) {
    if (slot->kind == NodeKind::Quote) return false;
    bool changed = false;
    for (NodePtr &k : slot->kids) changed |= expandOperators(k);
    if (slot->kind != NodeKind::Binary) return changed;
    const std::string &op = slot->text;
    auto decl = operators_.find(op);
    if (decl == operators_.end()) {
      diags_.error(slot->loc, "the operator '" + op +
                                  "' is not declared; declare it with "
                                  "'let meta operator ( " + op + " )'");
      return changed;
    }
    std::string who = "operator ( " + op + " )";
    try {
      interp_.setSite(slot->loc);
      ValuePtr &fn = closures_[op];
      if (!fn) fn = interp_.eval(*decl->second->kids[2]);
      ValuePtr v = interp_.apply(
          fn, {Interpreter::syntaxValue(clone(*slot->kids[0])),
               Interpreter::syntaxValue(clone(*slot->kids[1]))});
      if (v->kind != Value::Kind::Syntax || !v->syntax ||
          v->syntax->kind == NodeKind::Program) {
        diags_.error(slot->loc, who + " must produce an expression");
        return changed;
      }
      NodePtr replacement = clone(*v->syntax);
      moveComments(*slot, *replacement);
      slot = std::move(replacement);
      produced(who, slot->loc);
      return true;
    } catch (const MetaError &e) {
      diags_.error(e.loc, who + " failed: " + e.message);
    } catch (const Deferred &d) {
      diags_.error(slot->loc, who + " needs the type '" + d.type + "'");
    }
    return changed;
  }

  Node &program_;
  Diagnostics &diags_;
  Options options_;
  Interpreter interp_;
  std::map<std::string, const Node *> operators_;
  std::map<std::string, ValuePtr> closures_;
  std::set<std::string> types_;
  std::set<std::string> producers_;
  SourceLoc producerLoc_;  // where the first of them ran in the last pass
  std::vector<Waiting> waiting_;
  // The derives that have run on each type item, by its name.
  std::map<std::string, std::set<std::string>> derived_;
  // A lifted payload record's variant, by the record's name.
  std::map<std::string, std::string> payloadOf_;
  // Each lifted payload record, by its name; the program owns it.
  std::map<std::string, Node *> lifted_;
  // Theory-building metaprograms (ADR 0036): every `let meta`, for the
  // totality check, and each instance built, by its call.
  std::map<std::string, const Node *> metaItems_;
  std::map<std::string, std::string> instances_;
};

}  // namespace

bool expand(Node &program, Diagnostics &diags, const Options &options) {
  size_t before = diags.errors().size();
  Expander(program, diags, options).run();
  return diags.errors().size() == before;
}

}  // namespace pia::meta
