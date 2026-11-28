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
      "u8",  "u16",   "u32",   "u64", "i8",  "i16",  "i32",
      "i64", "usize", "isize", "f32", "f64", "bool", "unit",
  };
  return names.count(name);
}

// `let name = let (t : type) ... => type ...`: a generic type.
bool isGenericTypeItem(const Node &item) {
  return item.kind == NodeKind::LetItem && item.kids.size() > 3 &&
         item.kids[0]->kids.empty() && item.kids[3]->kind == NodeKind::Lambda &&
         !item.kids[3]->kids.empty() &&
         item.kids[3]->kids.back()->kind == NodeKind::TypeValue;
}

// The dotted name of `a.b.c`, or "" when `e` is not a chain of names.
std::string dottedName(const Node &e) {
  if (e.kind == NodeKind::Name)
    return e.text;
  if (e.kind != NodeKind::Field || e.kids.size() != 1)
    return "";
  std::string base = dottedName(*e.kids[0]);
  return base.empty() ? "" : base + "." + e.text;
}

// The type that the expression `e` names, written as a type, or null when
// it names none of `types` (ADR 0064, section 1): `u8`, `byte`,
// `option u8`, `Pia.Core.Option.option u8`, `[u8; 4]` and `[u8]`. A type
// is a value, so `let byte = u8` is another name for `u8`, while
// `let length = type u32` makes a new type.
NodePtr asType(const Node &e, const std::set<std::string> &types,
               const std::set<std::string> &generics) {
  if (e.kind == NodeKind::TypeValue && e.flags == "alias")
    return clone(*e.kids[0]);
  std::string name = dottedName(e);
  if (!name.empty()) {
    if (!isBuiltinType(name) && !types.count(name))
      return nullptr;
    return makeNode(NodeKind::TypeName, e.loc, name);
  }
  // `(a | b)`, which an expression reads as `bor a b`: the error set of
  // both (ADR 0028), so `let e = (a | b)` names a union.
  if (e.kind == NodeKind::Apply && e.kids.size() == 3 &&
      e.kids[0]->kind == NodeKind::Name && e.kids[0]->text == "bor" &&
      e.kids[0]->flags == "prelude") {
    auto u = makeNode(NodeKind::UnionType, e.loc);
    for (size_t i = 1; i < 3; ++i) {
      NodePtr t = asType(*e.kids[i], types, generics);
      if (!t)
        return nullptr;
      // `a | b | c` is `bor (bor a b) c`: one union of all three.
      if (t->kind == NodeKind::UnionType) {
        for (NodePtr &k : t->kids)
          u->add(std::move(k));
        continue;
      }
      u->add(std::move(t));
    }
    return u;
  }
  if (e.kind == NodeKind::Apply && e.kids.size() > 1) {
    std::string head = dottedName(*e.kids[0]);
    if (head.empty() || !generics.count(head))
      return nullptr;
    auto app = makeNode(NodeKind::TypeApp, e.loc);
    app->add(makeNode(NodeKind::TypeName, e.kids[0]->loc, head));
    for (size_t i = 1; i < e.kids.size(); ++i) {
      const Node &a = *e.kids[i];
      if (a.kind == NodeKind::IntLit) {
        app->add(clone(a));
        continue;
      }
      NodePtr t = asType(a, types, generics);
      if (!t)
        return nullptr;
      app->add(std::move(t));
    }
    return app;
  }
  if (e.kind == NodeKind::ListLit &&
      (e.kids.size() == 1 || e.kids.size() == 2)) {
    NodePtr elem = asType(*e.kids[0], types, generics);
    if (!elem)
      return nullptr;
    if (e.kids.size() == 1) {
      auto slice = makeNode(NodeKind::SliceType, e.loc);
      slice->add(std::move(elem));
      return slice;
    }
    if (e.kids[1]->kind != NodeKind::IntLit)
      return nullptr;
    auto array = makeNode(NodeKind::ArrayType, e.loc);
    array->add(std::move(elem));
    array->add(clone(*e.kids[1]));
    return array;
  }
  return nullptr;
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
    interp_.setEmbedOptions(&options_.embeds);
  }

  void run() {
    declare(preludeProgram());
    declare(program_);
    checkListedMetaprograms();
    for (unsigned pass = 1;; ++pass) {
      size_t errors = diags_.errors().size();
      producers_.clear();
      producerLoc_ = program_.loc;
      waiting_.clear();
      types_.clear();
      nameAliases();
      makeDistinct();
      convertCalls();
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
   // `let byte = u8`, and `let buf = option byte` after it: a `let` with
   // no parameters, annotation or contracts whose value names a type is
   // another name for that type, the type item `let byte = type u8` marked
   // "alias" (ADR 0064, section 1). Repeated until nothing changes, so a
   // chain of aliases resolves in any order.
   void nameAliases() {
     std::set<std::string> types, generics;
     for (const Node *program :
          {&preludeProgram(), static_cast<const Node *>(&program_)})
       for (const NodePtr &item : program->kids) {
         if (isTypeItem(*item))
           types.insert(item->text);
         if (isGenericTypeItem(*item))
           generics.insert(item->text);
       }
     for (bool changed = true; changed;) {
       changed = false;
       for (NodePtr &item : program_.kids) {
         if (item->kind != NodeKind::LetItem || item->kids.size() != 4 ||
             isTypeItem(*item) || isMetaItem(*item) ||
             !item->kids[0]->kids.empty() ||
             item->kids[1]->kind != NodeKind::None ||
             !item->kids[2]->kids.empty())
           continue;
         NodePtr t = asType(*item->kids[3], types, generics);
         if (!t)
           continue;
         auto value = makeNode(NodeKind::TypeValue, item->kids[3]->loc);
         value->flags = "alias";
         value->add(std::move(t));
         value->add(makeNode(NodeKind::Attrs, item->kids[3]->loc));
         value->add(makeNode(NodeKind::None, item->kids[3]->loc));
         item->kids[3] = std::move(value);
         types.insert(item->text);
         changed = true;
       }
     }
   }

   // An interface's `let meta m : item` (any result but `concept`) lists a
   // metaprogram, which the module must define (ADR 0039).
   void checkListedMetaprograms() {
     for (const NodePtr &item : program_.kids) {
       if (item->kind != NodeKind::Interface)
         continue;
       for (const NodePtr &r : item->kids) {
         if (r->kind != NodeKind::SigVal || r->flags != "meta")
           continue;
         const Node &t = *r->kids[0]->kids[1];
         if (t.kind != NodeKind::TypeName || t.text == "concept")
           continue;
         if (!metaItems_.count(r->text))
           diags_.error(r->loc, "the interface '" + item->text +
                                    "' lists the metaprogram '" + r->text +
                                    "', which the module does not define");
       }
     }
   }

   // `let length = type u32`: a new type, distinct from u32 (ADR 0064,
   // section 2). It becomes a record of one field that no source can name,
   // since its name holds a `#`, and two conversions:
   //
   //   let length = type { raw#length : u32 }          (flagged "distinct")
   //   let length#of (x : u32) : length  ensures result.raw#length = x
   //   let u32#of (x : length) : u32     ensures result = x.raw#length
   //
   // `length 5` calls the first and `u32 l` the second (convertCalls), so
   // every conversion is written, and a distinct type over a record or
   // scalar costs nothing once records are scalarized.
   void makeDistinct() {
     std::vector<NodePtr> out;
     for (NodePtr &item : program_.kids) {
       if (!isTypeItem(*item) || item->kids[3]->flags == "alias" ||
           item->flags.find("distinct") != std::string::npos) {
         out.push_back(std::move(item));
         continue;
       }
       Node &value = *item->kids[3];
       NodeKind body = value.kids[0]->kind;
       // A refinement type, `type { n : u32 | n <= 64 }`, names a subset
       // of its base rather than a new type (ADR 0006).
       if (body == NodeKind::RecordType || body == NodeKind::Variants ||
           body == NodeKind::RefinementType ||
           (body == NodeKind::TypeName && value.kids[0]->text == "#sort")) {
         out.push_back(std::move(item));
         continue;
       }
       const std::string n = item->text;
       if (n.find('.') != std::string::npos) {
         diags_.error(item->loc, "importing the distinct type '" + n +
                                     "' is not supported yet (ADR 0064)");
         out.push_back(std::move(item));
         continue;
       }
       if (value.kids.size() > 2 && value.kids[2]->kind != NodeKind::None) {
         diags_.error(value.kids[2]->loc,
                      "a distinct type with a 'where' refinement is not "
                      "supported yet (ADR 0064, section 6)");
         out.push_back(std::move(item));
         continue;
       }
       SourceLoc at = item->loc;
       const std::string field = "raw#" + n;
       NodePtr under = std::move(value.kids[0]);
       auto annot = [&](NodePtr type) {
         auto a = makeNode(NodeKind::Annot, at);
         a->add(makeNode(NodeKind::Modifiers, at));
         a->add(std::move(type));
         a->add(makeNode(NodeKind::None, at));
         return a;
       };
       auto record = makeNode(NodeKind::RecordType, at);
       auto decl = makeNode(NodeKind::FieldDecl, at, field);
       decl->add(annot(clone(*under)));
       record->add(std::move(decl));
       value.kids[0] = std::move(record);
       item->flags += item->flags.empty() ? "distinct" : " distinct";
       distinct_[n] = clone(*under);
       // A distinct arrow type (ADR 0071, amendment of 2026-11-28) holds a
       // function reference: `op succ` stores `succ` in the field, where it
       // is checked against the arrow, and nothing converts an `op` back,
       // since an `op` is called as it is.
       if (under->kind == NodeKind::ArrowType) {
         arrowTypes_.insert(n);
         out.push_back(std::move(item));
         continue;
       }

       auto fn = [&](const std::string &name, NodePtr param, NodePtr result,
                     NodePtr ensures, NodePtr body) {
         auto f = makeNode(NodeKind::LetItem, at, name);
         auto ps = makeNode(NodeKind::Params, at);
         auto x = makeNode(NodeKind::Param, at, "x");
         x->add(annot(std::move(param)));
         ps->add(std::move(x));
         f->add(std::move(ps));
         auto ret = makeNode(NodeKind::RetAnnot, at);
         ret->add(annot(std::move(result)));
         ret->add(makeNode(NodeKind::Attrs, at));
         f->add(std::move(ret));
         auto cs = makeNode(NodeKind::Contracts, at);
         auto e = makeNode(NodeKind::Ensures, at);
         e->add(std::move(ensures));
         cs->add(std::move(e));
         f->add(std::move(cs));
         f->add(std::move(body));
         return f;
       };
       auto name = [&](const std::string &t) {
         return makeNode(NodeKind::Name, at, t);
       };
       auto rawOf = [&](const std::string &v) {
         auto f = makeNode(NodeKind::Field, at, field);
         f->add(name(v));
         return f;
       };
       auto equals = [&](NodePtr a, NodePtr b) {
         auto eq = makeNode(NodeKind::Binary, at, "=");
         eq->add(std::move(a));
         eq->add(std::move(b));
         return eq;
       };
       auto lit = makeNode(NodeKind::RecordLit, at);
       auto init = makeNode(NodeKind::FieldInit, at, field);
       init->add(name("x"));
       lit->add(std::move(init));
       NodePtr make =
           fn(n + "#of", clone(*under), makeNode(NodeKind::TypeName, at, n),
              equals(rawOf("result"), name("x")), std::move(lit));
       std::string head = unwrapName(*under);
       NodePtr raw;
       if (!head.empty())
         raw =
             fn(head + "#of", makeNode(NodeKind::TypeName, at, n),
                clone(*under), equals(name("result"), rawOf("x")), rawOf("x"));
       out.push_back(std::move(item));
       out.push_back(std::move(make));
       if (raw) {
         unwrapHeads_.insert(head);
         out.push_back(std::move(raw));
       }
     }
     program_.kids = std::move(out);
   }

   // The name that unwraps a distinct type over `t` when applied: `u32` for
   // u32, `byte` for an alias, `int` for `int{0..100}`, `option` for
   // `option u8`. Empty for a type no name can be applied for, such as an
   // array.
   static std::string unwrapName(const Node &t) {
     if (t.kind == NodeKind::TypeName || t.kind == NodeKind::RangeType)
       return t.text;
     if (t.kind == NodeKind::TypeApp && !t.kids.empty() &&
         t.kids[0]->kind == NodeKind::TypeName)
       return t.kids[0]->text;
     return "";
   }

   // `length 5` and `u32 l`: a type applied to one value converts it
   // (ADR 0064, section 2). Both are calls of `<type>#of`, whose overloads
   // are told apart by their argument's type: with `let pixels = type
   // length`, `length#of` takes a u32 and makes a length, or takes a pixels
   // and unwraps it.
   void convertCalls() {
     if (distinct_.empty())
       return;
     std::function<void(Node &)> walk = [&](Node &e) {
       for (NodePtr &k : e.kids)
         walk(*k);
       if (e.kind != NodeKind::Apply || e.kids.size() != 2 ||
           e.kids[0]->kind != NodeKind::Name || !e.kids[0]->flags.empty())
         return;
       std::string &head = e.kids[0]->text;
       if (arrowTypes_.count(head)) {
         // `op succ` is the record `{ raw#op = succ }`.
         auto init = makeNode(NodeKind::FieldInit, e.loc, "raw#" + head);
         init->add(std::move(e.kids[1]));
         e.kind = NodeKind::RecordLit;
         e.text.clear();
         e.kids.clear();
         e.add(std::move(init));
         return;
       }
       if (distinct_.count(head) || unwrapHeads_.count(head))
         head += "#of";
     };
     for (NodePtr &item : program_.kids)
       if (!isMetaItem(*item))
         walk(*item);
   }

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
      // `@lower(gen args)` computes the function's MLIR (ADR 0065, step 2).
      if (item->kind == NodeKind::LetItem)
        changed |= runLowering(*item);
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

  // `@lower(gen args)` on a function runs the metaprogram `gen` on the
  // arguments, and the string it returns becomes the attribute's MLIR, as
  // if written there (ADR 0065, step 2). In the arguments, the function's
  // parameters stand for themselves, as names, as in a tactic's. So a
  // lowering can depend on a shape, an element type or a target that its
  // author passes. `@lower("text")` is left as it is; IRGen checks both
  // the same way, and the MLIR is parsed before anything is proved.
  bool runLowering(Node &item) {
    if (item.kids.size() < 4 || item.kids[1]->kind != NodeKind::RetAnnot ||
        item.kids[1]->kids.size() < 2)
      return false;
    Node &attrs = *item.kids[1]->kids[1];
    Node *lower = nullptr;
    for (NodePtr &a : attrs.kids)
      if (a->text == "lower")
        lower = a.get();
    if (!lower || lower->kids.size() != 1)
      return false;
    const Node &e = *lower->kids[0];
    const Node &head = e.kind == NodeKind::Apply ? *e.kids[0] : e;
    // A string, or anything that is not a metaprogram's call, is for IRGen
    // to accept or explain.
    if (head.kind != NodeKind::Name || !interp_.isMeta(head.text))
      return false;
    std::string who = "the metaprogram '" + head.text + "'";
    std::vector<std::pair<std::string, ValuePtr>> bindings;
    for (const NodePtr &p : item.kids[0]->kids)
      if (p->kind == NodeKind::Param)
        bindings.emplace_back(p->text, Interpreter::syntaxValue(makeNode(
                                           NodeKind::Name, p->loc, p->text)));
    ValuePtr v;
    try {
      interp_.setSite(lower->loc);
      v = interp_.evalWith(e, bindings);
      produced(head.text, lower->loc);
    } catch (const Deferred &d) {
      diags_.error(lower->loc, who + " needs the type '" + d.type + "'");
      lower->kids.clear();
      return true;
    } catch (const MetaError &err) {
      diags_.error(err.loc, who + " failed: " + err.message);
      lower->kids.clear();
      return true;
    }
    if (v->kind != Value::Kind::Str) {
      diags_.error(lower->loc, "@lower(" + head.text +
                                   " ...) must compute a string of "
                                   "MLIR, but " +
                                   who + " returned " +
                                   Interpreter::kindName(v->kind));
      lower->kids.clear();
      return true;
    }
    // The string as a literal's spelling, which IRGen decodes.
    std::string spelling = "\"";
    for (char c : v->s) {
      if (c == '\n')
        spelling += "\\n";
      else if (c == '\t')
        spelling += "\\t";
      else if (c == '"' || c == '\\')
        spelling += std::string("\\") + c;
      else
        spelling += c;
    }
    spelling += "\"";
    lower->kids[0] = makeNode(NodeKind::StringLit, lower->loc, spelling);
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
      // A recursive variant's payload is in its cycle, and `rec` too
      // (ADR 0047).
      rec->flags = item.flags.find("rec") != std::string::npos ? "rec payload"
                                                               : "payload";
      rec->add(makeNode(NodeKind::Params, c->loc));
      rec->add(makeNode(NodeKind::None, c->loc));
      rec->add(makeNode(NodeKind::Contracts, c->loc));
      auto value = makeNode(NodeKind::TypeValue, c->loc);
      value->add(std::move(c->kids[0]));
      // The record derives what its variant derives, so a variant's
      // codec can build on its payloads' (ADR 0045, step 5).
      auto attrs = makeNode(NodeKind::Attrs, c->loc);
      for (const NodePtr &a : item.kids[3]->kids[1]->kids)
        if (a->text == "derive") attrs->add(clone(*a));
      value->add(std::move(attrs));
      value->add(makeNode(NodeKind::None, c->loc));
      rec->add(std::move(value));
      c->kids[0] = makeNode(NodeKind::TypeName, c->loc, name);
      payloadOf_[name] = item.text;
      lifted_[name] = rec.get();
      types_.insert(name);
      // The variant's derives, later in this pass, read it.
      interp_.addToListing(rec.get());
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
        // A derive of the program's own, or one an imported interface
        // exports, as Pia.Text.Json.Derive's derive_json (ADR 0039).
        if (!interp_.isMeta(fn)) {
          std::vector<std::string> found = interp_.importedMetas(fn);
          if (found.size() > 1) {
            std::string names;
            for (const std::string &f : found) names += (names.empty() ? "'" : ", '") + f + "'";
            diags_.error(arg->loc, "more than one imported metaprogram is '" + fn +
                                       "' for " + what + ": " + names);
            continue;
          }
          if (found.empty()) {
            diags_.error(arg->loc, "there is no metaprogram '" + fn + "' for " +
                                       what);
            continue;
          }
          fn = found[0];
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
  // Whether a type item derives anything: an @derive left, or one run.
  bool derives(const Node &item) {
    for (const NodePtr &a : item.kids[3]->kids[1]->kids)
      if (a->text == "derive") return true;
    return !derived_[item.text].empty();
  }

  bool settleAttrs(Node &item) {
    std::set<std::string> pending;
    for (const NodePtr &attr : item.kids[3]->kids[1]->kids)
      if (attr->text == "derive")
        for (const NodePtr &arg : attr->kids) pending.insert(arg->text);
    // A lifted payload record that derives nothing of its own has
    // attributes for its variant's derives, which settle them with the
    // variant's own; one that derives settles them itself.
    if (payloadOf_.count(item.text) && pending.empty() &&
        derived_[item.text].empty())
      return false;
    const std::set<std::string> &done = derived_[item.text];
    bool changed = false;
    auto settle = [&](Node &attrs, const std::string *member,
                      const std::string &owner) {
      std::vector<NodePtr> kept;
      for (NodePtr &a : attrs.kids) {
        if (a->text == "derive" || pending.count(a->text)) {
          kept.push_back(std::move(a));
        } else if (done.count(a->text)) {
          // Another type's derive may still read it, as a variant's
          // reads its record payload's member names, so it is kept
          // aside where field_attrs and ctor_attrs find it.
          if (member)
            interp_.settleAttr(owner, *member, std::move(a));
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
    settle(*item.kids[3]->kids[1], nullptr, item.text);
    Node &body = *item.kids[3]->kids[0];
    if (body.kind == NodeKind::RecordType || body.kind == NodeKind::Variants)
      for (NodePtr &m : body.kids)
        for (NodePtr &k : m->kids)
          if (k->kind == NodeKind::Attrs)
            settle(*k, &m->text, item.text);
    if (body.kind == NodeKind::Variants)
      for (NodePtr &c : body.kids)
        if (auto r = lifted_.find(item.text + "_" + c->text);
            r != lifted_.end() && !derives(*r->second))
          for (NodePtr &f : r->second->kids[3]->kids[0]->kids)
            for (NodePtr &k : f->kids)
              if (k->kind == NodeKind::Attrs)
                settle(*k, &f->text, r->second->text);
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
  // The distinct types made so far, each with its underlying type, and
  // the names that unwrap one (makeDistinct).
  std::map<std::string, NodePtr> distinct_;
  std::set<std::string> unwrapHeads_;
  std::set<std::string> arrowTypes_; // distinct arrow types
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

// --- frame lemmas (ADR 0060, section 3) -----------------------------------

// `f'frame`, the frame lemma of a spec function `f` that says
// `reads xs.[a .. b]`: for xs and xs' that agree on xs.[a .. b], f gives the
// same result. It is proved by induction on f's own `decreases`: its body
// follows f's, calling itself where f calls f, and asserting that each
// element f reads is in the footprint.
namespace frames {

NodePtr name(const std::string &n, SourceLoc l) {
  return makeNode(NodeKind::Name, l, n);
}

NodePtr binary(const std::string &op, NodePtr a, NodePtr b, SourceLoc l) {
  NodePtr n = makeNode(NodeKind::Binary, l, op);
  n->add(std::move(a));
  n->add(std::move(b));
  return n;
}

NodePtr apply(NodePtr f, std::vector<NodePtr> args, SourceLoc l) {
  NodePtr n = makeNode(NodeKind::Apply, l);
  n->add(std::move(f));
  for (NodePtr &a : args)
    n->add(std::move(a));
  return n;
}

// A copy of `n` with the name `from` renamed `to`.
NodePtr renamed(const Node &n, const std::string &from, const std::string &to) {
  NodePtr c = clone(n);
  std::function<void(Node &)> walk = [&](Node &m) {
    if (m.kind == NodeKind::Name && m.text == from)
      m.text = to;
    for (NodePtr &k : m.kids)
      if (k)
        walk(*k);
  };
  walk(*c);
  return c;
}

NodePtr sequence(std::vector<NodePtr> stmts, SourceLoc l) {
  NodePtr tail = makeNode(NodeKind::Unit, l);
  for (auto it = stmts.rbegin(); it != stmts.rend(); ++it) {
    NodePtr s = makeNode(NodeKind::Sequence, l);
    s->add(std::move(*it));
    s->add(std::move(tail));
    tail = std::move(s);
  }
  return tail;
}

struct Builder {
  const Node &fn;
  std::string xs, ys, lemma;
  size_t at; // xs's position among the parameters
  Diagnostics &diags;
  bool ok = true;

  // The lemma calls and element assertions for `e`, an expression of f's
  // body that is not an `if`.
  void collect(const Node &e, std::vector<NodePtr> &out) {
    if (e.kind == NodeKind::Apply && e.kids[0]->kind == NodeKind::Name &&
        e.kids[0]->text == fn.text) {
      std::vector<NodePtr> args;
      for (size_t k = 1; k < e.kids.size(); ++k) {
        args.push_back(clone(*e.kids[k]));
        if (k - 1 == at) {
          if (e.kids[k]->kind != NodeKind::Name || e.kids[k]->text != xs) {
            diags.error(e.kids[k]->loc,
                        "a spec function that says what it reads must pass '" +
                            xs + "' itself to its recursive calls");
            ok = false;
          }
          args.push_back(name(ys, e.loc));
        }
      }
      out.push_back(apply(name(lemma, e.loc), std::move(args), e.loc));
      for (size_t k = 1; k < e.kids.size(); ++k)
        collect(*e.kids[k], out);
      return;
    }
    // An `if` inside an expression guards what its branches read.
    if (e.kind == NodeKind::If && e.kids.size() >= 3 && e.kids[2] &&
        e.kids[2]->kind != NodeKind::None) {
      std::vector<NodePtr> a, b;
      collect(*e.kids[1], a);
      collect(*e.kids[2], b);
      collect(*e.kids[0], out);
      if (a.empty() && b.empty())
        return;
      NodePtr n = makeNode(NodeKind::If, e.loc);
      n->add(clone(*e.kids[0]));
      n->add(sequence(std::move(a), e.loc));
      n->add(sequence(std::move(b), e.loc));
      out.push_back(std::move(n));
      return;
    }
    if (e.kind == NodeKind::Index && e.kids[0]->kind == NodeKind::Name &&
        e.kids[0]->text == xs && e.kids[1]->kind != NodeKind::Range) {
      NodePtr a = makeNode(NodeKind::Assert, e.loc);
      NodePtr l = makeNode(NodeKind::Index, e.loc);
      l->add(name(ys, e.loc));
      l->add(clone(*e.kids[1]));
      a->add(binary("=", std::move(l), clone(e), e.loc));
      out.push_back(std::move(a));
    }
    for (const NodePtr &k : e.kids)
      if (k)
        collect(*k, out);
  }

  NodePtr body(const Node &e) {
    if (e.kind == NodeKind::If && e.kids.size() >= 3 && e.kids[2] &&
        e.kids[2]->kind != NodeKind::None) {
      NodePtr n = makeNode(NodeKind::If, e.loc);
      n->add(clone(*e.kids[0]));
      n->add(body(*e.kids[1]));
      n->add(body(*e.kids[2]));
      return n;
    }
    std::vector<NodePtr> stmts;
    collect(e, stmts);
    return sequence(std::move(stmts), e.loc);
  }
};

} // namespace frames

void addFrameLemmas(Node &program, Diagnostics &diags) {
  using namespace frames;
  for (size_t i = 0; i < program.kids.size(); ++i) {
    const Node &fn = *program.kids[i];
    if (fn.kind != NodeKind::LetItem || fn.kids.size() < 4)
      continue;
    if (fn.flags.find("spec") == std::string::npos)
      continue;
    const Node &params = *fn.kids[0], &ret = *fn.kids[1];
    const Node &contracts = *fn.kids[2], &value = *fn.kids[3];
    const Node *reads = nullptr, *measure = nullptr;
    for (const NodePtr &c : contracts.kids) {
      if (c->kind == NodeKind::Reads)
        reads = c.get();
      if (c->kind == NodeKind::Decreases)
        measure = c.get();
    }
    if (!reads)
      continue;
    const Node &view = *reads->kids[0];
    bool byOwner = reads->kids.size() == 2;
    if (view.kind != NodeKind::Index || view.kids[0]->kind != NodeKind::Name ||
        (!byOwner && view.kids[1]->kind != NodeKind::Range) ||
        (byOwner && view.kids[1]->kind != NodeKind::Name))
      continue; // IRGen reports it
    Builder b{fn,
              view.kids[0]->text,
              view.kids[0]->text + "'",
              fn.text + "'frame",
              0,
              diags};
    bool found = false;
    for (size_t k = 0; k < params.kids.size(); ++k)
      if (params.kids[k]->text == b.xs)
        b.at = k, found = true;
    if (!found)
      continue; // IRGen reports it
    SourceLoc l = reads->loc;
    NodePtr item = makeNode(NodeKind::LetItem, l, b.lemma);
    item->flags = "lemma";
    NodePtr ps = makeNode(NodeKind::Params, params.loc);
    for (size_t k = 0; k < params.kids.size(); ++k) {
      ps->add(clone(*params.kids[k]));
      if (k == b.at) {
        NodePtr p = clone(*params.kids[k]);
        p->text = b.ys;
        ps->add(std::move(p));
      }
    }
    item->add(std::move(ps));
    NodePtr r = makeNode(NodeKind::RetAnnot, ret.loc);
    NodePtr annot = makeNode(NodeKind::Annot, ret.loc);
    annot->add(makeNode(NodeKind::Modifiers, ret.loc));
    annot->add(makeNode(NodeKind::TypeName, ret.loc, "unit"));
    annot->add(makeNode(NodeKind::None, ret.loc));
    r->add(std::move(annot));
    r->add(makeNode(NodeKind::Attrs, ret.loc));
    item->add(std::move(r));
    NodePtr cs = makeNode(NodeKind::Contracts, contracts.loc);
    for (const NodePtr &c : contracts.kids)
      if (c->kind == NodeKind::Requires) {
        cs->add(clone(*c));
        cs->add(renamed(*c, b.xs, b.ys));
      }
    auto lenOf = [&](const std::string &x) {
      std::vector<NodePtr> a;
      a.push_back(name(x, l));
      return apply(name("len", l), std::move(a), l);
    };
    NodePtr sameLen = makeNode(NodeKind::Requires, l);
    sameLen->add(binary("=", lenOf(b.ys), lenOf(b.xs), l));
    cs->add(std::move(sameLen));
    // forall (c in a .. b). xs'.[c] = xs.[c], or with an owner,
    // forall (c in 0 .. len xs). owner.[c] = v ==> xs'.[c] = xs.[c]
    std::string c = "c'frame";
    NodePtr q = makeNode(NodeKind::Quantifier, l, "forall");
    NodePtr binder = makeNode(NodeKind::RangeBinder, l, c);
    if (byOwner) {
      NodePtr r = makeNode(NodeKind::Range, l);
      r->add(makeNode(NodeKind::IntLit, l, "0"));
      r->add(lenOf(b.xs));
      binder->add(std::move(r));
    } else {
      binder->add(clone(*view.kids[1]));
    }
    q->add(std::move(binder));
    NodePtr lhs = makeNode(NodeKind::Index, l);
    lhs->add(name(b.ys, l));
    lhs->add(name(c, l));
    NodePtr rhs = makeNode(NodeKind::Index, l);
    rhs->add(name(b.xs, l));
    rhs->add(name(c, l));
    NodePtr agreeAt = binary("=", std::move(lhs), std::move(rhs), l);
    if (byOwner)
      agreeAt = binary("==>", renamed(*reads->kids[1], view.kids[1]->text, c),
                       std::move(agreeAt), l);
    q->add(std::move(agreeAt));
    NodePtr agree = makeNode(NodeKind::Requires, l);
    agree->add(std::move(q));
    cs->add(std::move(agree));
    auto call = [&](const std::string &x) {
      std::vector<NodePtr> a;
      for (const NodePtr &p : params.kids)
        a.push_back(name(p->text == b.xs ? x : p->text, l));
      return apply(name(fn.text, l), std::move(a), l);
    };
    NodePtr same = makeNode(NodeKind::Ensures, l);
    same->add(binary("=", call(b.ys), call(b.xs), l));
    cs->add(std::move(same));
    if (measure)
      cs->add(clone(*measure));
    item->add(std::move(cs));
    item->add(b.body(value));
    if (!b.ok)
      continue;
    program.kids.insert(program.kids.begin() + i + 1, std::move(item));
    ++i;
  }
}

bool expand(Node &program, Diagnostics &diags, const Options &options) {
  size_t before = diags.errors().size();
  Expander(program, diags, options).run();
  if (diags.errors().size() == before)
    addFrameLemmas(program, diags);
  return diags.errors().size() == before;
}

}  // namespace pia::meta
