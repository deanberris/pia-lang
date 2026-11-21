#include "meta/Expand.h"

#include <iterator>
#include <set>
#include <string>
#include <vector>

#include "meta/Interpreter.h"
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
          return isBuiltinType(t) || types_.count(t);
        }) {}

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
      if (!isMetaItem(*item)) kept.push_back(std::move(item));
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
        out.push_back(std::move(item));
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
      if (isTypeItem(*item)) changed |= runDerives(*item, generated);
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
    if (v->kind == Value::Kind::Syntax && v->syntax) {
      const Node &n = *v->syntax;
      if (n.kind == NodeKind::Program) {
        for (const NodePtr &k : n.kids) out.push_back(clone(*k));
        return true;
      }
      if (n.kind == NodeKind::LetItem) {
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

  // Runs each `@derive(x)` on a type item through `derive_x`.
  bool runDerives(Node &item, std::vector<NodePtr> &out) {
    Node &attrs = *item.kids[3]->kids[1];
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
          ValuePtr v = interp_.apply(f, {Interpreter::syntaxValue(clone(item))});
          produced(fn, attr->loc);
          takeItems(v, attr->loc, what, out);
          changed = true;
        } catch (const Deferred &d) {
          waiting_.push_back({what, d.type, arg->loc});
          keptArgs.push_back(std::move(arg));
        } catch (const MetaError &e) {
          diags_.error(e.loc, what + " failed: " + e.message);
        }
      }
      if (!keptArgs.empty()) {
        attr->kids = std::move(keptArgs);
        keptAttrs.push_back(std::move(attr));
      }
    }
    attrs.kids = std::move(keptAttrs);
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
};

}  // namespace

bool expand(Node &program, Diagnostics &diags, const Options &options) {
  size_t before = diags.errors().size();
  Expander(program, diags, options).run();
  return diags.errors().size() == before;
}

}  // namespace pia::meta
