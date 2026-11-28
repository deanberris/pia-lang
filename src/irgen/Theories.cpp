#include "irgen/Theories.h"

#include <functional>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "llvm/ADT/StringRef.h"
#include "sema/Sema.h"

namespace pia::irgen {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

namespace {

struct Theory {
  std::string name;
  std::set<std::string> members;
  const char *kind = "theory";  // or "model", for messages
  std::set<std::string> sorts, abstracts;  // a theory's
  std::vector<NodePtr> axioms;  // qualified copies, for the model check
};

std::string shadowMessage(const std::string &name, const std::string &what) {
  return "'" + name + "' shadows " + what +
         "; Pia does not allow shadowing (ADR 0022), so rename it to " +
         name + "'";
}

// `let spec f : (a : t) -> (b : u) -> r` as `let spec f (a : t) (b : u) : r`.
bool unfoldArrow(Node &item, syntax::Diagnostics &diags) {
  Node &ret = *item.kids[1];
  if (ret.kind != NodeKind::RetAnnot || ret.kids.empty() ||
      ret.kids[0]->kind != NodeKind::Annot) {
    diags.error(item.loc, "the abstract spec function '" + item.text +
                              "' needs a type, as in 'let spec " + item.text +
                              " : (x : t) -> r'");
    return false;
  }
  Node &annot = *ret.kids[0];
  NodePtr type = std::move(annot.kids[1]);
  Node &params = *item.kids[0];
  while (type->kind == NodeKind::ArrowType) {
    Node &dom = *type->kids[0];
    if (dom.text.empty()) {
      diags.error(dom.loc, "an abstract spec function names its parameters, "
                           "as in '(x : t) -> r'");
      return false;
    }
    auto param = syntax::makeNode(NodeKind::Param, dom.loc, dom.text);
    auto pa = syntax::makeNode(NodeKind::Annot, dom.loc);
    for (NodePtr &k : dom.kids) pa->add(std::move(k));
    param->add(std::move(pa));
    params.add(std::move(param));
    NodePtr rest = std::move(type->kids[1]);
    type = std::move(rest);
  }
  annot.kids[1] = std::move(type);
  return true;
}

// Names the theory's members by their qualified names inside its items,
// and reports a parameter or binder that would shadow one.
void qualify(Node &n, const Theory &t, syntax::Diagnostics &diags) {
  bool binds = n.kind == NodeKind::Param || n.kind == NodeKind::Binder ||
               n.kind == NodeKind::RangeBinder || n.kind == NodeKind::LetIn;
  if (binds && t.members.count(n.text))
    diags.error(n.loc, shadowMessage(n.text, "'" + t.name + "." + n.text +
                                                 "' in the " + t.kind + " '" +
                                                 t.name + "'"));
  // A name a quote left free is marked `toplevel`; inside a theory a
  // generator built, it still means the theory's member (ADR 0036).
  if ((n.kind == NodeKind::Name &&
       (n.flags.empty() || n.flags == "toplevel")) ||
      n.kind == NodeKind::TypeName)
    if (t.members.count(n.text)) {
      n.text = t.name + "." + n.text;
      n.flags.clear();
    }
  for (NodePtr &k : n.kids) qualify(*k, t, diags);
}

// `T.x` outside or inside a theory: a Field of the theory's name.
void resolveQualified(Node &n, const std::map<std::string, Theory> &theories,
                      syntax::Diagnostics &diags) {
  if (n.kind == NodeKind::Field && n.kids.size() == 1 &&
      n.kids[0]->kind == NodeKind::Name && n.kids[0]->flags.empty()) {
    auto it = theories.find(n.kids[0]->text);
    if (it != theories.end()) {
      if (!it->second.members.count(n.text))
        diags.error(n.loc, "the theory '" + it->first + "' has no '" +
                               n.text + "'");
      n.kind = NodeKind::Name;
      n.text = it->second.name + "." + n.text;  // an alias's target
      n.kids.clear();
      return;
    }
  }
  if (n.kind == NodeKind::TypeName) {
    size_t dot = n.text.find('.');
    if (dot != std::string::npos) {
      auto it = theories.find(n.text.substr(0, dot));
      std::string member = n.text.substr(dot + 1);
      if (it != theories.end() && !it->second.members.count(member))
        diags.error(n.loc, "the theory '" + it->first + "' has no '" +
                               member + "'");
      else if (it != theories.end())
        n.text = it->second.name + "." + member;  // an alias's target
    }
  }
  for (NodePtr &k : n.kids) resolveQualified(*k, theories, diags);
}

bool hasFlag(const Node &item, const std::string &flag) {
  size_t pos = 0;
  const std::string &f = item.flags;
  while (pos <= f.size()) {
    size_t end = f.find(' ', pos);
    if (end == std::string::npos) end = f.size();
    if (f.compare(pos, end - pos, flag) == 0) return true;
    pos = end + 1;
  }
  return false;
}

}  // namespace

bool hasTheories(const Node &program) {
  for (const NodePtr &item : program.kids)
    if (item->kind == NodeKind::Theory || item->kind == NodeKind::FileAttr ||
        item->kind == NodeKind::Model)
      return true;
  return false;
}

bool isTrustedFile(const Node &program) {
  for (const NodePtr &item : program.kids) {
    if (item->kind == NodeKind::ModuleHeader && !item->kids.empty())
      for (const NodePtr &a : item->kids[0]->kids)
        if (a->text == "trusted") return true;
    if (item->kind == NodeKind::FileAttr && item->text == "trusted")
      return true;
  }
  return false;
}

namespace {

// `let s = type <t>`, the type item a sort becomes; `#sort` for a new
// uninterpreted one.
NodePtr sortItem(Node &sort, const std::string &name, bool abstract) {
  auto ti = syntax::makeNode(NodeKind::LetItem, sort.loc, name);
  ti->flags = abstract ? "sort" : "";
  ti->add(syntax::makeNode(NodeKind::Params, sort.loc));
  ti->add(syntax::makeNode(NodeKind::None, sort.loc));
  ti->add(syntax::makeNode(NodeKind::Contracts, sort.loc));
  auto tv = syntax::makeNode(NodeKind::TypeValue, sort.loc);
  if (!sort.kids.empty())
    tv->add(std::move(sort.kids[0]));
  else
    tv->add(syntax::makeNode(NodeKind::TypeName, sort.loc, "#sort"));
  tv->add(syntax::makeNode(NodeKind::Attrs, sort.loc));
  ti->add(std::move(tv));
  return ti;
}

// In an axiom of T, each sort and abstract function of T as the model's.
void substitute(Node &n, const Theory &t, const std::string &model) {
  if ((n.kind == NodeKind::TypeName && t.sorts.count(n.text)) ||
      (n.kind == NodeKind::Name && n.flags.empty() && t.abstracts.count(n.text)))
    n.text = model + n.text.substr(t.name.size());
  for (NodePtr &k : n.kids) substitute(*k, t, model);
}

}  // namespace

void flattenTheories(Node &program, syntax::Diagnostics &diags,
                     TheoryInfo *info) {
  bool trusted = isTrustedFile(program);
  std::set<std::string> topLevel;
  std::map<std::string, Theory> theories;
  for (const NodePtr &item : program.kids) {
    if (item->kind == NodeKind::FileAttr) {
      if (item->text != "trusted")
        diags.error(item->loc, "only '@trusted' can mark a whole file; "
                               "@" + item->text + " is not a file attribute");
      continue;
    }
    if (item->kind == NodeKind::Theory && item->flags == "alias") continue;
    if (item->kind == NodeKind::Theory) {
      if (theories.count(item->text) || topLevel.count(item->text))
        diags.error(item->loc, "'" + item->text + "' is already defined");
      Theory t;
      t.name = item->text;
      for (const NodePtr &m : item->kids) {
        if (!t.members.insert(m->text).second)
          diags.error(m->loc, "'" + m->text + "' is already declared in the "
                              "theory '" + t.name + "'");
      }
      theories[t.name] = std::move(t);
      continue;
    }
    if (!item->text.empty() && item->kind != NodeKind::Import)
      topLevel.insert(item->text);
  }
  // `let theory U = gen args` with the arguments of an earlier `let theory
  // T`: U is another name for T (ADR 0036, one theory per argument tuple).
  for (const NodePtr &item : program.kids)
    if (item->kind == NodeKind::Theory && item->flags == "alias") {
      auto target = theories.find(item->kids[0]->text);
      if (target == theories.end()) continue;
      if (theories.count(item->text) || topLevel.count(item->text)) {
        diags.error(item->loc, "'" + item->text + "' is already defined");
        continue;
      }
      Theory alias;
      alias.name = target->second.name;
      alias.members = target->second.members;
      theories[item->text] = std::move(alias);
    }
  // A theory with a model in this program is proved consistent by it, so
  // its axioms are not trusted (ADR 0036, "Modelled").
  std::set<std::string> modelled;
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Model) continue;
    const std::string &theory = item->kids[0]->text;
    if (!theories.count(theory)) {
      diags.error(item->kids[0]->loc, "'" + theory + "' is not a theory in "
                                      "this program");
      continue;
    }
    modelled.insert(theory);
  }

  // A member's name is visible inside its theory, so it may not shadow a
  // name visible there: another item, a builtin or a builtin type.
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Theory || item->flags == "alias") continue;
    const Theory &t = theories.at(item->text);
    // The built-in `Target` (ADR 0049) is the compiler's, and a program
    // only ever names its members qualified, so a program's own
    // `page_size` does not clash with it.
    bool builtin = item->flags == "builtin";
    // An imported theory (ADR 0088) is named only qualified, as `M.T.x`,
    // and its exporter proved its model or trusted it.
    bool imported = hasFlag(*item, "imported");
    if (imported && info && hasFlag(*item, "proved"))
      info->importModelled.insert(t.name);
    if (imported && info && hasFlag(*item, "trusting"))
      info->trusting.emplace_back(t.name, item->loc);
    for (const NodePtr &m : item->kids) {
      if (builtin || imported)
        break;
      std::string what;
      if (topLevel.count(m->text) || theories.count(m->text))
        what = "the item '" + m->text + "'";
      else if (sema::isCoreBuiltin(m->text))
        what = "a core builtin";
      else if (sema::isBuiltinTypeName(m->text))
        what = "the type '" + m->text + "'";
      if (!what.empty()) diags.error(m->loc, shadowMessage(m->text, what));
    }
    bool axioms = false;
    for (const NodePtr &m : item->kids)
      if (m->kind == NodeKind::LetItem && hasFlag(*m, "axiom")) axioms = true;
    // A box's theory (ADR 0046) is justified by the use check at `widen`.
    bool box = hasFlag(*item, "box");
    if (box && hasFlag(*item, "modelled") && info)
      info->boxModelled.insert(t.name);
    if (axioms && !trusted && !modelled.count(t.name) && !box && !imported)
      diags.error(item->loc,
                  "the theory '" + t.name + "' has axioms and no model, so its "
                  "axioms are trusted: give it a model, 'let model m : " +
                  t.name + " = struct ... end', or mark the file '@trusted' "
                  "on a line of its own");
  }
  if (diags.hasErrors()) return;

  std::vector<NodePtr> out;
  std::vector<NodePtr> models;
  for (NodePtr &item : program.kids) {
    if (item->kind == NodeKind::FileAttr) continue;
    if (item->kind == NodeKind::Theory && item->flags == "alias") continue;
    // `import T` of a theory in this program needs nothing: there are no
    // modules yet, so its names are already here.
    if (item->kind == NodeKind::Import && theories.count(item->text)) {
      // `import T trusting` grants trust in T's axioms (ADR 0036). In the
      // module that declares T it changes nothing, since T is trusted
      // there already; the grant is recorded for --trust-report.
      if (info && item->flags == "trusting")
        info->trusting.emplace_back(item->text, item->loc);
      continue;
    }
    if (item->kind != NodeKind::Theory && item->kind != NodeKind::Model) {
      out.push_back(std::move(item));
      continue;
    }
    if (item->kind == NodeKind::Model) {
      models.push_back(std::move(item));
      continue;
    }
    Theory &t = theories.at(item->text);
    for (NodePtr &m : item->kids) {
      if (m->kind == NodeKind::SortItem) {
        // Only a new sort is the model's to choose; an abbreviation is
        // already a type.
        if (m->kids.empty()) t.sorts.insert(t.name + "." + m->text);
        m = sortItem(*m, m->text, m->kids.empty());
      } else if (hasFlag(*m, "abstract")) {
        t.abstracts.insert(t.name + "." + m->text);
        if (!unfoldArrow(*m, diags)) continue;
      } else if (hasFlag(*m, "axiom") && hasFlag(*m, "rec")) {
        diags.error(m->loc, "an axiom is not recursive");
      } else if (!hasFlag(*m, "spec") && !hasFlag(*m, "lemma") &&
                 !hasFlag(*m, "axiom")) {
        diags.error(m->loc, "a theory holds sorts, spec functions, axioms "
                            "and lemmas; '" + m->text + "' is none of these");
      }
      qualify(*m, t, diags);
      m->text = t.name + "." + m->text;
      m->flags += m->flags.empty() ? "theory" : " theory";
      if (hasFlag(*m, "axiom")) t.axioms.push_back(syntax::clone(*m));
      out.push_back(std::move(m));
    }
  }
  // Once every theory is known: each model's sorts and functions become
  // `m.x`, and each axiom of its theory, with them in place of the
  // theory's, becomes a lemma the model must prove (ADR 0036).
  for (NodePtr &model : models) {
    Theory &t = theories.at(model->kids[0]->text);
    Theory scope;
    scope.name = model->text;
    scope.kind = "model";
    for (size_t i = 1; i < model->kids.size(); ++i)
      scope.members.insert(model->kids[i]->text);
    std::set<std::string> defined;
    for (size_t i = 1; i < model->kids.size(); ++i) {
      NodePtr &m = model->kids[i];
      std::string qualified = t.name + "." + m->text;
      if (!defined.insert(qualified).second)
        diags.error(m->loc, "'" + m->text + "' is already defined in the "
                            "model '" + model->text + "'");
      if (m->kind == NodeKind::SortItem) {
        if (!t.sorts.count(qualified))
          diags.error(m->loc, "the theory '" + t.name + "' has no sort '" +
                                  m->text + "' for the model to define");
        m = sortItem(*m, m->text, false);
      } else if (!t.abstracts.count(qualified)) {
        diags.error(m->loc, "the theory '" + t.name + "' has no abstract "
                            "function '" + m->text + "' for the model to "
                            "define");
      } else if (!hasFlag(*m, "spec") || hasFlag(*m, "abstract") ||
                 m->kids[3]->kind == NodeKind::None) {
        diags.error(m->loc, "a model defines '" + m->text + "' as a spec "
                            "function with a body, 'let spec " + m->text +
                            " ... = ...'");
      }
      qualify(*m, scope, diags);
      m->text = model->text + "." + m->text;
      m->flags += m->flags.empty() ? "model" : " model";
      if (info) info->modelOf[m->text] = model->text;
      out.push_back(std::move(m));
    }
    for (const std::string &need : t.sorts)
      if (!defined.count(need))
        diags.error(model->loc, "the model '" + model->text + "' does not "
                                "define the sort '" + need + "'");
    for (const std::string &need : t.abstracts)
      if (!defined.count(need))
        diags.error(model->loc, "the model '" + model->text + "' does not "
                                "define '" + need + "'");
    // A built-in model is proved to meet the axioms once, when the
    // compiler is tested (tests/verify/target_theory.pia), not again in
    // every program that uses it.
    bool builtin = model->flags == "builtin";
    for (const NodePtr &axiom : t.axioms) {
      if (builtin)
        break;
      NodePtr lemma = syntax::clone(*axiom);
      substitute(*lemma, t, model->text);
      std::string name = model->text + axiom->text.substr(t.name.size());
      lemma->text = name;
      lemma->flags = "lemma model";
      // `: unit`, with no @trigger: a lemma, proved over the model.
      auto ret = syntax::makeNode(NodeKind::RetAnnot, axiom->loc);
      auto annot = syntax::makeNode(NodeKind::Annot, axiom->loc);
      annot->add(syntax::makeNode(NodeKind::Modifiers, axiom->loc));
      annot->add(syntax::makeNode(NodeKind::TypeName, axiom->loc, "unit"));
      annot->add(syntax::makeNode(NodeKind::None, axiom->loc));
      ret->add(std::move(annot));
      ret->add(syntax::makeNode(NodeKind::Attrs, axiom->loc));
      lemma->kids[1] = std::move(ret);
      lemma->kids[3] = syntax::makeNode(NodeKind::Unit, axiom->loc);
      if (info) {
        info->obligations[name] = {model->text, axiom->text};
        info->modelOf[name] = model->text;
      }
      out.push_back(std::move(lemma));
    }
    if (info) info->modelled[t.name] = model->text;
  }
  program.kids = std::move(out);
  for (NodePtr &item : program.kids) resolveQualified(*item, theories, diags);
  if (diags.hasErrors() || !info) return;

  // Witnesses: each lemma and spec function outside a theory that uses a
  // modelled theory, copied with the model's sorts and functions in place
  // of the theory's. A goal that fails over the axioms is tried there,
  // where everything is concrete: a counterexample in the model is one to
  // the axioms too, since the model meets them (ADR 0036). Copies of items
  // that use other copies call those; an item that uses a theory member a
  // model does not define, such as a theory lemma, gets no copy.
  for (const auto &[theoryName, modelName] : info->modelled) {
    const Theory &t = theories.at(theoryName);
    std::string prefix = t.name + ".";
    std::map<std::string, Node *> users;
    std::function<bool(const Node &)> mentions = [&](const Node &n) {
      if ((n.kind == NodeKind::Name || n.kind == NodeKind::TypeName) &&
          llvm::StringRef(n.text).starts_with(prefix))
        return true;
      for (const NodePtr &k : n.kids)
        if (mentions(*k)) return true;
      return false;
    };
    // Types that hold this theory's sorts, such as a record with a
    // spec-only field (ADR 0041): the witness cannot replace the sort
    // inside them, so their users get no copy.
    std::set<std::string> holders;
    std::function<bool(const Node &)> holds = [&](const Node &n) {
      if (n.kind == NodeKind::TypeName && holders.count(n.text)) return true;
      for (const NodePtr &k : n.kids)
        if (holds(*k)) return true;
      return false;
    };
    for (bool changed = true; changed;) {
      changed = false;
      for (NodePtr &item : program.kids)
        if (item->kind == NodeKind::LetItem && !item->text.empty() &&
            item->kids.size() > 3 &&
            item->kids[3]->kind == NodeKind::TypeValue &&
            !holders.count(item->text) &&
            (mentions(*item->kids[3]) || holds(*item->kids[3]))) {
          holders.insert(item->text);
          changed = true;
        }
    }
    for (NodePtr &item : program.kids) {
      if (item->kind != NodeKind::LetItem || item->text.empty() ||
          hasFlag(*item, "theory") || hasFlag(*item, "model") ||
          item->kids[3]->kind == NodeKind::None ||
          (!hasFlag(*item, "lemma") && !hasFlag(*item, "spec")))
        continue;
      if (mentions(*item)) users[item->text] = item.get();
    }
    // Drop users of what no witness can stand for, to a fixed point.
    std::function<bool(const Node &, const std::set<std::string> &)> usable =
        [&](const Node &n, const std::set<std::string> &ok) {
          if (n.kind == NodeKind::Name && n.flags.empty() &&
              llvm::StringRef(n.text).starts_with(prefix) &&
              !t.abstracts.count(n.text))
            return false;
          // Another theory's member may take or return this theory's
          // sorts, which the witness replaces: no copy for its users.
          if (n.kind == NodeKind::Name || n.kind == NodeKind::TypeName) {
            auto other = llvm::StringRef(n.text).split('.').first.str();
            if (other != t.name && theories.count(other)) return false;
          }
          if (n.kind == NodeKind::TypeName &&
              llvm::StringRef(n.text).starts_with(prefix) &&
              !t.sorts.count(n.text))
            return false;
          if (n.kind == NodeKind::TypeName && holders.count(n.text))
            return false;
          if (n.kind == NodeKind::Name && n.flags.empty() &&
              topLevel.count(n.text) && !ok.count(n.text)) {
            // a top-level function: fine unless it is a user of the theory
            // with no witness
            for (const auto &[name, node] : users)
              if (name == n.text) return false;
          }
          for (const NodePtr &k : n.kids)
            if (!usable(*k, ok)) return false;
          return true;
        };
    std::set<std::string> ok;
    for (const auto &[name, node] : users) ok.insert(name);
    for (bool changed = true; changed;) {
      changed = false;
      for (auto it = ok.begin(); it != ok.end();) {
        if (!usable(*users.at(*it), ok)) {
          it = ok.erase(it);
          changed = true;
        } else {
          ++it;
        }
      }
    }
    std::string wprefix = modelName + ".witness.";
    std::function<void(Node &)> rename = [&](Node &n) {
      if (n.kind == NodeKind::Name && n.flags.empty() && ok.count(n.text))
        n.text = wprefix + n.text;
      for (NodePtr &k : n.kids) rename(*k);
    };
    for (const std::string &name : ok) {
      NodePtr copy = syntax::clone(*users.at(name));
      substitute(*copy, t, modelName);
      rename(*copy);
      copy->text = wprefix + name;
      info->witnesses[copy->text] = name;
      info->modelOf[copy->text] = modelName;
      program.kids.push_back(std::move(copy));
    }
  }
}

}  // namespace pia::irgen
