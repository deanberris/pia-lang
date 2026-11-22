#include "irgen/Theories.h"

#include <functional>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "sema/Sema.h"

namespace pia::irgen {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

namespace {

struct Theory {
  std::string name;
  std::set<std::string> members;
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
                                                 "' in the theory '" + t.name +
                                                 "'"));
  if ((n.kind == NodeKind::Name && n.flags.empty()) ||
      n.kind == NodeKind::TypeName)
    if (t.members.count(n.text)) n.text = t.name + "." + n.text;
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
      n.text = it->first + "." + n.text;
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
    if (item->kind == NodeKind::Theory || item->kind == NodeKind::FileAttr)
      return true;
  return false;
}

void flattenTheories(Node &program, syntax::Diagnostics &diags) {
  bool trusted = false;
  std::set<std::string> topLevel;
  std::map<std::string, Theory> theories;
  for (const NodePtr &item : program.kids) {
    if (item->kind == NodeKind::FileAttr) {
      if (item->text == "trusted")
        trusted = true;
      else
        diags.error(item->loc, "only '@trusted' can mark a whole file; "
                               "@" + item->text + " is not a file attribute");
      continue;
    }
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

  // A member's name is visible inside its theory, so it may not shadow a
  // name visible there: another item, a builtin or a builtin type.
  for (const NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Theory) continue;
    const Theory &t = theories.at(item->text);
    for (const NodePtr &m : item->kids) {
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
    if (axioms && !trusted)
      diags.error(item->loc,
                  "the theory '" + t.name + "' has axioms and no model, so its "
                  "axioms are trusted: mark the file '@trusted' on a line of "
                  "its own (models, which make a theory proved, come in ADR "
                  "0036 step 3)");
  }
  if (diags.hasErrors()) return;

  std::vector<NodePtr> out;
  for (NodePtr &item : program.kids) {
    if (item->kind == NodeKind::FileAttr) continue;
    // `import T` of a theory in this program needs nothing: there are no
    // modules yet, so its names are already here.
    if (item->kind == NodeKind::Import && theories.count(item->text)) continue;
    if (item->kind != NodeKind::Theory) {
      out.push_back(std::move(item));
      continue;
    }
    const Theory &t = theories.at(item->text);
    for (NodePtr &m : item->kids) {
      if (m->kind == NodeKind::SortItem) {
        // `let T.s = type <t>`, or `#sort` for a new uninterpreted sort.
        auto ti = syntax::makeNode(NodeKind::LetItem, m->loc, m->text);
        ti->flags = "sort";
        ti->add(syntax::makeNode(NodeKind::Params, m->loc));
        ti->add(syntax::makeNode(NodeKind::None, m->loc));
        ti->add(syntax::makeNode(NodeKind::Contracts, m->loc));
        auto tv = syntax::makeNode(NodeKind::TypeValue, m->loc);
        if (!m->kids.empty())
          tv->add(std::move(m->kids[0]));
        else
          tv->add(syntax::makeNode(NodeKind::TypeName, m->loc, "#sort"));
        tv->add(syntax::makeNode(NodeKind::Attrs, m->loc));
        ti->add(std::move(tv));
        m = std::move(ti);
      } else if (hasFlag(*m, "abstract")) {
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
      out.push_back(std::move(m));
    }
  }
  program.kids = std::move(out);
  for (NodePtr &item : program.kids) resolveQualified(*item, theories, diags);
}

}  // namespace pia::irgen
