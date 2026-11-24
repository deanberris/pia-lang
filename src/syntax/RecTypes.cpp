#include "syntax/RecTypes.h"

#include <functional>
#include <map>

namespace pia::syntax {

using N = NodeKind;

std::vector<TypeItem> typeItems(const Node &program) {
  std::vector<TypeItem> out;
  for (const NodePtr &item : program.kids) {
    if (item->kind != N::LetItem || item->kids.size() < 4 ||
        !item->kids[0]->kids.empty())
      continue;
    TypeItem t;
    t.item = item.get();
    t.rec = item->flags.find("rec") != std::string::npos;
    const Node &value = *item->kids[3];
    if (value.kind == N::TypeValue) {
      t.body = &value;
    } else if (value.kind == N::Lambda && !value.kids.empty() &&
               value.kids.back()->kind == N::TypeValue) {
      t.body = value.kids.back().get();
      // Its type parameters, `(t : type)`; regions are erased first.
      for (size_t i = 0; i + 1 < value.kids.size(); ++i) {
        const Node &p = *value.kids[i];
        if (p.kind != N::LParam || p.kids.size() < 2 ||
            p.kids[0]->kind != N::PVar || p.kids[1]->kids.size() < 2)
          continue;
        const Node &k = *p.kids[1]->kids[1];
        if (k.kind == N::TypeKind && k.text != "region")
          t.params.push_back(p.kids[0]->text);
      }
    } else {
      continue;
    }
    out.push_back(t);
  }
  return out;
}

std::set<std::string> typeMentions(const TypeItem &t,
                                   const std::set<std::string> &names) {
  std::set<std::string> out;
  std::function<void(const Node &)> walk = [&](const Node &n) {
    if (n.kind == N::TypeName && names.count(n.text)) out.insert(n.text);
    for (const NodePtr &k : n.kids) walk(*k);
  };
  walk(*t.body);
  return out;
}

std::vector<std::vector<const TypeItem *>> typeCycles(
    const std::vector<TypeItem> &items) {
  std::set<std::string> names;
  std::map<std::string, const TypeItem *> byName;
  for (const TypeItem &t : items) {
    names.insert(t.item->text);
    byName[t.item->text] = &t;
  }
  std::map<std::string, std::set<std::string>> edges;
  for (const TypeItem &t : items) edges[t.item->text] = typeMentions(t, names);
  // Tarjan's strongly connected components.
  std::map<std::string, int> index, low;
  std::set<std::string> onStack;
  std::vector<std::string> stack;
  int next = 0;
  std::vector<std::vector<const TypeItem *>> out;
  std::function<void(const std::string &)> visit = [&](const std::string &v) {
    index[v] = low[v] = next++;
    stack.push_back(v);
    onStack.insert(v);
    for (const std::string &w : edges[v]) {
      if (!index.count(w)) {
        visit(w);
        low[v] = std::min(low[v], low[w]);
      } else if (onStack.count(w)) {
        low[v] = std::min(low[v], index[w]);
      }
    }
    if (low[v] != index[v]) return;
    std::vector<const TypeItem *> group;
    std::string w;
    do {
      w = stack.back();
      stack.pop_back();
      onStack.erase(w);
      group.push_back(byName[w]);
    } while (w != v);
    bool cyclic = group.size() > 1 || edges[v].count(v);
    if (!cyclic) return;
    // In source order.
    std::vector<const TypeItem *> ordered;
    for (const TypeItem &t : items)
      for (const TypeItem *g : group)
        if (g == &t) ordered.push_back(g);
    out.push_back(std::move(ordered));
  };
  for (const TypeItem &t : items)
    if (!index.count(t.item->text)) visit(t.item->text);
  return out;
}

} // namespace pia::syntax
