#include "irgen/Regions.h"

#include <algorithm>
#include <map>
#include <vector>

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

namespace pia::irgen {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

namespace {

// `(r : region)`: a parameter whose annotation is the word `region`.
bool isRegionAnnot(const Node &annot) {
  return annot.kind == NodeKind::Annot && annot.kids.size() > 1 &&
         annot.kids[0]->kind == NodeKind::Modifiers &&
         annot.kids[0]->text.empty() && annot.kids[0]->kids.empty() &&
         annot.kids[1]->kind == NodeKind::TypeName &&
         annot.kids[1]->text == "region";
}

bool isRegionParam(const Node &p) {
  if (p.kind == NodeKind::Param)
    return !p.kids.empty() && isRegionAnnot(*p.kids[0]);
  if (p.kind == NodeKind::LParam)
    return p.kids.size() > 1 && p.kids[0]->kind == NodeKind::PVar &&
           isRegionAnnot(*p.kids[1]);
  return false;
}

std::string paramName(const Node &p) {
  return p.kind == NodeKind::LParam ? p.kids[0]->text : p.text;
}

// A generic type's parameters: which of them are regions.
struct Shape {
  std::vector<bool> region;
  size_t regions() const {
    return std::count(region.begin(), region.end(), true);
  }
};

bool isGenericType(const Node &item) {
  if (item.kind != NodeKind::LetItem || item.kids.size() < 4 ||
      !item.kids[0]->kids.empty())
    return false;
  const Node &v = *item.kids[3];
  return v.kind == NodeKind::Lambda && !v.kids.empty() &&
         v.kids.back()->kind == NodeKind::TypeValue;
}

bool isFunction(const Node &item) {
  return item.kind == NodeKind::LetItem && item.kids.size() >= 4 &&
         item.kids[0]->kind == NodeKind::Params &&
         !item.kids[0]->kids.empty() && !isGenericType(item);
}

std::string join(const std::vector<std::string> &xs) {
  std::string out;
  for (const std::string &x : xs) out += (out.empty() ? "" : ",") + x;
  return out;
}

void addUnique(std::vector<std::string> &to, const std::string &x) {
  if (std::find(to.begin(), to.end(), x) == to.end()) to.push_back(x);
}

class Eraser {
 public:
  Eraser(syntax::Diagnostics &diags, RegionInfo &info)
      : diags_(diags), info_(info) {}

  void run(Node &program) {
    std::vector<Node *> items;
    for (NodePtr &item : program.kids) {
      if (item->kind == NodeKind::Adapter) {
        for (size_t i = 1; i < item->kids.size(); ++i)
          items.push_back(item->kids[i].get());
        continue;
      }
      items.push_back(item.get());
    }
    // First the generic types, whose shapes the rest need.
    for (Node *item : items)
      if (isGenericType(*item)) shapeOf(*item);
    for (Node *item : items) {
      if (isGenericType(*item)) {
        eraseInType(*item);
      } else if (isFunction(*item)) {
        eraseInFunction(*item);
      } else {
        strip(*item, {});
      }
    }
  }

 private:
  void shapeOf(Node &item) {
    Node &value = *item.kids[3];
    Shape s;
    for (size_t i = 0; i + 1 < value.kids.size(); ++i)
      s.region.push_back(isRegionParam(*value.kids[i]));
    if (s.regions()) shapes_[item.text] = std::move(s);
  }

  // Removes the region parameters of `params`, from `first` on, and
  // returns their names.
  std::vector<std::string> takeRegions(Node &params, size_t first,
                                       size_t end) {
    std::vector<std::string> names, others;
    for (size_t i = first; i < end; ++i) {
      const Node &p = *params.kids[i];
      if (isRegionParam(p)) {
        if (std::find(names.begin(), names.end(), paramName(p)) !=
            names.end())
          diags_.error(p.loc, "the region '" + paramName(p) +
                                  "' is declared twice");
        names.push_back(paramName(p));
      } else if (p.kind == NodeKind::Param || p.kind == NodeKind::LParam) {
        others.push_back(paramName(p));
      }
    }
    for (size_t i = first; i < end; ++i) {
      const Node &p = *params.kids[i];
      if (isRegionParam(p) &&
          std::find(others.begin(), others.end(), paramName(p)) !=
              others.end())
        diags_.error(p.loc, "the region '" + paramName(p) +
                                "' has the name of another parameter");
    }
    auto &k = params.kids;
    k.erase(std::remove_if(k.begin() + first, k.begin() + end,
                           [](const NodePtr &p) { return isRegionParam(*p); }),
            k.begin() + end);
    return names;
  }

  void eraseInType(Node &item) {
    Node &value = *item.kids[3];
    std::vector<std::string> regions =
        takeRegions(value, 0, value.kids.size() - 1);
    if (regions.empty()) {
      strip(item, {});
      return;
    }
    Node &tv = *value.kids.back();
    // Fields `borrowed(r) mutable [t]` borrow from the region: a value of
    // the type may hold a loan.
    if (!tv.kids.empty() && tv.kids[0]->kind == NodeKind::RecordType)
      for (NodePtr &f : tv.kids[0]->kids) {
        if (f->kids.empty() || f->kids[0]->kind != NodeKind::Annot) continue;
        Node &mods = *f->kids[0]->kids[0];
        if (mods.kids.empty()) continue;
        const std::string &lender = mods.kids[0]->text;
        if (std::find(regions.begin(), regions.end(), lender) ==
            regions.end()) {
          diags_.error(mods.kids[0]->loc,
                       "'borrowed(" + lender + ")' on a field names a region "
                       "parameter of its type, and '" + item.text +
                       "' has no region '" + lender + "'");
          continue;
        }
        llvm::SmallVector<llvm::StringRef> words;
        llvm::StringRef(mods.text).split(words, ' ', -1, false);
        bool ok = true;
        for (llvm::StringRef w : words)
          ok &= w == "borrowed" || w == "mutable";
        if (!ok) {
          diags_.error(f->loc, "a field that borrows from a region may be "
                               "'borrowed(" + lender + ")' or 'borrowed(" +
                               lender + ") mutable', and nothing else");
          continue;
        }
        info_.lentFields.insert(item.text + "." + f->text);
        mods.text.clear();
        mods.kids.clear();
      }
    // A type of regions only is a plain type.
    if (value.kids.size() == 1) {
      NodePtr tvp = std::move(value.kids.back());
      item.kids[3] = std::move(tvp);
    }
    strip(item, regions);
  }

  void eraseInFunction(Node &item) {
    Node &params = *item.kids[0];
    std::vector<std::string> regions =
        takeRegions(params, 0, params.kids.size());
    if (regions.empty()) {
      strip(item, {});
      return;
    }
    auto isRegion = [&](const std::string &n) {
      return std::find(regions.begin(), regions.end(), n) != regions.end();
    };
    // Which regions each parameter's type mentions, before the arguments
    // go.
    std::map<std::string, std::vector<std::string>> mentions;
    for (NodePtr &p : params.kids) {
      if (p->kind != NodeKind::Param || p->kids.empty()) continue;
      std::vector<std::string> m;
      mentionsOf(*p->kids[0], m);
      mentions[p->text] = m;
    }
    auto from = [&](const std::string &r) {
      std::vector<std::string> out;
      for (NodePtr &p : params.kids)
        if (p->kind == NodeKind::Param) {
          const auto &m = mentions[p->text];
          if (std::find(m.begin(), m.end(), r) != m.end())
            out.push_back(p->text);
        }
      return out;
    };
    // `borrowed(r)` on a parameter or in the result.
    auto markLenders = [&](Node &annot, std::vector<std::string> &m) {
      forEachLender(annot, [&](Node &lender) {
        if (!isRegion(lender.text)) return;
        lender.flags = "region";
        addUnique(m, lender.text);
        if (from(lender.text).empty())
          diags_.error(lender.loc,
                       "'borrowed(" + lender.text + ")': no parameter of '" +
                           item.text + "' has a type that mentions the "
                           "region '" + lender.text + "', so nothing can "
                           "lend from it");
      });
    };
    for (NodePtr &p : params.kids) {
      if (p->kind != NodeKind::Param || p->kids.empty()) continue;
      std::vector<std::string> m = mentions[p->text];
      markLenders(*p->kids[0], m);
      if (!m.empty()) p->flags = "regions:" + join(m);
    }
    Node &ret = *item.kids[1];
    if (ret.kind == NodeKind::RetAnnot && !ret.kids.empty()) {
      std::vector<std::string> m;
      mentionsOf(*ret.kids[0], m);
      markLenders(*ret.kids[0], m);
      if (!m.empty()) ret.flags = "regions:" + join(m);
    }
    strip(item, regions);
  }

  template <typename F>
  static void forEachLender(Node &n, F f) {
    if (n.kind == NodeKind::Annot && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::Modifiers && !n.kids[0]->kids.empty())
      f(*n.kids[0]->kids[0]);
    for (NodePtr &k : n.kids) forEachLender(*k, f);
  }

  // The regions that the type applications in `n` pass.
  void mentionsOf(const Node &n, std::vector<std::string> &out) {
    if (n.kind == NodeKind::TypeApp && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::TypeName)
      if (auto s = shapes_.find(n.kids[0]->text);
          s != shapes_.end() && n.kids.size() - 1 == s->second.region.size())
        for (size_t i = 0; i < s->second.region.size(); ++i)
          if (s->second.region[i] && n.kids[i + 1]->kind == NodeKind::TypeName)
            addUnique(out, n.kids[i + 1]->text);
    for (const NodePtr &k : n.kids) mentionsOf(*k, out);
  }

  // Removes the region arguments of type applications in `n`.
  void strip(Node &n, const std::vector<std::string> &scope) {
    if (n.kind == NodeKind::TypeApp && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::TypeName)
      if (auto s = shapes_.find(n.kids[0]->text); s != shapes_.end()) {
        const Shape &shape = s->second;
        size_t given = n.kids.size() - 1;
        if (given == shape.region.size()) {
          for (size_t i = shape.region.size(); i-- > 0;) {
            if (!shape.region[i]) continue;
            const Node &a = *n.kids[i + 1];
            if (a.kind != NodeKind::TypeName ||
                std::find(scope.begin(), scope.end(), a.text) == scope.end())
              diags_.error(a.loc,
                           "'" + n.kids[0]->text + "' takes a region here, "
                           "and this is not one: name a region parameter, "
                           "as in '(r : region)', or leave the regions out");
            n.kids.erase(n.kids.begin() + i + 1);
          }
          if (n.kids.size() == 1) {
            NodePtr head = std::move(n.kids[0]);
            n = std::move(*head);
            return;
          }
        }
      }
    for (NodePtr &k : n.kids) strip(*k, scope);
  }

  syntax::Diagnostics &diags_;
  RegionInfo &info_;
  std::map<std::string, Shape> shapes_;
};

bool anyRegion(const Node &n) {
  if (isRegionParam(n)) return true;
  for (const NodePtr &k : n.kids)
    if (anyRegion(*k)) return true;
  return false;
}

}  // namespace

bool hasRegions(const Node &program) { return anyRegion(program); }

void eraseRegions(Node &program, syntax::Diagnostics &diags,
                  RegionInfo &info) {
  Eraser(diags, info).run(program);
}

}  // namespace pia::irgen
