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

// `let meta C (t : type) (r : region) : concept = sig ... end`.
bool isConcept(const Node &item) {
  return item.kind == NodeKind::LetItem && item.kids.size() >= 4 &&
         item.kids[0]->kind == NodeKind::Params &&
         item.kids[3]->kind == NodeKind::Sig;
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
    // First the generic types, whose shapes the rest need, including
    // those an interface shows.
    for (Node *item : items) {
      if (isGenericType(*item))
        shapeOf(item->text, *item->kids[3]);
      else if (isConcept(*item)) conceptShapeOf(*item);
      else if (item->kind == NodeKind::Interface)
        for (NodePtr &r : item->kids)
          if (isGenericSigType(*r))
            shapeOf(r->text, *r->kids[0]);
    }
    for (Node *item : items) {
      if (item->kind == NodeKind::Interface) {
        eraseInInterface(*item);
      } else if (isGenericType(*item)) {
        eraseInType(item->text, item->kids[3], *item);
      } else if (isConcept(*item)) {
        eraseInConcept(*item);
      } else if (isFunction(*item)) {
        eraseInFunction(*item);
      } else {
        strip(*item, {});
      }
    }
  }

 private:
   void shapeOf(const std::string &name, const Node &value) {
     Shape s;
     for (size_t i = 0; i + 1 < value.kids.size(); ++i)
       s.region.push_back(isRegionParam(*value.kids[i]));
     if (s.regions())
       shapes_[name] = std::move(s);
   }

   // `let t = let (u : type) (r : region) => type ...` in an interface.
   static bool isGenericSigType(const Node &r) {
     if (r.kind != NodeKind::SigType || r.kids.empty())
       return false;
     const Node &v = *r.kids[0];
     return v.kind == NodeKind::Lambda && !v.kids.empty() &&
            v.kids.back()->kind == NodeKind::TypeValue;
   }

   // An interface shows types and signatures as the module defines them,
   // so they lose their regions the same way, and an interface's copy
   // still matches the definition's (ADR 0042, step 2).
   void eraseInInterface(Node &iface) {
     for (NodePtr &r : iface.kids) {
       if (isGenericSigType(*r)) {
         eraseInType(r->text, r->kids[0], *r);
       } else if (r->kind == NodeKind::SigVal && !r->kids.empty() &&
                  r->kids[0]->kids.size() > 1) {
         eraseInSignature(*r);
       } else {
         strip(*r, {});
       }
     }
   }

   // `let f : (t : type) -> (r : region) -> (m : inout bump t r) -> ...`:
   // the region domains go, a domain whose type mentions a region is
   // flagged with it, and `borrowed(r)` naming one is flagged "region", as
   // a function's own parameters are.
   void eraseInSignature(Node &sigVal) {
     std::vector<std::string> regions;
     NodePtr *slot = &sigVal.kids[0]->kids[1];
     while ((*slot)->kind == NodeKind::ArrowType && (*slot)->kids.size() == 2) {
       Node &dom = *(*slot)->kids[0];
       if (dom.kids.size() > 1 && dom.kids[1]->kind == NodeKind::TypeName &&
           dom.kids[1]->text == "region") {
         addUnique(regions, dom.text);
         NodePtr rest = std::move((*slot)->kids[1]);
         *slot = std::move(rest);
         continue;
       }
       slot = &(*slot)->kids[1];
     }
     if (regions.empty()) {
       strip(sigVal, {});
       return;
     }
     auto isRegion = [&](const std::string &n) {
       return std::find(regions.begin(), regions.end(), n) != regions.end();
     };
     Node *cur = sigVal.kids[0]->kids[1].get();
     for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
       Node &dom = *cur->kids[0];
       std::vector<std::string> m;
       if (dom.kids.size() > 1)
         mentionsOf(*dom.kids[1], m);
       forEachLender(dom, [&](Node &lender) {
         if (!isRegion(lender.text))
           return;
         lender.flags = "region";
         addUnique(m, lender.text);
       });
       if (!m.empty())
         dom.flags = "regions:" + join(m);
     }
     forEachLender(*cur, [&](Node &lender) {
       if (isRegion(lender.text))
         lender.flags = "region";
     });
     strip(sigVal, regions);
   }

  void conceptShapeOf(Node &item) {
    Shape s;
    for (const NodePtr &p : item.kids[0]->kids)
      if (p->kind == NodeKind::Param) s.region.push_back(isRegionParam(*p));
    if (s.regions()) concepts_[item.text] = std::move(s);
  }

  // A concept's regions are where the values of its types borrow from: a
  // requirement's parameter whose type mentions one of the concept's type
  // parameters is in every region of the concept, and `borrowed(r)` in a
  // requirement names one of them.
  void eraseInConcept(Node &item) {
    Node &params = *item.kids[0];
    std::vector<std::string> typeParams;
    for (const NodePtr &p : params.kids)
      if (p->kind == NodeKind::Param && !p->kids.empty() &&
          p->kids[0]->kind == NodeKind::Annot &&
          p->kids[0]->kids[1]->kind == NodeKind::TypeKind)
        typeParams.push_back(p->text);
    std::vector<std::string> regions =
        takeRegions(params, 0, params.kids.size());
    if (regions.empty()) {
      strip(item, {});
      return;
    }
    for (NodePtr &r : item.kids[3]->kids) {
      if (r->kind != NodeKind::SigVal || r->kids.empty()) continue;
      Node *cur = r->kids[0]->kids.size() > 1 ? r->kids[0]->kids[1].get()
                                              : nullptr;
      bool any = false;
      for (; cur && cur->kind == NodeKind::ArrowType;
           cur = cur->kids[1].get()) {
        Node &d = *cur->kids[0];
        if (d.kids.size() > 1 && namesAny(*d.kids[1], typeParams)) {
          d.flags = "regions:" + join(regions);
          any = true;
        }
      }
      forEachLender(*r->kids[0], [&](Node &lender) {
        if (std::find(regions.begin(), regions.end(), lender.text) ==
            regions.end())
          return;
        lender.flags = "region";
        if (!any)
          diags_.error(lender.loc,
                       "'borrowed(" + lender.text + ")': no parameter of '" +
                           r->text + "' has a type of '" + item.text +
                           "', so nothing can lend from the region '" +
                           lender.text + "'");
      });
    }
    strip(item, regions);
  }

  static bool namesAny(const Node &n, const std::vector<std::string> &names) {
    if (n.kind == NodeKind::TypeName &&
        std::find(names.begin(), names.end(), n.text) != names.end())
      return true;
    for (const NodePtr &k : n.kids)
      if (namesAny(*k, names)) return true;
    return false;
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

  // A generic type's definition, `slot` in `item`: a type item's value,
  // or an interface's copy of it.
  void eraseInType(const std::string &name, NodePtr &slot, Node &item) {
    Node &value = *slot;
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
          diags_.error(mods.kids[0]->loc, "'borrowed(" + lender +
                                              ")' on a field names a region "
                                              "parameter of its type, and '" +
                                              name + "' has no region '" +
                                              lender + "'");
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
        info_.lentFields.insert(name + "." + f->text);
        mods.text.clear();
        mods.kids.clear();
      }
    // A type of regions only is a plain type.
    if (value.kids.size() == 1) {
      NodePtr tvp = std::move(value.kids.back());
      slot = std::move(tvp);
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

  // Removes the region arguments of type applications in `n`, and of
  // constraints such as `Allocator a t r`.
  void strip(Node &n, const std::vector<std::string> &scope) {
    if (n.kind == NodeKind::Apply && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::Name)
      if (auto s = concepts_.find(n.kids[0]->text); s != concepts_.end() &&
          n.kids.size() - 1 == s->second.region.size())
        for (size_t i = s->second.region.size(); i-- > 0;) {
          if (!s->second.region[i]) continue;
          const Node &a = *n.kids[i + 1];
          if ((a.kind != NodeKind::Name && a.kind != NodeKind::TypeName) ||
              std::find(scope.begin(), scope.end(), a.text) == scope.end())
            diags_.error(a.loc, "'" + n.kids[0]->text + "' takes a region "
                                "here, and this is not one: name a region "
                                "parameter, as in '(r : region)'");
          n.kids.erase(n.kids.begin() + i + 1);
        }
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
  std::map<std::string, Shape> concepts_;
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
