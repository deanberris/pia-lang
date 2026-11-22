#include "meta/Totality.h"

#include <map>
#include <vector>

namespace pia::meta {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

namespace {

std::string at(const Node &n) {
  return std::to_string(n.loc.line) + ":" + std::to_string(n.loc.column);
}

class Checker {
 public:
  Checker(const Node &item,
          const std::function<bool(const std::string &)> &isGlobal,
          std::set<std::string> &callees)
      : self_(item.text), isGlobal_(isGlobal), callees_(callees) {
    for (const NodePtr &p : item.kids[0]->kids) params_.push_back(p->text);
  }

  std::optional<std::string> run(const Node &body) {
    std::map<std::string, size_t> smaller;
    walk(body, smaller);
    if (why_) return why_;
    if (!calls_.empty() && decreasing_.empty())
      return "its recursive calls at " + callsText() +
             " do not all make the same argument smaller";
    return std::nullopt;
  }

 private:
  using Smaller = std::map<std::string, size_t>;  // variable -> parameter

  void fail(std::string why) {
    if (!why_) why_ = std::move(why);
  }

  std::string callsText() const {
    std::string out;
    for (size_t i = 0; i < calls_.size(); ++i)
      out += (i ? ", " : "") + calls_[i];
    return out;
  }

  static bool isName(const Node &n, const char *text) {
    return n.kind == NodeKind::Name && n.text == text;
  }

  // Whether `e` is the parameter `i` itself or a component of it.
  bool reaches(const Node &e, size_t i, const Smaller &smaller) const {
    if (e.kind == NodeKind::Name && e.text == params_[i]) return true;
    return isSmaller(e, i, smaller);
  }

  // Whether `e` is a component of the parameter `i`: `element p`, or a
  // variable bound to one.
  bool isSmaller(const Node &e, size_t i, const Smaller &smaller) const {
    if (e.kind == NodeKind::Name) {
      auto s = smaller.find(e.text);
      return s != smaller.end() && s->second == i;
    }
    return e.kind == NodeKind::Apply && e.kids.size() == 2 &&
           isName(*e.kids[0], "element") && reaches(*e.kids[1], i, smaller);
  }

  // The parameter whose components the list `e` holds: `field_types p` or
  // `type_args p`, for `p` the parameter or a component of it.
  std::optional<size_t> componentsOf(const Node &e,
                                     const Smaller &smaller) const {
    if (e.kind != NodeKind::Apply || e.kids.size() != 2 ||
        !(isName(*e.kids[0], "field_types") || isName(*e.kids[0], "type_args")))
      return std::nullopt;
    for (size_t i = 0; i < params_.size(); ++i)
      if (reaches(*e.kids[1], i, smaller)) return i;
    return std::nullopt;
  }

  static std::string lambdaParam(const Node &lambda, size_t k) {
    if (lambda.kind != NodeKind::Lambda || k + 1 >= lambda.kids.size())
      return "";
    const Node &p = *lambda.kids[k];
    if (p.kids.empty() || p.kids[0]->kind != NodeKind::PVar) return "";
    return p.kids[0]->text;
  }

  void recursiveCall(const Node &call, const Smaller &smaller) {
    calls_.push_back(at(call));
    std::set<size_t> here;
    for (size_t i = 0; i < params_.size() && i + 1 < call.kids.size(); ++i)
      if (isSmaller(*call.kids[i + 1], i, smaller)) here.insert(i);
    if (here.empty()) {
      fail("the recursive call at " + at(call) +
           " has no argument that is a component of its parameter, such as "
           "'element " + (params_.empty() ? "t" : params_[0]) + "'");
      return;
    }
    if (calls_.size() == 1) {
      decreasing_ = here;
    } else {
      std::set<size_t> both;
      for (size_t i : decreasing_)
        if (here.count(i)) both.insert(i);
      decreasing_ = both;
    }
  }

  void walk(const Node &n, const Smaller &smaller) {
    if (why_) return;
    switch (n.kind) {
      case NodeKind::Name:
        if (n.text == self_) {
          fail("it refers to itself at " + at(n) +
               " other than by calling itself");
        } else if (n.text == "listing" || n.text == "redefine") {
          fail("it calls '" + n.text + "' at " + at(n) +
               ", which reads or changes the program");
        } else if (isGlobal_(n.text)) {
          callees_.insert(n.text);
        }
        return;
      case NodeKind::Apply: {
        const Node &head = *n.kids[0];
        if (head.kind == NodeKind::Name && head.text == self_) {
          recursiveCall(n, smaller);
          for (size_t i = 1; i < n.kids.size(); ++i) walk(*n.kids[i], smaller);
          return;
        }
        // `map f (field_types p)` hands f each component of p, and so does
        // `fold f init (field_types p)`, as f's second argument.
        bool isMap = isName(head, "map") && n.kids.size() == 3;
        bool isFold = isName(head, "fold") && n.kids.size() == 4;
        if (isMap || isFold) {
          const Node &fn = *n.kids[1];
          std::optional<size_t> of = componentsOf(*n.kids.back(), smaller);
          std::string x = lambdaParam(fn, isMap ? 0 : 1);
          if (of && !x.empty()) {
            Smaller inner = smaller;
            inner[x] = *of;
            walk(head, smaller);
            walk(fn, inner);
            for (size_t i = 2; i < n.kids.size(); ++i)
              walk(*n.kids[i], smaller);
            return;
          }
        }
        for (const NodePtr &k : n.kids) walk(*k, smaller);
        return;
      }
      case NodeKind::LetIn: {
        const Node &value = *n.kids[3];
        Smaller inner = smaller;
        if (n.kids[0]->kids.empty()) {
          walk(value, smaller);
          for (size_t i = 0; i < params_.size(); ++i)
            if (isSmaller(value, i, smaller)) inner[n.text] = i;
        } else {
          if (mentions(value, n.text))
            fail("its local function '" + n.text + "' at " + at(n) +
                 " is recursive, which is not supported yet in a "
                 "metaprogram that must terminate");
          walk(value, smaller);
        }
        walk(*n.kids[4], inner);
        return;
      }
      case NodeKind::Quote:
        // Only what a quote splices runs.
        walkSplices(n, smaller);
        return;
      default:
        for (const NodePtr &k : n.kids) walk(*k, smaller);
    }
  }

  void walkSplices(const Node &n, const Smaller &smaller) {
    for (const NodePtr &k : n.kids) {
      if (k->kind == NodeKind::Splice) {
        for (const NodePtr &e : k->kids) walk(*e, smaller);
      } else {
        walkSplices(*k, smaller);
      }
    }
  }

  static bool mentions(const Node &n, const std::string &name) {
    if (n.kind == NodeKind::Name && n.text == name) return true;
    for (const NodePtr &k : n.kids)
      if (mentions(*k, name)) return true;
    return false;
  }

  std::string self_;
  const std::function<bool(const std::string &)> &isGlobal_;
  std::set<std::string> &callees_;
  std::vector<std::string> params_;
  std::vector<std::string> calls_;
  std::set<size_t> decreasing_;
  std::optional<std::string> why_;
};

}  // namespace

std::optional<std::string> checkOwnTotality(
    const Node &item, const std::function<bool(const std::string &)> &isGlobal,
    std::set<std::string> &callees) {
  return Checker(item, isGlobal, callees).run(*item.kids[3]);
}

}  // namespace pia::meta
