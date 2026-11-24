// Lints for idiomatic Pia (ADR 0037). See Lint.h and docs/idioms.md.

#include "syntax/Lint.h"
#include "syntax/RecTypes.h"

#include <algorithm>
#include <cctype>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <sstream>

namespace pia::syntax {

namespace {

using i128 = __int128;
using N = NodeKind;

std::string str(i128 v) {
  if (v == 0)
    return "0";
  bool neg = v < 0;
  unsigned __int128 u = neg ? static_cast<unsigned __int128>(-(v + 1)) + 1
                            : static_cast<unsigned __int128>(v);
  std::string s;
  while (u) {
    s.push_back(static_cast<char>('0' + static_cast<int>(u % 10)));
    u /= 10;
  }
  if (neg)
    s.push_back('-');
  std::reverse(s.begin(), s.end());
  return s;
}

// An integer literal without a suffix, such as 100, 0xff or 1_000.
std::optional<i128> literal(std::string_view s) {
  unsigned radix = 10;
  if (s.size() > 2 && s[0] == '0' &&
      (s[1] == 'x' || s[1] == 'o' || s[1] == 'b')) {
    radix = s[1] == 'x' ? 16 : s[1] == 'o' ? 8 : 2;
    s.remove_prefix(2);
  }
  i128 v = 0;
  bool any = false;
  for (char c : s) {
    if (isDigitSeparator(c))
      continue;
    unsigned d;
    if (std::isdigit(static_cast<unsigned char>(c)))
      d = c - '0';
    else if (radix == 16 && std::isxdigit(static_cast<unsigned char>(c)))
      d = std::tolower(static_cast<unsigned char>(c)) - 'a' + 10;
    else
      return std::nullopt; // a suffix, such as 100u8
    if (d >= radix)
      return std::nullopt;
    v = v * radix + d;
    if (v > (static_cast<i128>(1) << 70))
      return std::nullopt;
    any = true;
  }
  if (!any)
    return std::nullopt;
  return v;
}

std::optional<i128> constant(const Node &n) {
  if (n.kind == N::IntLit)
    return literal(n.text);
  if (n.kind == N::Neg && n.kids.size() == 1 && n.kids[0]->kind == N::IntLit)
    if (auto v = literal(n.kids[0]->text))
      return -*v;
  return std::nullopt;
}

struct Interval {
  i128 lo = 0, hi = 0;
  bool operator==(const Interval &o) const { return lo == o.lo && hi == o.hi; }
};

const std::map<std::string, Interval> &machineTypes() {
  static const std::map<std::string, Interval> table = [] {
    std::map<std::string, Interval> t;
    for (int w : {8, 16, 32, 64}) {
      i128 one = 1;
      t["u" + std::to_string(w)] = {0, (one << w) - 1};
      t["i" + std::to_string(w)] = {-(one << (w - 1)), (one << (w - 1)) - 1};
    }
    t["usize"] = t["u64"];
    t["isize"] = t["i64"];
    return t;
  }();
  return table;
}

// The range of an integer type written as `u8` or `int{0..99}`.
std::optional<Interval> rangeOf(const Node &type) {
  if (type.kind == N::TypeName) {
    auto it = machineTypes().find(type.text);
    if (it != machineTypes().end())
      return it->second;
  }
  if (type.kind == N::RangeType && type.text == "int" &&
      type.kids.size() == 2) {
    auto lo = constant(*type.kids[0]), hi = constant(*type.kids[1]);
    if (lo && hi && *lo <= *hi)
      return Interval{*lo, *hi};
  }
  return std::nullopt;
}

// The machine integer a range is stored in (docs/irgen.md).
std::string storage(Interval r) {
  for (int w : {8, 16, 32, 64}) {
    i128 one = 1;
    if (r.lo >= 0 && r.hi <= (one << w) - 1)
      return "u" + std::to_string(w);
    if (r.lo < 0 && r.lo >= -(one << (w - 1)) && r.hi <= (one << (w - 1)) - 1)
      return "i" + std::to_string(w);
  }
  return "?";
}

std::string rangeText(Interval r) {
  return "int{" + str(r.lo) + ".." + str(r.hi) + "}";
}

bool isSpace(char c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }

struct Span {
  uint32_t b = UINT32_MAX, e = 0;
};

// The source bytes a node covers, from its leaves. Parentheses around the
// node are not included; edits check the text they keep or remove.
void spanInto(const Node &n, std::string_view src, Span &s) {
  if (n.kind == N::None)
    return;
  s.b = std::min(s.b, n.loc.offset);
  uint32_t e =
      n.loc.offset + static_cast<uint32_t>(std::max<size_t>(n.text.size(), 1));
  if (n.kind == N::Field && !n.kids.empty()) {
    Span o;
    spanInto(*n.kids[0], src, o);
    size_t at = src.find(n.text, o.e);
    s.b = std::min(s.b, o.b);
    e = at == std::string_view::npos
            ? o.e
            : static_cast<uint32_t>(at + n.text.size());
  } else {
    for (const NodePtr &k : n.kids)
      spanInto(*k, src, s);
  }
  if (n.kind == N::Index || n.kind == N::RangeType || n.kind == N::ArrayType ||
      n.kind == N::SliceType) {
    // Closed by `]` or `}` after the last child.
    char close = n.kind == N::RangeType ? '}' : ']';
    size_t at = src.find(close, std::max(s.e, e));
    if (at != std::string_view::npos)
      e = static_cast<uint32_t>(at + 1);
  }
  s.e = std::max(s.e, e);
}

Span spanOf(const Node &n, std::string_view src) {
  Span s;
  spanInto(n, src, s);
  if (s.b == UINT32_MAX)
    s.b = s.e = n.loc.offset;
  return s;
}

bool allSpace(std::string_view src, uint32_t b, uint32_t e) {
  if (b > e || e > src.size())
    return false;
  for (uint32_t i = b; i < e; ++i)
    if (!isSpace(src[i]))
      return false;
  return true;
}

// Whether src[b, e) is `&&` with only white space around it.
bool isAndSeparator(std::string_view src, uint32_t b, uint32_t e) {
  if (b > e || e > src.size())
    return false;
  std::string_view t = src.substr(b, e - b);
  size_t at = t.find("&&");
  if (at == std::string_view::npos)
    return false;
  return allSpace(src, b, b + static_cast<uint32_t>(at)) &&
         allSpace(src, b + static_cast<uint32_t>(at) + 2, e);
}

void flattenAnd(const Node &n, std::vector<const Node *> &out) {
  if (n.kind == N::Binary && n.text == "&&" && n.kids.size() == 2) {
    flattenAnd(*n.kids[0], out);
    flattenAnd(*n.kids[1], out);
  } else {
    out.push_back(&n);
  }
}

bool isComparison(const std::string &op) {
  return op == "<" || op == "<=" || op == ">" || op == ">=";
}

bool isArith(const std::string &op) {
  return op == "+" || op == "-" || op == "*" || op == "/" || op == "%" ||
         op == "+|" || op == "-|" || op == "&" || op == "|" || op == "^" ||
         op == "<<" || op == ">>";
}

// What a constant bound applies to: a parameter, the result, or the
// elements of a slice or array parameter.
struct Target {
  // "x", "result" or "xs.[]".
  std::string key;
  // For messages: "'x'", "the result" or "the elements of 'xs'".
  std::string label;
  // The integer type node that the fix replaces.
  const Node *type = nullptr;
  Interval base;
  // A scalar parameter, whose arithmetic may change with its type.
  bool param = false;
  // The parameter's name.
  std::string name;

  bool isElements() const {
    return key.size() > 3 && key.compare(key.size() - 3, 3, ".[]") == 0;
  }
};

struct Bound {
  const Target *target = nullptr;
  Interval limit; // the bound alone, intersected with the base later
};

// `x < 100`, `100 >= x`, `-5 <= x` on a target named `subject`.
std::optional<Interval>
boundOf(const Node &c, const std::function<bool(const Node &)> &isSubject,
        Interval base) {
  if (c.kind != N::Binary || !isComparison(c.text) || c.kids.size() != 2)
    return std::nullopt;
  const Node &l = *c.kids[0], &r = *c.kids[1];
  std::string op = c.text;
  std::optional<i128> k = isSubject(l) ? constant(r) : std::nullopt;
  if (!k && isSubject(r)) {
    // `100 > x` is `x < 100`.
    k = constant(l);
    op = op == "<" ? ">" : op == "<=" ? ">=" : op == ">" ? "<" : "<=";
  }
  if (!k)
    return std::nullopt;
  Interval b = base;
  if (op == "<")
    b.hi = std::min(b.hi, *k - 1);
  else if (op == "<=")
    b.hi = std::min(b.hi, *k);
  else if (op == ">")
    b.lo = std::max(b.lo, *k + 1);
  else
    b.lo = std::max(b.lo, *k);
  return b;
}

std::string modifiersOf(const Node &annot) {
  return annot.kids.empty() ? std::string() : annot.kids[0]->text;
}

bool writable(const std::string &mods) {
  return mods.find("mutable") != std::string::npos ||
         mods.find("out") != std::string::npos;
}

// Whether `name` is an operand of arithmetic in `n`.
bool arithmeticOn(const Node &n, const std::string &name) {
  if (n.kind == N::Binary && isArith(n.text))
    for (const NodePtr &k : n.kids)
      if (k->kind == N::Name && k->text == name)
        return true;
  if (n.kind == N::Neg && !n.kids.empty() && n.kids[0]->kind == N::Name &&
      n.kids[0]->text == name)
    return true;
  for (const NodePtr &k : n.kids)
    if (arithmeticOn(*k, name))
      return true;
  return false;
}

// Whether `name` is an operand of arithmetic where nothing expects a wider
// type, so the arithmetic happens at the parameter's own type (IRGen joins
// operand types with the expected type): the value of an unannotated
// `let ... in`, an operand of a comparison, or an index.
bool arithmeticAtOwnType(const Node &n, const std::string &name) {
  // Arithmetic in loop invariants and assertions is exact (docs/verifier.md).
  if (n.kind == N::LoopAnnots || n.kind == N::Assert || n.kind == N::Assume)
    return false;
  if (n.kind == N::LetIn && n.kids.size() >= 5) {
    const Node &ret = *n.kids[1];
    bool annotated = ret.kind == N::RetAnnot && !ret.kids.empty() &&
                     ret.kids[0]->kind == N::Annot;
    if (!annotated && n.kids[0]->kids.empty() && arithmeticOn(*n.kids[3], name))
      return true;
  }
  if (n.kind == N::Binary && isComparison(n.text))
    for (const NodePtr &k : n.kids)
      if (arithmeticOn(*k, name))
        return true;
  if (n.kind == N::Index && n.kids.size() == 2 &&
      arithmeticOn(*n.kids[1], name))
    return true;
  for (const NodePtr &k : n.kids)
    if (arithmeticAtOwnType(*k, name))
      return true;
  return false;
}

std::string joinNames(const std::vector<std::string> &names) {
  std::string s;
  for (size_t i = 0; i < names.size(); ++i) {
    if (i)
      s += i + 1 == names.size() ? " and " : ", ";
    s += names[i];
  }
  return s;
}

// A structural key for a subtree, without locations.
void keyOf(const Node &n, std::string &out, bool maskTypes, bool maskLits) {
  static const std::set<N> typeKinds = {
      N::TypeName,  N::RangeType,  N::TypeInst,       N::SliceType,
      N::ArrayType, N::RecordType, N::RefinementType, N::UnionType,
      N::ArrowType, N::TypeApp};
  if (maskTypes && typeKinds.count(n.kind)) {
    out += "(T)";
    return;
  }
  out += '(';
  out += nodeKindName(n.kind);
  if (!n.text.empty()) {
    out += ' ';
    out += maskLits && (n.kind == N::IntLit || n.kind == N::FloatLit) ? "#"
                                                                      : n.text;
  }
  for (const NodePtr &k : n.kids)
    keyOf(*k, out, maskTypes, maskLits);
  out += ')';
}

size_t sizeOf(const Node &n) {
  size_t s = 1;
  for (const NodePtr &k : n.kids)
    s += sizeOf(*k);
  return s;
}

class Linter {
public:
  Linter(std::string_view src) : src_(src) {}

  std::vector<Lint> run(const Node &program) {
    walk(program, /*topLevel=*/true);
    families(program);
    needlessRec(program);
    std::stable_sort(out_.begin(), out_.end(),
                     [](const Lint &a, const Lint &b) {
                       return a.loc.offset < b.loc.offset;
                     });
    return std::move(out_);
  }

private:
  std::string_view src_;
  std::vector<Lint> out_;
  std::set<std::string> allow_; // of the function being linted

  std::string text(Span s) const {
    return std::string(src_.substr(s.b, s.e - s.b));
  }

  void add(Lint l) {
    if (allow_.count(l.name))
      return;
    out_.push_back(std::move(l));
  }

  // A `let rec` type that refers to no type of its cycle needs no `rec`
  // (ADR 0047).
  void needlessRec(const Node &program) {
    std::vector<TypeItem> items = typeItems(program);
    std::set<const Node *> cyclic;
    for (const std::vector<const TypeItem *> &g : typeCycles(items))
      for (const TypeItem *t : g) cyclic.insert(t->item);
    for (const TypeItem &t : items) {
      if (!t.rec || cyclic.count(t.item)) continue;
      Lint l;
      l.name = "needless_rec";
      l.loc = t.item->loc;
      l.end = t.item->loc.offset;
      l.message = "'" + t.item->text + "' is declared 'let rec' but does not "
                  "refer to itself; drop 'rec'";
      add(std::move(l));
    }
  }

  void walk(const Node &n, bool topLevel) {
    // A quote is a template for a metaprogram to fill in, not code.
    if (n.kind == N::Quote)
      return;
    if (n.kind == N::LetItem || n.kind == N::LetIn)
      function(n);
    for (const NodePtr &k : n.kids)
      walk(*k, topLevel && (n.kind == N::Program || n.kind == N::Module));
  }

  // --- one function --------------------------------------------------

  void function(const Node &fn) {
    if (fn.kids.size() < 4)
      return;
    const Node &params = *fn.kids[0];
    const Node &ret = *fn.kids[1];
    const Node &contracts = *fn.kids[2];
    const Node &body = *fn.kids[3];
    if (fn.flags.find("meta") != std::string::npos)
      return;
    bool erased = fn.flags.find("spec") != std::string::npos ||
                  fn.flags.find("lemma") != std::string::npos;

    allowOf(fn);
    // Under @overflow(wrap) or (saturate) the arithmetic is defined, so a
    // bound moved into a type would change what the code computes.
    bool proofMode = true;
    for (const Node *a : annotations(ret)) {
      if (a->text == "overflow" && !a->kids.empty() &&
          a->kids[0]->text != "proof")
        proofMode = false;
      if (a->text == "fuel" && !a->kids.empty())
        deepFuel(fn, *a);
    }

    for (const NodePtr &c : contracts.kids) {
      if (c->kids.empty())
        continue;
      // A lemma's contract is the fact, proved once, that this lint asks
      // for, so it is not flagged.
      bool lemma = false;
      std::istringstream words(fn.flags);
      for (std::string word; words >> word;)
        lemma = lemma || word == "lemma";
      if (!lemma)
        nonlinear(*c, fn.text);
    }
    assumes(body);

    if (!proofMode || erased)
      return;
    // A foreign function's types are its C signature (#55).
    if (body.kind == N::Apply && body.kids.size() == 2 &&
        body.kids[0]->kind == N::Name && body.kids[0]->text == "extern" &&
        body.kids[1]->kind == N::StringLit)
      return;

    std::vector<Target> targets = boundTargets(params, ret);
    if (targets.empty())
      return;

    for (const NodePtr &c : contracts.kids) {
      if (c->kids.empty())
        continue;
      if (c->kind == N::Requires)
        bounds(*c, targets, body, /*ensures=*/false);
      if (c->kind == N::Ensures)
        bounds(*c, targets, body, /*ensures=*/true);
    }
  }

  // The annotations on a return type, such as @fuel(8) and @allow(name).
  static std::vector<const Node *> annotations(const Node &ret) {
    std::vector<const Node *> out;
    if (ret.kind != N::RetAnnot || ret.kids.size() < 2)
      return out;
    for (const NodePtr &a : ret.kids[1]->kids)
      out.push_back(a.get());
    return out;
  }

  void deepFuel(const Node &fn, const Node &fuel) {
    std::optional<i128> f = constant(*fuel.kids[0]);
    if (!f || *f <= 4)
      return;
    Lint l;
    l.name = "deep_fuel";
    l.loc = fuel.loc;
    l.end = spanOf(fuel, src_).e;
    l.message = "@fuel(" + str(*f) + ") unfolds '" + fn.text + "' " + str(*f) +
                " times in every query that mentions it; prove the "
                "fact you need once, as a 'let lemma' by induction, "
                "and keep the fuel low";
    add(std::move(l));
  }

  // The places a constant bound could move into a type: each read-only
  // integer parameter, the elements of each read-only slice or array of
  // integers, and an integer result. A type that already has a refinement
  // (`where ...`) is left alone, since the fix would have to merge them.
  static std::vector<Target> boundTargets(const Node &params, const Node &ret) {
    std::vector<Target> targets;
    for (const NodePtr &p : params.kids) {
      if (p->kind != N::Param || p->kids.empty())
        continue;
      const Node &annot = *p->kids[0];
      if (annot.kids.size() < 2 || writable(modifiersOf(annot)))
        continue;
      if (annot.kids.size() > 2 && annot.kids[2]->kind != N::None)
        continue;
      const Node &t = *annot.kids[1];
      if (auto r = rangeOf(t)) {
        targets.push_back(
            {p->text, "'" + p->text + "'", &t, *r, true, p->text});
        continue;
      }
      if (t.kind != N::SliceType && t.kind != N::ArrayType)
        continue;
      if (t.kids.empty())
        continue;
      if (auto er = rangeOf(*t.kids[0]))
        targets.push_back({p->text + ".[]", "the elements of '" + p->text + "'",
                           t.kids[0].get(), *er, false, p->text});
    }
    if (ret.kind != N::RetAnnot || ret.kids.empty() ||
        ret.kids[0]->kind != N::Annot)
      return targets;
    const Node &annot = *ret.kids[0];
    if (annot.kids.size() < 2 || !modifiersOf(annot).empty())
      return targets;
    if (annot.kids.size() >= 3 && annot.kids[2]->kind != N::None)
      return targets;
    if (auto r = rangeOf(*annot.kids[1]))
      targets.push_back(
          {"result", "the result", annot.kids[1].get(), *r, false, "result"});
    return targets;
  }

  // Which target, if any, a conjunct bounds by a constant.
  std::optional<Bound>
  classify(const Node &c, const std::vector<Target> &targets, bool ensures) {
    for (const Target &t : targets) {
      bool isResult = t.key == "result";
      if (isResult != ensures)
        continue;
      if (t.isElements()) {
        if (auto r = elementBound(c, t))
          return Bound{&t, *r};
        continue;
      }
      auto isName = [&](const Node &n) {
        return n.kind == N::Name && n.text == t.key;
      };
      if (auto r = boundOf(c, isName, t.base))
        return Bound{&t, *r};
    }
    return std::nullopt;
  }

  // The bound on the elements of slice `t` that `c` states, if it is
  // `forall (k in 0..len xs). xs.[k] < C`, with any number of bounds on
  // `xs.[k]` joined by `&&`. Elements can only be bounded in a precondition.
  static std::optional<Interval> elementBound(const Node &c, const Target &t) {
    if (c.kind != N::Quantifier || c.text != "forall" || c.kids.size() != 2)
      return std::nullopt;
    const Node &b = *c.kids[0];
    if (b.kind != N::RangeBinder || b.kids.empty() ||
        b.kids[0]->kind != N::Range)
      return std::nullopt;
    // The quantifier must cover every element, or the bound is weaker than
    // a type on the elements would say.
    const Node &range = *b.kids[0];
    std::optional<i128> lo = constant(*range.kids[0]);
    const Node &hi = *range.kids[1];
    bool wholeLen = hi.kind == N::Apply && hi.kids.size() == 2 &&
                    hi.kids[0]->text == "len" && hi.kids[1]->kind == N::Name &&
                    hi.kids[1]->text == t.name;
    if (!lo || *lo != 0 || !wholeLen)
      return std::nullopt;
    const std::string &k = b.text;
    auto isElem = [&](const Node &n) {
      return n.kind == N::Index && n.kids.size() == 2 &&
             n.kids[0]->kind == N::Name && n.kids[0]->text == t.name &&
             n.kids[1]->kind == N::Name && n.kids[1]->text == k;
    };
    std::vector<const Node *> parts;
    flattenAnd(*c.kids[1], parts);
    Interval r = t.base;
    for (const Node *p : parts) {
      std::optional<Interval> one = boundOf(*p, isElem, t.base);
      if (!one)
        return std::nullopt;
      r.lo = std::max(r.lo, one->lo);
      r.hi = std::min(r.hi, one->hi);
    }
    return r;
  }

  void bounds(const Node &clause, const std::vector<Target> &targets,
              const Node &body, bool ensures) {
    std::vector<const Node *> conj;
    flattenAnd(*clause.kids[0], conj);
    std::vector<std::optional<Bound>> what;
    std::map<const Target *, Interval> limit;
    std::vector<const Target *> order;
    for (const Node *c : conj) {
      what.push_back(classify(*c, targets, ensures));
      if (!what.back())
        continue;
      const Target *t = what.back()->target;
      auto [it, fresh] = limit.emplace(t, t->base);
      if (fresh)
        order.push_back(t);
      it->second.lo = std::max(it->second.lo, what.back()->limit.lo);
      it->second.hi = std::min(it->second.hi, what.back()->limit.hi);
    }
    if (order.empty())
      return;
    // An empty range means the contract can never hold: not this lint's
    // business.
    for (const Target *t : order)
      if (limit[t].lo > limit[t].hi)
        return;

    std::vector<Span> spans;
    for (const Node *c : conj)
      spans.push_back(spanOf(*c, src_));
    bool separated = true;
    for (size_t i = 0; i + 1 < spans.size(); ++i)
      separated = separated && isAndSeparator(src_, spans[i].e, spans[i + 1].b);
    std::string keyword = ensures ? "ensures" : "requires";
    uint32_t kwEnd = clause.loc.offset + static_cast<uint32_t>(keyword.size());
    bool clean = separated && allSpace(src_, kwEnd, spans.front().b);

    bool all = std::all_of(what.begin(), what.end(),
                           [](auto &w) { return w.has_value(); });
    if (all) {
      emit(clause, order, limit, body, ensures, clean, spans, what,
           /*removeAll=*/true, clause.loc, spans.back().e);
      return;
    }
    // Some conjuncts are not bounds and stay. One lint per target, so each
    // fix can be taken on its own.
    for (const Target *t : order) {
      std::vector<std::optional<Bound>> mine;
      for (auto &w : what)
        mine.push_back(w && w->target == t ? w : std::nullopt);
      size_t first = 0;
      while (!mine[first])
        ++first;
      uint32_t end = 0;
      for (size_t i = 0; i < mine.size(); ++i)
        if (mine[i])
          end = std::max(end, spans[i].e);
      std::map<const Target *, Interval> one{{t, limit[t]}};
      emit(clause, {t}, one, body, ensures, clean, spans, mine,
           /*removeAll=*/false, locAt(spans[first].b), end);
    }
  }

  SourceLoc locAt(uint32_t offset) const {
    SourceLoc l;
    l.offset = offset;
    l.line = 1;
    uint32_t lineStart = 0;
    for (uint32_t i = 0; i < offset && i < src_.size(); ++i)
      if (src_[i] == '\n') {
        ++l.line;
        lineStart = i + 1;
      }
    l.column = offset - lineStart + 1;
    return l;
  }

  void emit(const Node &clause, const std::vector<const Target *> &order,
            std::map<const Target *, Interval> &limit, const Node &body,
            bool ensures, bool clean, const std::vector<Span> &spans,
            const std::vector<std::optional<Bound>> &remove, bool removeAll,
            SourceLoc at, uint32_t end) {
    std::vector<std::string> tightened, redundant, types, notes;
    std::vector<TextEdit> edits;
    bool preferred = true;
    bool skipped = false;
    for (const Target *t : order) {
      Interval r = limit[t];
      if (r == t->base) {
        redundant.push_back(t->label);
        continue;
      }
      // A one-sided bound on a wide type would read int{1..4294967295};
      // until ranges can leave a side open, the contract says it better.
      bool open = (r.hi == t->base.hi && r.hi > 65535) ||
                  (r.lo == t->base.lo && r.lo < -65536);
      if (open) {
        skipped = true;
        continue;
      }
      tightened.push_back(t->label);
      std::string rt = rangeText(r);
      Span ts = spanOf(*t->type, src_);
      edits.push_back({ts.b, ts.e, rt});
      if (t->key == "result")
        types.push_back("the return type " + rt);
      else if (t->param)
        types.push_back("(" + t->name + " : " + rt + ")");
      else
        types.push_back("(" + t->name + " : [" + rt + "])");
      std::string from = storage(t->base), to = storage(r);
      if (from != to && t->key != "result" && t->param)
        notes.push_back("'" + t->name + "' is then stored as " + to + ", not " +
                        from + ", which changes the C signature");
      else if (from != to && t->key == "result")
        notes.push_back("the result is then stored as " + to + ", not " + from +
                        ", which changes the C signature");
      else if (from != to)
        notes.push_back("the elements of '" + t->name +
                        "' are then stored as " + to + ", not " + from);
      if (t->param && arithmeticAtOwnType(body, t->name)) {
        notes.push_back(
            "arithmetic on '" + t->name +
            "' that no wider type is "
            "expected for, such as in a comparison or an unannotated "
            "'let', then happens at " +
            rt + ", and may need a type");
        preferred = false;
      }
    }

    // The clause, or the conjuncts this lint covers, go away. Only a clause
    // written as plain conjuncts joined by `&&` gets a fix: anything else
    // between them, such as a comment or parentheses, would be lost.
    if (clean)
      edits.push_back(removeAll ? removeClause(clause, spans)
                                : keepConjuncts(spans, remove));
    std::sort(
        edits.begin(), edits.end(),
        [](const TextEdit &a, const TextEdit &b) { return a.begin < b.begin; });

    // Moving only some of the bounds would leave the clause half done.
    if (skipped)
      return;
    Lint l;
    l.loc = at;
    l.end = end;
    std::string what = ensures ? "postcondition" : "precondition";
    if (!tightened.empty()) {
      l.name = ensures ? "range_ensures" : "range_requires";
      bool elems = std::any_of(order.begin(), order.end(), [](const Target *t) {
        return !t->param && t->key != "result";
      });
      l.message =
          std::string(removeAll ? "this " + what + " only bounds "
                                : "this part of the " + what + " bounds ") +
          joinNames(tightened) + " by constants; say it in the type" +
          (tightened.size() > 1 ? "s" : "") + " instead, " + joinNames(types) +
          ", so the fact travels with the value and intervals can use it" +
          (elems ? " without a quantifier" : "");
      l.fixTitle = "Move the bound into the type: " + joinNames(types);
    } else {
      l.name = "redundant_bound";
      l.message = std::string(removeAll ? "this " : "this part of the ") +
                  what + " only restates the type of " + joinNames(redundant) +
                  "; remove it";
      l.fixTitle = "Remove the bound the type already states";
    }
    for (const std::string &n : notes)
      l.message += "; note: " + n;
    if (clean)
      l.edits = std::move(edits);
    else
      l.fixTitle.clear();
    l.preferred = preferred;
    add(std::move(l));
  }

  // Deletes the whole clause, with the line break and indentation before
  // it, so no blank line is left behind.
  TextEdit removeClause(const Node &clause,
                        const std::vector<Span> &spans) const {
    uint32_t b = clause.loc.offset;
    while (b > 0 && (src_[b - 1] == ' ' || src_[b - 1] == '\t'))
      --b;
    if (b > 0 && src_[b - 1] == '\n') {
      --b;
      if (b > 0 && src_[b - 1] == '\r')
        --b;
    }
    return {b, spans.back().e, ""};
  }

  // Replaces the conjuncts with the ones `remove` does not cover, each with
  // the separator that followed it, so a clause written over several lines
  // keeps its layout.
  TextEdit
  keepConjuncts(const std::vector<Span> &spans,
                const std::vector<std::optional<Bound>> &remove) const {
    std::vector<size_t> keep;
    for (size_t i = 0; i < spans.size(); ++i)
      if (!remove[i])
        keep.push_back(i);
    std::string kept;
    for (size_t j = 0; j < keep.size(); ++j) {
      size_t i = keep[j];
      kept += text(spans[i]);
      if (j + 1 < keep.size())
        kept +=
            i + 1 < spans.size() ? text({spans[i].e, spans[i + 1].b}) : " && ";
    }
    return {spans.front().b, spans.back().e, kept};
  }

  // --- contracts the solver finds hard ------------------------------

  void nonlinear(const Node &clause, const std::string &fn) {
    // Only inside an inequality: bounding a product needs nonlinear
    // reasoning, while `result = a * b` is a definition the solver can
    // usually match against the code.
    const Node *found = nullptr;
    bool inInequality = false;
    std::function<void(const Node &)> look = [&](const Node &n) {
      if (found)
        return;
      if (n.kind == N::Binary && isComparison(n.text) && !inInequality) {
        inInequality = true;
        for (const NodePtr &k : n.kids)
          look(*k);
        inInequality = false;
        return;
      }
      if (inInequality && n.kind == N::Binary && n.kids.size() == 2 &&
          (n.text == "*" || n.text == "/" || n.text == "%")) {
        // A real literal is a constant too: `x / 2.0` is linear.
        auto isConst = [](const Node &k) {
          const Node &v =
              k.kind == N::Neg && k.kids.size() == 1 ? *k.kids[0] : k;
          return constant(k).has_value() || v.kind == N::FloatLit;
        };
        bool lc = isConst(*n.kids[0]);
        bool rc = isConst(*n.kids[1]);
        // A division by a variable is hard anywhere. A product of two
        // variables is flagged in a precondition, which every goal of the
        // function assumes, but not in a postcondition, where it is often
        // the specification itself, as for a saturating multiply.
        if (n.text == "*" ? (!lc && !rc && clause.kind == N::Requires) : !rc) {
          found = &n;
          return;
        }
      }
      for (const NodePtr &k : n.kids)
        look(*k);
    };
    look(*clause.kids[0]);
    if (!found)
      return;
    Lint l;
    l.name = "nonlinear_contract";
    Span s = spanOf(*found, src_);
    l.loc = locAt(s.b);
    l.end = s.e;
    l.message =
        "'" + text(s) + "' in a contract of '" + fn +
        "' is nonlinear, and the solver has no decision procedure for it, "
        "so every query that assumes or proves this clause may be slow; "
        "bound the factors with range types so intervals decide it, "
        "compute the product in a helper with @overflow(saturate) and a "
        "linear contract, or prove the fact once as a 'let lemma'";
    add(std::move(l));
  }

  void assumes(const Node &n) {
    if (n.kind == N::Assume) {
      Lint l;
      l.name = "assume";
      l.loc = n.loc;
      l.end = spanOf(n, src_).e;
      l.message =
          "'assume' is never checked: if callers can promise it, make it a "
          "'requires'; if it follows from what is known, prove it with "
          "'assert' or a lemma";
      add(std::move(l));
    }
    for (const NodePtr &k : n.kids)
      assumes(*k);
  }

  // --- families of functions -----------------------------------------

  static bool plainFunction(const Node &n) {
    return n.kind == N::LetItem && n.kids.size() >= 4 &&
           !n.kids[0]->kids.empty() && n.kids[3]->kind != N::TypeValue &&
           n.flags.find("meta") == std::string::npos &&
           n.flags.find("lemma") == std::string::npos;
  }

  std::string signatureKey(const Node &fn, bool maskTypes) {
    std::string k;
    for (const NodePtr &p : fn.kids[0]->kids) {
      k += p->text;
      k += ':';
      if (!p->kids.empty())
        keyOf(*p->kids[0], k, maskTypes, false);
    }
    k += "->";
    keyOf(*fn.kids[1], k, maskTypes, false);
    return k;
  }

  void families(const Node &program) {
    std::vector<const Node *> fns;
    std::vector<const Node *> records;
    std::function<void(const Node &)> collect = [&](const Node &n) {
      for (const NodePtr &k : n.kids) {
        if (plainFunction(*k))
          fns.push_back(k.get());
        if (k->kind == N::LetItem && k->kids.size() >= 4 &&
            k->kids[3]->kind == N::TypeValue)
          records.push_back(k.get());
        if (k->kind == N::Module)
          collect(*k);
      }
    };
    collect(program);

    // Same names and body at other types: a generic function. Same up to
    // constants: a parameter or a metaprogram.
    std::map<std::string, const Node *> byBody, byShape;
    for (const Node *fn : fns) {
      const Node &body = *fn->kids[3];
      if (sizeOf(body) < 6)
        continue;
      std::string names;
      for (const NodePtr &p : fn->kids[0]->kids)
        names += p->text + ",";
      std::string exact = names, shape = names;
      keyOf(body, exact, true, false);
      keyOf(*fn->kids[2], exact, true, false);
      keyOf(body, shape, true, true);
      keyOf(*fn->kids[2], shape, true, true);
      allowOf(*fn);
      if (auto it = byBody.find(exact); it != byBody.end()) {
        const Node &first = *it->second;
        Lint l;
        l.loc = nameLoc(*fn);
        l.end = l.loc.offset + static_cast<uint32_t>(fn->text.size());
        if (signatureKey(first, false) == signatureKey(*fn, false)) {
          l.name = "duplicate_function";
          l.message = "'" + fn->text + "' is a copy of '" + first.text +
                      "' (line " + std::to_string(first.loc.line) +
                      "); call '" + first.text + "' instead";
        } else {
          l.name = "generic_candidate";
          l.message =
              "'" + fn->text + "' has the same body as '" + first.text +
              "' (line " + std::to_string(first.loc.line) +
              ") at other types; write it once as a generic function, "
              "'(t : type where C t)', where the concept C names what the "
              "body uses, and its laws are proved once per type instead of "
              "once per copy";
        }
        add(std::move(l));
        continue;
      }
      byBody.emplace(exact, fn);
      if (auto it = byShape.find(shape); it != byShape.end()) {
        const Node &first = *it->second;
        Lint l;
        l.name = "metaprogram_candidate";
        l.loc = nameLoc(*fn);
        l.end = l.loc.offset + static_cast<uint32_t>(fn->text.size());
        l.message =
            "'" + fn->text + "' differs from '" + first.text + "' (line " +
            std::to_string(first.loc.line) +
            ") only in its constants; take them as parameters (range-typed, "
            "so callers keep the facts), or generate the family with a "
            "metaprogram so there is one definition to read and prove";
        add(std::move(l));
        continue;
      }
      byShape.emplace(shape, fn);
    }

    // Hand-written field-by-field equality: @derive(eq).
    for (const Node *rec : records)
      derivableEq(*rec, fns);
    allow_.clear();
  }

  // Lints each function in `fns` that compares two values of record type
  // `rec` field by field, unless the record already derives eq.
  void derivableEq(const Node &rec, const std::vector<const Node *> &fns) {
    const Node &tv = *rec.kids[3];
    if (tv.kids.empty() || tv.kids[0]->kind != N::RecordType)
      return;
    if (tv.kids.size() > 1 && derives(*tv.kids[1], "eq"))
      return;
    std::set<std::string> fields;
    for (const NodePtr &f : tv.kids[0]->kids)
      if (f->kind == N::FieldDecl)
        fields.insert(f->text);
    if (fields.empty())
      return;
    for (const Node *fn : fns) {
      if (!comparesFields(*fn, rec.text, fields))
        continue;
      allowOf(*fn);
      Lint l;
      l.name = "derivable_eq";
      l.loc = nameLoc(*fn);
      l.end = l.loc.offset + static_cast<uint32_t>(fn->text.size());
      l.message = "'" + fn->text + "' compares every field of '" + rec.text +
                  "'; write '@derive(eq)' on the type and use '=', so the "
                  "equality and its postcondition stay in step with the fields";
      add(std::move(l));
    }
  }

  // Whether attributes such as `@derive(eq, ord)` derive `what`.
  static bool derives(const Node &attrs, const std::string &what) {
    for (const NodePtr &a : attrs.kids) {
      if (a->text != "derive")
        continue;
      for (const NodePtr &arg : a->kids)
        if (arg->text == what)
          return true;
    }
    return false;
  }

  // Whether `fn` takes two parameters of record type `type` and its body is
  // `a.f = b.f && ...`, comparing each of `fields` exactly once, with either
  // side first.
  static bool comparesFields(const Node &fn, const std::string &type,
                             const std::set<std::string> &fields) {
    const Node &ps = *fn.kids[0];
    if (ps.kids.size() != 2)
      return false;
    for (const NodePtr &p : ps.kids) {
      if (p->kind != N::Param || p->kids.empty() ||
          p->kids[0]->kids.size() < 2 ||
          p->kids[0]->kids[1]->kind != N::TypeName ||
          p->kids[0]->kids[1]->text != type)
        return false;
    }
    const std::string &a = ps.kids[0]->text;
    const std::string &b = ps.kids[1]->text;
    // The field `n` reads from `obj`, or "" when `n` is not `obj.f`.
    auto field = [](const Node &n, const std::string &obj) -> std::string {
      if (n.kind == N::Field && !n.kids.empty() && n.kids[0]->kind == N::Name &&
          n.kids[0]->text == obj)
        return n.text;
      return "";
    };
    std::vector<const Node *> conj;
    flattenAnd(*fn.kids[3], conj);
    std::set<std::string> seen;
    for (const Node *c : conj) {
      if (c->kind != N::Binary || c->text != "=" || c->kids.size() != 2)
        return false;
      std::string l1 = field(*c->kids[0], a), r1 = field(*c->kids[1], b);
      std::string l2 = field(*c->kids[0], b), r2 = field(*c->kids[1], a);
      std::string f = !l1.empty() && l1 == r1   ? l1
                      : !l2.empty() && l2 == r2 ? l2
                                                : "";
      if (f.empty() || !seen.insert(f).second)
        return false;
    }
    return seen == fields;
  }

  void allowOf(const Node &fn) {
    allow_.clear();
    for (const Node *a : annotations(*fn.kids[1])) {
      if (a->text != "allow")
        continue;
      for (const NodePtr &arg : a->kids)
        allow_.insert(arg->text);
    }
  }

  SourceLoc nameLoc(const Node &fn) const {
    size_t at = src_.find(fn.text, fn.loc.offset);
    if (at == std::string_view::npos)
      return fn.loc;
    return locAt(static_cast<uint32_t>(at));
  }
};

} // namespace

const std::vector<std::string_view> &lintNames() {
  static const std::vector<std::string_view> names = {"range_requires",
                                                      "range_ensures",
                                                      "redundant_bound",
                                                      "generic_candidate",
                                                      "metaprogram_candidate",
                                                      "duplicate_function",
                                                      "derivable_eq",
                                                      "nonlinear_contract",
                                                      "deep_fuel",
                                                      "assume",
                                                      "costly_goal",
                                                      "needless_rec"};
  return names;
}

std::vector<Lint> lint(const Node &program, std::string_view source) {
  return Linter(source).run(program);
}

void printLint(std::ostream &os, const Lint &l, std::string_view filename,
               std::string_view source) {
  os << filename << ":" << l.loc.line << ":" << l.loc.column
     << ": warning: " << l.message << " [" << l.name << "]\n";
  size_t start = l.loc.offset;
  while (start > 0 && start <= source.size() && source[start - 1] != '\n')
    --start;
  size_t end = source.find('\n', start);
  if (end == std::string_view::npos)
    end = source.size();
  if (start <= source.size()) {
    os << "  " << source.substr(start, end - start) << "\n  ";
    for (uint32_t i = 1; i < l.loc.column; ++i)
      os << ' ';
    os << "^\n";
  }
  if (!l.fixTitle.empty())
    os << "  fix: " << l.fixTitle << "\n";
}

} // namespace pia::syntax
