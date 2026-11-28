// The Lean 4 translation of a program's specification (ADR 0061). See
// Lean.h for what is translated and why.

#include "syntax/Lean.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <optional>
#include <set>
#include <sstream>

namespace pia::syntax {
namespace {

using N = NodeKind;

// Lean's keywords and the names its prelude makes awkward to shadow. A Pia
// name that is one of these, or is not a plain Lean identifier, is written
// in guillemets, which make any text a name.
const std::set<std::string> &leanReserved() {
  static const std::set<std::string> words = [] {
    std::istringstream list(
        "abbrev at axiom by calc class def deriving do else end example "
        "exists for from fun have if import in inductive instance let local "
        "match mut namespace noncomputable open opaque partial private "
        "protected Prop return section show Sort structure suffices then "
        "theorem termination_by decreasing_by Type universe unsafe variable "
        "where with default true false True False Int Bool Nat");
    std::set<std::string> out;
    for (std::string w; list >> w;)
      out.insert(w);
    return out;
  }();
  return words;
}

std::string ident(const std::string &name) {
  bool plain =
      !name.empty() &&
      (std::isalpha(static_cast<unsigned char>(name[0])) || name[0] == '_');
  for (char c : name)
    if (!std::isalnum(static_cast<unsigned char>(c)) && c != '_' && c != '\'')
      plain = false;
  if (plain && !leanReserved().count(name))
    return name;
  return "«" + name + "»";
}

bool hasWord(const std::string &flags, const std::string &word) {
  std::istringstream words(flags);
  std::string w;
  while (words >> w)
    if (w == word)
      return true;
  return false;
}

bool isByLean(const Node &item) {
  return item.kind == N::LetItem && hasWord(item.flags, "lemma") &&
         item.kids.size() > 3 && item.kids[3]->kind == N::ByLean;
}

bool isRecordType(const Node &item) {
  return item.kind == N::LetItem && item.kids.size() > 3 &&
         item.kids[0]->kids.empty() && item.kids[3]->kind == N::TypeValue &&
         !item.kids[3]->kids.empty() &&
         item.kids[3]->kids[0]->kind == N::RecordType;
}

// Where an expression sits: in a statement, where `&&` is `∧` and a
// comparison is a `Prop`, or in a value, where they are `Bool`.
enum class Mode { Prop, Value };

class Emitter {
public:
  Emitter(const Node &program, Diagnostics &diags) : diags_(diags) {
    for (const NodePtr &k : program.kids)
      if (k->kind == N::LetItem)
        items_.emplace(k->text, k.get());
  }

  // Emits the definition of `name` and everything it uses, once. False
  // when it has no translation, which is reported.
  bool need(const std::string &name, SourceLoc at) {
    if (text_.count(name) || failed_.count(name))
      return !failed_.count(name);
    if (std::find(visiting_.begin(), visiting_.end(), name) !=
        visiting_.end()) {
      if (name == visiting_.back())
        return true; // its own recursion
      return fail(at, "'" + name + "' and '" + visiting_.back() +
                          "' call each other, which the Lean translation "
                          "does not support yet (ADR 0061)");
    }
    auto it = items_.find(name);
    if (it == items_.end())
      return fail(at, "'" + name +
                          "' has no Lean translation: only spec "
                          "functions, record types and lemmas of "
                          "this file are translated (ADR 0061)");
    const Node &item = *it->second;
    visiting_.push_back(name);
    deps_[name];
    // A definition it uses is emitted in the middle of this one.
    bool saved = ok_;
    std::map<std::string, std::string> savedLocals;
    std::swap(savedLocals, locals_);
    std::vector<std::string> savedRanges, savedGuards;
    std::swap(savedRanges, ranges_);
    std::swap(savedGuards, guards_);
    unsigned savedHyps = hyps_;
    ok_ = true;
    std::string text;
    if (isRecordType(item))
      text = structure(item);
    else if (isByLean(item))
      text = statement(item);
    else if (hasWord(item.flags, "spec") && !hasWord(item.flags, "abstract"))
      text = definition(item);
    else
      fail(item.loc, "'" + name +
                         "' has no Lean translation: only spec "
                         "functions, record types and lemmas are "
                         "translated (ADR 0061)");
    bool good = ok_;
    ok_ = saved && good;
    locals_ = std::move(savedLocals);
    ranges_ = std::move(savedRanges);
    guards_ = std::move(savedGuards);
    hyps_ = savedHyps;
    visiting_.pop_back();
    if (!good) {
      failed_.insert(name);
      return false;
    }
    text_[name] = text;
    order_.push_back(name);
    return true;
  }

  // The text of `name` and of every definition it uses, in file order.
  std::string closure(const std::string &name) {
    std::set<std::string> seen;
    std::vector<std::string> todo{name};
    while (!todo.empty()) {
      std::string n = todo.back();
      todo.pop_back();
      if (!seen.insert(n).second)
        continue;
      for (const std::string &d : deps_[n])
        todo.push_back(d);
    }
    std::string out;
    for (const std::string &n : order_)
      if (seen.count(n))
        out += text_[n];
    return out;
  }

  std::string text() {
    std::string out;
    for (const std::string &n : order_)
      out += text_[n];
    return out;
  }

private:
  bool fail(SourceLoc at, std::string message) {
    if (ok_)
      diags_.error(at, std::move(message));
    ok_ = false;
    return false;
  }

  void use(const std::string &name) {
    if (!visiting_.empty() && name != visiting_.back())
      deps_[visiting_.back()].insert(name);
  }

  // A slice or fixed array is a `Slice'`, its length and its elements by
  // index, as the verifier encodes both. It is a definition like any other,
  // emitted once, first, and part of the hash of every statement that uses it.
  void useSlice() {
    static const char *kSlice = "Slice'";
    if (!text_.count(kSlice)) {
      text_[kSlice] =
          "/-- A Pia slice or fixed array: its length, and its "
          "elements by index. -/\nstructure Slice' (α : Type) where\n"
          "  len : Int\n  get : Int → α\n\n";
      order_.insert(order_.begin(), kSlice);
    }
    use(kSlice);
  }

  // --- types ---------------------------------------------------------

  // The range of a machine integer type. The verifier's integers are exact
  // and never wrap (docs/verifier.md), so in Lean each is an `Int` of
  // which its range is a hypothesis.
  static std::optional<std::pair<std::string, std::string>>
  machineRange(const std::string &name) {
    static const std::map<std::string, std::pair<std::string, std::string>>
        ranges = {
            {"u8", {"0", "255"}},
            {"u16", {"0", "65535"}},
            {"u32", {"0", "4294967295"}},
            {"u64", {"0", "18446744073709551615"}},
            {"usize", {"0", "18446744073709551615"}},
            {"i8", {"-128", "127"}},
            {"i16", {"-32768", "32767"}},
            {"i32", {"-2147483648", "2147483647"}},
            {"i64", {"-9223372036854775808", "9223372036854775807"}},
            {"isize", {"-9223372036854775808", "9223372036854775807"}},
        };
    auto it = ranges.find(name);
    if (it == ranges.end())
      return std::nullopt;
    return it->second;
  }

  static std::string intLit(const std::string &digits) {
    return "(" + digits + " : Int)";
  }

  // The hypothesis that `x` has the type `t`, or "" when every value of
  // its Lean type has it. With `decidable`, only the part an `if` can
  // test: a slice's length, not the range of each element.
  std::string range(const Node &t, const std::string &x,
                    bool decidable = false) {
    if (t.kind == N::Annot)
      return range(*t.kids[1], x, decidable);
    if ((t.kind == N::SliceType && !t.kids.empty()) ||
        (t.kind == N::ArrayType && t.kids.size() == 2)) {
      // A fixed array's length is its type's.
      std::string out =
          t.kind == N::ArrayType
              ? "(" + x + ".len = " + expr(*t.kids[1], Mode::Value) + ")"
              : "(" + intLit("0") + " ≤ " + x + ".len ∧ " + x + ".len ≤ " +
                    intLit("18446744073709551615") + ")";
      if (decidable)
        return out;
      // `i'` is a name no program writes, so it captures none of `x`.
      std::string elem = range(*t.kids[0], "(" + x + ".get i')");
      if (!elem.empty())
        out += " ∧ (∀ (i' : Int), " + intLit("0") + " ≤ i' ∧ i' < " + x +
               ".len → " + elem + ")";
      return out;
    }
    if (t.kind == N::TypeName) {
      if (auto r = machineRange(t.text))
        return "(" + intLit(r->first) + " ≤ " + x + " ∧ " + x + " ≤ " +
               intLit(r->second) + ")";
      return "";
    }
    if (t.kind == N::RangeType && t.kids.size() == 2)
      return "(" + expr(*t.kids[0], Mode::Value) + " ≤ " + x + " ∧ " + x +
             " ≤ " + expr(*t.kids[1], Mode::Value) + ")";
    return "";
  }

  // `field` is set for a record's field, which has no hypothesis to carry
  // its range, so only a type all of whose Lean values it has may be one.
  std::string type(const Node &t, bool field = false) {
    if (t.kind == N::Annot) {
      if (t.kids.size() > 2 && t.kids[2]->kind != N::None)
        fail(t.kids[2]->loc, "a 'where' type has no Lean translation yet "
                             "(ADR 0061, step 3)");
      return type(*t.kids[1], field);
    }
    if (t.kind == N::TypeName) {
      if (t.text == "int")
        return "Int";
      if (t.text == "bool")
        return "Bool";
      if (machineRange(t.text) && !field)
        return "Int";
      auto it = items_.find(t.text);
      if (it != items_.end() && isRecordType(*it->second)) {
        if (!need(t.text, t.loc))
          return "Int";
        use(t.text);
        return ident(t.text);
      }
    }
    if (((t.kind == N::SliceType && !t.kids.empty()) ||
         (t.kind == N::ArrayType && t.kids.size() == 2)) &&
        !field) {
      auto buffer = [](const Node &e) {
        return e.kind == N::SliceType || e.kind == N::ArrayType;
      };
      if (buffer(*t.kids[0]) ||
          (t.kids[0]->kind == N::Annot && t.kids[0]->kids.size() > 1 &&
           buffer(*t.kids[0]->kids[1]))) {
        fail(t.loc, "a slice or array of slices or arrays has no Lean "
                    "translation yet (ADR 0061, step 3)");
        return "Int";
      }
      std::string elem = type(*t.kids[0]);
      useSlice();
      return "(Slice' " + elem + ")";
    }
    if (t.kind == N::RangeType && !field && t.kids.size() == 2 &&
        (t.text == "int" || machineRange(t.text)))
      return "Int";
    if (field && (t.kind == N::SliceType || t.kind == N::ArrayType)) {
      fail(t.loc, "a record field that is a slice or array has no Lean "
                  "translation yet (ADR 0061, step 3)");
      return "Int";
    }
    if (field && (t.kind == N::RangeType ||
                  (t.kind == N::TypeName && machineRange(t.text)))) {
      fail(t.loc, "a record field of a machine integer or range type has no "
                  "Lean translation yet (ADR 0061, step 3)");
      return "Int";
    }
    std::string what =
        t.kind == N::TypeName ? "'" + t.text + "'" : std::string("this type");
    fail(t.loc, "the Lean translation supports int, bool, machine integers "
                "and records of int and bool, not " +
                    what + " yet (ADR 0061, step 3)");
    return "Int";
  }

  // The parameters as binders, with the hypotheses of their ranges in
  // `ranges_`.
  std::string params(const Node &ps, bool binders) {
    std::string out;
    ranges_.clear();
    guards_.clear();
    for (const NodePtr &p : ps.kids) {
      if (p->kind != N::Param || p->kids.empty() ||
          p->kids[0]->kind == N::None) {
        fail(p->loc, "a parameter needs a type for the Lean translation");
        continue;
      }
      locals_[p->text] = ident(p->text);
      out += (binders ? "" : " ") + std::string("(") + ident(p->text) + " : " +
             type(*p->kids[0]) + ")";
      if (binders)
        out += " ";
      if (std::string r = range(*p->kids[0], ident(p->text)); !r.empty())
        ranges_.push_back(r);
      if (std::string r = range(*p->kids[0], ident(p->text), true); !r.empty())
        guards_.push_back(r);
    }
    return out;
  }

  // --- items ---------------------------------------------------------

  std::string structure(const Node &item) {
    std::string out = "structure " + ident(item.text) + " where\n";
    for (const NodePtr &f : item.kids[3]->kids[0]->kids)
      out += "  " + ident(f->text) + " : " + type(*f->kids[0], true) + "\n";
    return out + "  deriving DecidableEq, Inhabited\n\n";
  }

  // `let spec f (a : t) : r requires p decreases m = e`. Lean functions are
  // total, so outside its precondition, where the Pia function says
  // nothing, it is an opaque constant `f'outside`, of which Lean can prove
  // nothing either. A recursive one ends because its measure does, as the
  // verifier proved.
  std::string definition(const Node &item) {
    locals_.clear();
    hyps_ = 0;
    std::string ps = params(*item.kids[0], false);
    const Node &ret = *item.kids[1];
    if (ret.kind != N::RetAnnot || ret.kids.empty() ||
        ret.kids[0]->kind == N::None) {
      fail(item.loc, "'" + item.text +
                         "' needs a result type for the Lean "
                         "translation");
      return "";
    }
    std::string result = type(*ret.kids[0]);
    // Outside its parameters' ranges, which no call reaches, the function
    // is `f'outside` too. The ranges of a slice's elements are left out,
    // since an `if` cannot test a `∀`. A statement applies the function
    // only to slices whose elements are in range, so its value elsewhere
    // decides nothing.
    std::vector<std::string> pre = guards_;
    const Node *measure = nullptr;
    for (const NodePtr &c : item.kids[2]->kids)
      if (c->kind == N::Requires)
        pre.push_back(expr(*c->kids[0], Mode::Prop));
      else if (c->kind == N::Decreases)
        measure = c->kids[0].get();
    // Ensures and reads clauses are proved facts about the function, not
    // its definition.
    std::string body = expr(*item.kids[3], Mode::Value);
    std::string out;
    if (!pre.empty()) {
      // No name a program writes has a `'`, so this one is free.
      std::string outside = ident(item.text + "'outside"), arrow, args;
      for (const NodePtr &p : item.kids[0]->kids)
        if (p->kind == N::Param && !p->kids.empty() &&
            p->kids[0]->kind != N::None) {
          arrow += type(*p->kids[0]) + " → ";
          args += " " + ident(p->text);
        }
      out = "opaque " + outside + " : " + arrow + result + "\n\n";
      body = "if h_req : " + conj(pre) + " then\n    " + body + "\n  else " +
             outside + args;
    }
    out += "def " + ident(item.text) + ps + " : " + result + " :=\n  " + body +
           "\n";
    bool recursive = hasWord(item.flags, "rec");
    if (recursive && !measure)
      fail(item.loc, "the recursive '" + item.text +
                         "' needs a 'decreases' "
                         "measure for the Lean translation");
    if (recursive && measure)
      out += "termination_by (" + expr(*measure, Mode::Value) +
             ").toNat\ndecreasing_by all_goals first | omega | "
             "(simp_wf; omega)\n";
    return out + "\n";
  }

  // `let lemma l (a : t) requires p ensures q = by lean T`, as the
  // proposition `∀ a, p → q`.
  std::string statement(const Node &item) {
    locals_.clear();
    hyps_ = 0;
    std::string binders = params(*item.kids[0], true);
    std::vector<std::string> pre = ranges_, ensures;
    for (const NodePtr &c : item.kids[2]->kids)
      if (c->kind == N::Requires)
        pre.push_back(expr(*c->kids[0], Mode::Prop));
      else if (c->kind == N::Ensures)
        ensures.push_back(expr(*c->kids[0], Mode::Prop));
      else
        fail(c->loc, "a lemma proved in Lean states only 'requires' and "
                     "'ensures'");
    if (ensures.empty())
      fail(item.loc, "the lemma '" + item.text +
                         "' states nothing: give it "
                         "an 'ensures'");
    std::string prop = conj(ensures);
    if (!pre.empty())
      prop = conj(pre) + " → " + prop;
    if (!binders.empty())
      prop = "∀ " + binders.substr(0, binders.size() - 1) + ",\n    " + prop;
    return "/-- The Pia lemma `" + item.text + "`, proved by `" +
           item.kids[3]->text + "`. -/\n@[reducible] def " + ident(item.text) +
           " : Prop :=\n  " + prop + "\n\n";
  }

  static std::string conj(const std::vector<std::string> &ps) {
    std::string out;
    for (const std::string &p : ps)
      out += (out.empty() ? "" : " ∧ ") + p;
    return out;
  }

  // --- expressions ---------------------------------------------------

  // A `Bool` in a statement is the proposition that it is true.
  static std::string asProp(const std::string &value, Mode m) {
    return m == Mode::Prop ? "(" + value + " = true)" : value;
  }

  std::string unsupported(const Node &n, const std::string &what) {
    fail(n.loc, what + " has no Lean translation yet (ADR 0061, step 3)");
    return "default";
  }

  std::string expr(const Node &n, Mode m) {
    switch (n.kind) {
    case N::IntLit: {
      std::string digits;
      for (char c : n.text)
        if (c != '\'' && c != '_')
          digits += c;
      bool hex = digits.size() > 2 && digits[0] == '0' &&
                 (digits[1] == 'x' || digits[1] == 'X');
      size_t end = hex ? 2 : 0;
      while (end < digits.size() &&
             (hex ? std::isxdigit(static_cast<unsigned char>(digits[end]))
                  : std::isdigit(static_cast<unsigned char>(digits[end]))))
        ++end;
      // A suffix such as `u8` names the literal's type, and the checker
      // has made sure the value fits it, so the value is the same `Int`.
      if (end < digits.size() && !machineRange(digits.substr(end)))
        return unsupported(n, "a literal with the suffix '" +
                                  digits.substr(end) + "'");
      // Typed, since a term of literals alone would otherwise be a `Nat`,
      // where `0 - 1 = 0` holds and Pia's `int` says it does not.
      return intLit(digits.substr(0, end));
    }
    case N::BoolLit:
      if (m == Mode::Prop)
        return n.text == "true" ? "True" : "False";
      return n.text;
    case N::Name:
      return asProp(name(n), m);
    case N::Neg:
      return "(-" + expr(*n.kids[0], Mode::Value) + ")";
    case N::Apply:
      return apply(n, m);
    case N::If: {
      if (n.kids.size() < 3 || n.kids[2]->kind == N::None)
        return unsupported(n, "an 'if' with no 'else'");
      std::string h = "h_" + std::to_string(++hyps_);
      return "(if " + h + " : " + expr(*n.kids[0], Mode::Prop) + " then " +
             expr(*n.kids[1], m) + " else " + expr(*n.kids[2], m) + ")";
    }
    case N::LetIn: {
      if (!n.kids[0]->kids.empty() || hasWord(n.flags, "rec") ||
          !n.kids[2]->kids.empty())
        return unsupported(n, "a local function");
      std::string t;
      const Node &ret = *n.kids[1];
      if (ret.kind == N::RetAnnot && !ret.kids.empty() &&
          ret.kids[0]->kind != N::None)
        t = " : " + type(*ret.kids[0]);
      // The value is put in place of the name, which keeps it in sight of
      // `omega` when it proves that a recursion ends. Hygiene means no
      // name is shadowed (ADR 0022), so the substitution captures nothing.
      std::string value = expr(*n.kids[3], Mode::Value);
      if (!t.empty())
        value = "(" + value + t + ")";
      auto saved = locals_.find(n.text) == locals_.end()
                       ? std::optional<std::string>()
                       : std::optional<std::string>(locals_[n.text]);
      locals_[n.text] = value;
      std::string body = expr(*n.kids[4], m);
      if (saved)
        locals_[n.text] = *saved;
      else
        locals_.erase(n.text);
      return body;
    }
    case N::Index:
      if (n.kids.size() != 2)
        return unsupported(n, "this index");
      return asProp("((" + expr(*n.kids[0], Mode::Value) + ").get " +
                        expr(*n.kids[1], Mode::Value) + ")",
                    m);
    case N::Field:
      if (!n.text.empty() && n.text[0] == '$')
        return unsupported(n, "a spliced field");
      return asProp("(" + expr(*n.kids[0], Mode::Value) + ")." + ident(n.text),
                    m);
    case N::RecordLit:
      return "{ " + fields(n, 0) + " }";
    case N::RecordUpdate:
      return "{ " + expr(*n.kids[0], Mode::Value) + " with " + fields(n, 1) +
             " }";
    case N::Quantifier:
      return quantifier(n, m);
    default:
      return unsupported(n, std::string("'") + nodeKindName(n.kind) + "'");
    }
  }

  std::string fields(const Node &n, size_t from) {
    std::string out;
    for (size_t i = from; i < n.kids.size(); ++i) {
      const Node &f = *n.kids[i];
      out += (out.empty() ? "" : ", ") + ident(f.text) +
             " := " + expr(*f.kids[0], Mode::Value);
    }
    return out;
  }

  std::string name(const Node &n) {
    if (auto it = locals_.find(n.text); it != locals_.end())
      return it->second;
    if (n.text == "result")
      return unsupported(n, "'result'");
    if (!need(n.text, n.loc))
      return "default";
    use(n.text);
    return ident(n.text);
  }

  std::string apply(const Node &n, Mode m) {
    const Node &head = *n.kids[0];
    if (head.kind != N::Name)
      return unsupported(n, "a call of a computed function");
    // The prelude's operators, as the meta engine expands them.
    if (hasWord(head.flags, "prelude") && n.kids.size() == 3) {
      static const std::map<std::string, std::string> arith = {
          {"add", "+"}, {"sub", "-"}, {"mul", "*"}};
      static const std::map<std::string, std::string> cmp = {
          {"eq", "="}, {"ne", "≠"}, {"lt", "<"},
          {"le", "≤"}, {"gt", ">"}, {"ge", "≥"}};
      const std::string &op = head.text;
      const Node &a = *n.kids[1], &b = *n.kids[2];
      if (auto it = arith.find(op); it != arith.end())
        return "(" + expr(a, Mode::Value) + " " + it->second + " " +
               expr(b, Mode::Value) + ")";
      if (auto it = cmp.find(op); it != cmp.end()) {
        std::string p = "(" + expr(a, Mode::Value) + " " + it->second + " " +
                        expr(b, Mode::Value) + ")";
        return m == Mode::Prop ? p : "(decide " + p + ")";
      }
      if (op == "and" || op == "or" || op == "implies" || op == "iff") {
        std::string x = expr(a, m), y = expr(b, m);
        if (m == Mode::Prop) {
          const char *sym = op == "and"       ? " ∧ "
                            : op == "or"      ? " ∨ "
                            : op == "implies" ? " → "
                                              : " ↔ ";
          return "(" + x + sym + y + ")";
        }
        if (op == "and")
          return "(" + x + " && " + y + ")";
        if (op == "or")
          return "(" + x + " || " + y + ")";
        if (op == "implies")
          return "(!" + x + " || " + y + ")";
        return "(" + x + " == " + y + ")";
      }
      return unsupported(n, "the operator '" + op + "'");
    }
    if (locals_.count(head.text))
      return unsupported(n, "a call of a parameter");
    // A conversion to `int` is exact (docs/verifier.md), so it is its
    // operand. An integer meets a machine type without one, where the
    // verifier proves it fits; `u8 x` converts a float, which has no
    // translation yet.
    if (!items_.count(head.text) && n.kids.size() == 2) {
      if (head.text == "int")
        return expr(*n.kids[1], Mode::Value);
      if (head.text == "len")
        return "(" + expr(*n.kids[1], Mode::Value) + ").len";
      if (machineRange(head.text))
        return unsupported(n, "a conversion to '" + head.text + "'");
    }
    std::string call = "(" + name(head);
    for (size_t i = 1; i < n.kids.size(); ++i)
      call += " " + expr(*n.kids[i], Mode::Value);
    return asProp(call + ")", m);
  }

  std::string quantifier(const Node &n, Mode m) {
    if (m != Mode::Prop)
      return unsupported(n, "a quantifier in a spec function's body");
    bool all = n.text == "forall";
    std::vector<std::string> added;
    std::string out = "(";
    for (size_t i = 0; i + 1 < n.kids.size(); ++i) {
      const Node &b = *n.kids[i];
      std::string x = ident(b.text);
      if (b.kind == N::Binder) {
        if (b.kids.empty() || b.kids[0]->kind == N::None) {
          unsupported(b, "a bound variable with no type");
          continue;
        }
        out += (all ? "∀ (" : "∃ (") + x + " : " + type(*b.kids[0]) + "), ";
        if (std::string r = range(*b.kids[0], x); !r.empty())
          out += r + (all ? " → " : " ∧ ");
      } else if (b.kind == N::RangeBinder && b.kids[0]->kind == N::Range) {
        std::string lo = expr(*b.kids[0]->kids[0], Mode::Value);
        std::string hi = expr(*b.kids[0]->kids[1], Mode::Value);
        out += (all ? "∀ (" : "∃ (") + x + " : Int), " + lo + " ≤ " + x +
               (all ? " → " : " ∧ ") + x + " < " + hi + (all ? " → " : " ∧ ");
      } else {
        unsupported(b, "this bound variable");
        continue;
      }
      if (locals_.emplace(b.text, x).second)
        added.push_back(b.text);
    }
    out += expr(*n.kids.back(), Mode::Prop) + ")";
    for (const std::string &x : added)
      locals_.erase(x);
    return out;
  }

  Diagnostics &diags_;
  std::map<std::string, const Node *> items_;
  std::map<std::string, std::string> text_;
  std::map<std::string, std::set<std::string>> deps_;
  std::set<std::string> failed_;
  std::vector<std::string> order_, visiting_;
  // What each parameter, bound variable and local stands for.
  std::map<std::string, std::string> locals_;
  // The ranges of the parameters that params() last translated.
  std::vector<std::string> ranges_, guards_;
  unsigned hyps_ = 0;
  bool ok_ = true;
};

} // namespace

std::vector<std::pair<std::string, std::string>>
leanLemmas(const Node &program) {
  std::vector<std::pair<std::string, std::string>> out;
  for (const NodePtr &k : program.kids)
    if (isByLean(*k))
      out.emplace_back(k->text, k->kids[3]->text);
  return out;
}

LeanFile emitLean(const Node &program, const std::string &ns,
                  Diagnostics &diags) {
  LeanFile file;
  Emitter e(program, diags);
  for (const NodePtr &k : program.kids) {
    if (!isByLean(*k) || !e.need(k->text, k->loc))
      continue;
    file.statements.push_back(
        {k->text, k->kids[3]->text, e.closure(k->text), k->loc});
  }
  if (!file.statements.empty())
    file.text = "namespace " + ns + "\n\n" + e.text() + "end " + ns + "\n";
  return file;
}

} // namespace pia::syntax
