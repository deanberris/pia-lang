#include "meta/Interpreter.h"

#include <algorithm>
#include <cstdint>
#include <iterator>
#include <set>

#include "syntax/Comments.h"

namespace pia::meta {

using syntax::clone;
using syntax::makeNode;
using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;
using K = Value::Kind;

namespace {

// Steps one expansion may take before it is stopped (design.md,
// "Termination").
constexpr uint64_t kFuel = 1'000'000;

ValuePtr make(Value v) { return std::make_shared<const Value>(std::move(v)); }

ValuePtr unitValue() { return make({}); }

ValuePtr intValue(int64_t i) {
  Value v;
  v.kind = K::Int;
  v.i = i;
  return make(std::move(v));
}

ValuePtr boolValue(bool b) {
  Value v;
  v.kind = K::Bool;
  v.b = b;
  return make(std::move(v));
}

ValuePtr strValue(std::string s) {
  Value v;
  v.kind = K::Str;
  v.s = std::move(s);
  return make(std::move(v));
}

ValuePtr listValue(std::vector<ValuePtr> xs) {
  Value v;
  v.kind = K::List;
  v.list = std::move(xs);
  return make(std::move(v));
}

const char *kindName(K k) {
  switch (k) {
    case K::Unit: return "unit";
    case K::Int: return "an integer";
    case K::Bool: return "a bool";
    case K::Str: return "a string";
    case K::Syntax: return "syntax";
    case K::List: return "a list";
    case K::Closure: case K::Builtin: return "a function";
    case K::Type: return "a type";
  }
  return "?";
}

// The builtins metaprograms can call, with their arity (docs/meta.md).
const std::map<std::string, size_t> &metaBuiltins() {
  // A table laid out by hand, in groups.
  // clang-format off
  static const std::map<std::string, size_t> table = {
      {"map", 2},   {"fold", 3},   {"fields", 1},
      {"name", 1},  {"concat", 2}, {"length", 1},
      // Lists, for generators (ADR 0056).
      {"nth", 2},     {"zip", 2},    {"range", 1},
      {"reverse", 1}, {"filter", 2}, {"product", 1},
      // Signatures and substitution, for generators (ADR 0056).
      {"param_types", 1}, {"return_type", 1}, {"range_of", 1},
      {"constructors", 1}, {"subst", 3},
      // Comments and literate programs (ADR 0029).
      {"listing", 1}, {"comments", 1}, {"doc", 1},   {"text", 1},
      {"style", 1},   {"place", 1},    {"kind", 1},  {"with_doc", 2},
      {"fail", 1},
      // Tactics (ADR 0036, step 6): a goal and the syntax of its terms.
      {"hypotheses", 1}, {"conclusion", 1}, {"params", 1},
      {"children", 1},   {"op", 1},         {"make_call", 2},
      // Pia.Live, in the REPL only (ADR 0031).
      {"redefine", 1},
      // Types, in type-level metaprograms (ADR 0035).
      {"size_of", 1}, {"type_kind", 1}, {"element", 1},
      {"field_types", 1}, {"type_args", 1},
      // The core builtins that operators expand to, so a `where`
      // predicate, which is expanded code, can run (ADR 0035).
      {"eq", 2}, {"ne", 2}, {"lt", 2}, {"gt", 2}, {"le", 2}, {"ge", 2},
      {"add", 2}, {"sub", 2}, {"mul", 2}, {"div", 2}, {"rem", 2},
      {"and", 2}, {"or", 2}, {"implies", 2}, {"iff", 2},
  };
  // clang-format on
  return table;
}

std::string unescape(const std::string &spelling) {
  std::string out;
  for (size_t i = 1; i + 1 < spelling.size(); ++i) {
    char c = spelling[i];
    if (c == '\\' && i + 2 < spelling.size()) {
      char e = spelling[++i];
      out += e == 'n' ? '\n' : e == 't' ? '\t' : e;
    } else {
      out += c;
    }
  }
  return out;
}

// The type item a `type_decl` value holds: `let name = type ...`.
const Node *typeItem(const Value &v) {
  if (v.kind != K::Syntax || !v.syntax) return nullptr;
  const Node &n = *v.syntax;
  if (n.kind == NodeKind::LetItem && n.kids.size() > 3 &&
      n.kids[3]->kind == NodeKind::TypeValue)
    return &n;
  return nullptr;
}

void collectTypeNames(const Node &n, std::vector<std::string> &out) {
  if (n.kind == NodeKind::TypeName) out.push_back(n.text);
  for (const NodePtr &k : n.kids) collectTypeNames(*k, out);
}

// Whether `n` holds an operator not yet expanded to a builtin call.
bool hasBinary(const Node &n) {
  if (n.kind == NodeKind::Binary)
    return true;
  for (const NodePtr &k : n.kids)
    if (hasBinary(*k))
      return true;
  return false;
}

// Whether `n` holds a call of a core builtin that an operator expanded to.
bool hasPreludeCall(const Node &n) {
  if (n.kind == NodeKind::Apply && !n.kids.empty() &&
      n.kids[0]->kind == NodeKind::Name && n.kids[0]->flags == "prelude")
    return true;
  for (const NodePtr &k : n.kids)
    if (hasPreludeCall(*k))
      return true;
  return false;
}

// Whether the child at `index` of a node of kind `parent` is in a type
// position, where a spliced name becomes a type name.
bool isTypePosition(NodeKind parent, size_t index) {
  switch (parent) {
    case NodeKind::Annot: return index == 1;
    case NodeKind::SliceType: case NodeKind::ArrayType: return index == 0;
    case NodeKind::Domain: return index == 1;
    case NodeKind::ArrowType: return index == 1;
    case NodeKind::PTyped: return index == 1;
    case NodeKind::RefinementType: return index == 0;
    case NodeKind::SortItem: return index == 0;  // `let sort s = $t`
    case NodeKind::TypeApp: case NodeKind::UnionType: case NodeKind::TypeInst:
      return true;
    default: return false;
  }
}

// Kinds whose text is a binder name, which may be spliced (`let $n`).
bool hasBinderText(NodeKind k) {
  switch (k) {
    case NodeKind::LetItem: case NodeKind::LetIn: case NodeKind::Param:
    case NodeKind::PVar: case NodeKind::PAs: case NodeKind::Binder:
    case NodeKind::RangeBinder: case NodeKind::Field: case NodeKind::FieldInit: case NodeKind::PField:
    case NodeKind::QuotedDecl:
    // A theory's, a model's and a sort's names (ADR 0036): `let sort $s`.
    case NodeKind::Theory: case NodeKind::Model: case NodeKind::SortItem:
      return true;
    default:
      return false;
  }
}

}  // namespace

bool Interpreter::isCoreBuiltin(const std::string &name) {
  // A table laid out by hand, in groups.
  // clang-format off
  static const std::set<std::string> names = {
      "add", "sub", "add_sat", "sub_sat", "mul", "div", "rem",
      "eq",  "ne",  "lt",      "gt",      "le",  "ge",
      "and", "or",  "implies", "iff",     "len", "old",
      "band", "bor", "bxor", "bnot", "shl", "shr", "abort",
      "clz", "ctz", "popcount", "bswap", "rotl", "rotr",
      // Atomics, as in sema::isCoreBuiltin (ADR 0052).
      "atomic_new", "atomic_load", "atomic_store", "atomic_swap",
      "atomic_cas", "atomic_add", "atomic_sub", "atomic_and", "atomic_or",
      "atomic_xor", "atomic_min", "atomic_max", "fence",
  };
  // clang-format on
  return names.count(name);
}

ValuePtr Interpreter::syntaxValue(NodePtr node) {
  Value v;
  v.kind = K::Syntax;
  v.syntax = std::shared_ptr<Node>(node.release());
  return make(std::move(v));
}

std::vector<std::string> Interpreter::takeRan() {
  std::vector<std::string> out;
  out.swap(ran_);
  return out;
}

void Interpreter::define(const Node &item) { globals_[item.text] = &item; }

const char *Interpreter::kindName(K k) { return pia::meta::kindName(k); }

ValuePtr Interpreter::typeValue(std::string spelling) {
  Value v;
  v.kind = K::Type;
  v.s = std::move(spelling);
  return make(std::move(v));
}

ValuePtr Interpreter::evalWith(
    const Node &expr,
    const std::vector<std::pair<std::string, ValuePtr>> &bindings) {
  fuel_ = 0;
  EnvPtr env;
  for (auto &[name, value] : bindings) {
    auto e = std::make_shared<Env>();
    e->name = name;
    e->value = value;
    e->parent = env;
    env = e;
  }
  return eval(expr, env);
}

ValuePtr Interpreter::call(const std::string &name,
                           std::vector<ValuePtr> args) {
  fuel_ = 0;
  Node n;
  n.kind = NodeKind::Name;
  n.text = name;
  return apply(lookup(n, nullptr), std::move(args));
}

size_t Interpreter::arity(const std::string &name) const {
  auto g = globals_.find(name);
  return g == globals_.end() ? 0 : g->second->kids[0]->kids.size();
}

void Interpreter::tick(const Node &) {
  if (++fuel_ > kFuel)
    throw MetaError{site_, "the metaprogram ran out of fuel after " +
                               std::to_string(kFuel) + " steps"};
}

ValuePtr Interpreter::eval(const Node &expr) {
  fuel_ = 0;
  return eval(expr, nullptr);
}

ValuePtr Interpreter::closure(std::vector<std::string> params,
                              const Node &body, EnvPtr env, std::string name) {
  Value v;
  v.kind = K::Closure;
  v.params = std::move(params);
  v.body = &body;
  v.env = std::move(env);
  v.name = std::move(name);
  return make(std::move(v));
}

static std::vector<std::string> paramNames(const Node &params) {
  std::vector<std::string> out;
  for (const NodePtr &p : params.kids)
    out.push_back(p->kind == NodeKind::Param ? p->text : "");
  return out;
}

ValuePtr Interpreter::lookup(const Node &n, const EnvPtr &env) {
  for (const Env *e = env.get(); e; e = e->parent.get())
    if (e->name == n.text) return e->value;
  auto g = globals_.find(n.text);
  if (g != globals_.end()) {
    const Node &item = *g->second;
    if (item.kids[0]->kids.empty()) return eval(*item.kids[3], nullptr);
    return closure(paramNames(*item.kids[0]), *item.kids[3], nullptr,
                   item.text);
  }
  if (metaBuiltins().count(n.text)) {
    Value v;
    v.kind = K::Builtin;
    v.s = n.text;
    return make(std::move(v));
  }
  // In a type-level metaprogram, a type's name is the type (ADR 0035).
  if (host_.named)
    if (std::optional<std::string> t = host_.named(n.text))
      return typeValue(*t);
  // In a top-level call, the name of one of the program's items is that
  // item, and a variant's constructor is its name, so a call can take a
  // type and its constructors as arguments: `machine conn_state Closed`
  // (ADR 0036, theory-building metaprograms).
  for (const Node *item : listing_) {
    if (item->kind != NodeKind::LetItem) continue;
    if (item->text == n.text && item->flags.find("meta") == std::string::npos)
      return syntaxValue(clone(*item));
    if (item->kids.size() > 3 && item->kids[3]->kind == NodeKind::TypeValue &&
        !item->kids[3]->kids.empty() &&
        item->kids[3]->kids[0]->kind == NodeKind::Variants)
      for (const syntax::NodePtr &c : item->kids[3]->kids[0]->kids)
        if (c->text == n.text) {
          auto name = makeNode(NodeKind::Name, site_, n.text);
          return syntaxValue(std::move(name));
        }
  }
  throw MetaError{site_, "unknown name '" + n.text + "' in a metaprogram"};
}

ValuePtr Interpreter::eval(const Node &n, const EnvPtr &env) {
  tick(n);
  switch (n.kind) {
    case NodeKind::IntLit: {
      std::string digits;
      for (char c : n.text) {
        if (syntax::isDigitSeparator(c))
          continue;
        if (c < '0' || c > '9') break;
        digits += c;
      }
      try {
        return intValue(std::stoll(digits));
      } catch (...) {
        throw MetaError{site_, "the integer " + n.text +
                                   " is too large for a metaprogram"};
      }
    }
    case NodeKind::BoolLit:
      return boolValue(n.text == "true");
    case NodeKind::StringLit:
      return strValue(unescape(n.text));
    case NodeKind::Unit:
      return unitValue();
    case NodeKind::Name:
      return lookup(n, env);
    case NodeKind::ListLit: {
      std::vector<ValuePtr> xs;
      for (const NodePtr &k : n.kids) xs.push_back(eval(*k, env));
      return listValue(std::move(xs));
    }
    case NodeKind::Apply: {
      ValuePtr fn = eval(*n.kids[0], env);
      std::vector<ValuePtr> args;
      for (size_t i = 1; i < n.kids.size(); ++i)
        args.push_back(eval(*n.kids[i], env));
      return apply(fn, std::move(args));
    }
    case NodeKind::Lambda: {
      std::vector<std::string> params;
      for (size_t i = 0; i + 1 < n.kids.size(); ++i) {
        if (n.kids[i]->kind != NodeKind::LParam) continue;
        const Node &pat = *n.kids[i]->kids[0];
        params.push_back(pat.kind == NodeKind::PVar ? pat.text : "");
      }
      return closure(std::move(params), *n.kids.back(), env, "");
    }
    case NodeKind::LetIn: {
      auto inner = std::make_shared<Env>();
      inner->name = n.text;
      inner->parent = env;
      if (n.kids[0]->kids.empty()) {
        inner->value = eval(*n.kids[3], env);
      } else {
        // A local function sees itself, so it may recurse.
        inner->value =
            closure(paramNames(*n.kids[0]), *n.kids[3], inner, n.text);
      }
      return eval(*n.kids[4], inner);
    }
    case NodeKind::If: {
      ValuePtr c = eval(*n.kids[0], env);
      if (c->kind != K::Bool)
        throw MetaError{site_, std::string("'if' needs a bool, found ") +
                                   kindName(c->kind)};
      if (c->b) return eval(*n.kids[1], env);
      if (n.kids.size() > 2 && n.kids[2]->kind != NodeKind::None)
        return eval(*n.kids[2], env);
      return unitValue();
    }
    case NodeKind::Sequence:
      eval(*n.kids[0], env);
      return eval(*n.kids[1], env);
    case NodeKind::Binary:
      return binary(n, env);
    case NodeKind::Neg: {
      ValuePtr v = eval(*n.kids[0], env);
      if (v->kind != K::Int)
        throw MetaError{site_, std::string("'-' needs an integer, found ") +
                                   kindName(v->kind)};
      return intValue(-v->i);
    }
    case NodeKind::Match:
      return match(n, env);
    case NodeKind::Quote:
      return quote(n, env);
    case NodeKind::Splice:
      throw MetaError{site_, "a splice is only allowed inside a quote"};
    default:
      throw MetaError{site_, std::string("'") + syntax::nodeKindName(n.kind) +
                                 "' is not supported in metaprograms yet"};
  }
}

// `match v with | p requires c ensures d -> e ...` (ADR 0035). Arms are
// tried in order; an arm's `requires` must hold for a value that reaches it
// (it is not a guard), and its `ensures` must hold of its value, `result`.
ValuePtr Interpreter::match(const Node &n, const EnvPtr &env) {
  ValuePtr v = eval(*n.kids[0], env);
  auto where = [](const Node &x) {
    return std::to_string(x.loc.line) + ":" + std::to_string(x.loc.column);
  };
  auto describe = [](const ValuePtr &x) -> std::string {
    switch (x->kind) {
      case K::Type: return x->s;
      case K::Int: return std::to_string(x->i);
      case K::Bool: return x->b ? "true" : "false";
      case K::Str: return "\"" + x->s + "\"";
      default: return std::string("a ") + kindName(x->kind);
    }
  };
  if (v->kind == K::Type) {
    const Node &last = *n.kids.back()->kids[0];
    const Node &core = last.kind == NodeKind::PAs ? *last.kids[0] : last;
    bool catchAll = core.kind == NodeKind::PVar && core.text != "int" &&
                    !(host_.named && host_.named(core.text));
    if (!catchAll)
      throw MetaError{site_, "the match at " + where(n) +
                                 " is on a type, and types are an open set, "
                                 "so it must end with a catch-all '| _ -> ...'"};
  }
  for (size_t i = 1; i < n.kids.size(); ++i) {
    const Node &arm = *n.kids[i];
    EnvPtr inner = env;
    if (!matches(*arm.kids[0], v, inner)) continue;
    const Node *contracts = arm.kids.size() > 2 ? arm.kids[2].get() : nullptr;
    auto holds = [&](const Node &c, const EnvPtr &e) {
      ValuePtr ok = eval(*c.kids[0], e);
      if (ok->kind != K::Bool)
        throw MetaError{site_, std::string("an arm's contract must be a "
                                           "bool, found ") +
                                   kindName(ok->kind)};
      return ok->b;
    };
    if (contracts)
      for (const NodePtr &c : contracts->kids)
        if (c->kind == NodeKind::Requires && !holds(*c, inner))
          throw MetaError{site_, describe(v) + " reaches the arm at " +
                                     where(arm) + ", but does not meet its "
                                     "'requires' at " + where(*c)};
    ValuePtr out = eval(*arm.kids[1], inner);
    if (contracts) {
      auto withResult = std::make_shared<Env>();
      withResult->name = "result";
      withResult->value = out;
      withResult->parent = inner;
      for (const NodePtr &c : contracts->kids)
        if (c->kind == NodeKind::Ensures && !holds(*c, withResult))
          throw MetaError{site_, "the arm at " + where(arm) + " gives " +
                                     describe(out) + ", which does not meet "
                                     "its 'ensures' at " + where(*c)};
    }
    return out;
  }
  throw MetaError{site_, "no arm of the match at " + where(n) + " matches " +
                             describe(v)};
}

// Whether the pattern `p` matches `v`, binding its names onto `env`.
bool Interpreter::matches(const Node &p, const ValuePtr &v, EnvPtr &env) {
  auto bindName = [&](const std::string &name, ValuePtr value) {
    auto e = std::make_shared<Env>();
    e->name = name;
    e->value = std::move(value);
    e->parent = env;
    env = e;
  };
  bool isType = v->kind == K::Type;
  TypeInfo info;
  if (isType && host_.info) info = host_.info(v->s);
  switch (p.kind) {
    case NodeKind::PAs:
      if (!matches(*p.kids[0], v, env)) return false;
      bindName(p.text, v);
      return true;
    case NodeKind::PTyped:
      return matches(*p.kids[0], v, env);
    case NodeKind::PVar: {
      if (p.text == "_") return true;
      if (isType && p.text == "int") return info.kind == "int";
      if (host_.named)
        if (std::optional<std::string> t = host_.named(p.text))
          return isType && v->s == *t;
      bindName(p.text, v);
      return true;
    }
    case NodeKind::PLit: {
      if (p.text == "()") return v->kind == K::Unit;
      if (p.text == "true" || p.text == "false")
        return v->kind == K::Bool && v->b == (p.text == "true");
      if (!p.text.empty() && p.text[0] == '"')
        return v->kind == K::Str && v->s == unescape(p.text);
      Node lit;
      lit.kind = NodeKind::IntLit;
      lit.text = p.text;
      ValuePtr k = eval(lit, nullptr);
      return v->kind == K::Int && v->i == k->i;
    }
    case NodeKind::PSlice:
      if (!isType || info.kind != "slice" || !info.element) return false;
      return matches(*p.kids[0], typeValue(*info.element), env);
    case NodeKind::PArray:
      if (!isType || info.kind != "array" || !info.element || !info.length)
        return false;
      return matches(*p.kids[0], typeValue(*info.element), env) &&
             matches(*p.kids[1], intValue(*info.length), env);
    case NodeKind::PCtor: {
      if (!isType)
        throw MetaError{site_, "a metaprogram matches constructors only of "
                               "types for now"};
      if ((p.text == "record" || p.text == "variant") && p.kids.size() == 1) {
        if (info.kind != p.text) return false;
        std::vector<ValuePtr> fs;
        for (const std::string &f : info.fields) fs.push_back(typeValue(f));
        return matches(*p.kids[0], listValue(std::move(fs)), env);
      }
      if (info.generic != p.text || info.args.size() != p.kids.size())
        return false;
      for (size_t i = 0; i < p.kids.size(); ++i)
        if (!matches(*p.kids[i], typeValue(info.args[i]), env)) return false;
      return true;
    }
    default:
      throw MetaError{site_, std::string("this pattern is not supported in "
                                         "metaprograms yet: ") +
                                 syntax::nodeKindName(p.kind)};
  }
}

ValuePtr Interpreter::binary(const Node &n, const EnvPtr &env) {
  const std::string &op = n.text;
  if (op == "&&" || op == "||") {
    ValuePtr a = eval(*n.kids[0], env);
    if (a->kind != K::Bool)
      throw MetaError{site_, "'" + op + "' needs bools"};
    if (op == "&&" ? !a->b : a->b) return a;
    ValuePtr b = eval(*n.kids[1], env);
    if (b->kind != K::Bool)
      throw MetaError{site_, "'" + op + "' needs bools"};
    return b;
  }
  ValuePtr a = eval(*n.kids[0], env);
  ValuePtr b = eval(*n.kids[1], env);
  return binop(op, a, b);
}

ValuePtr Interpreter::binop(const std::string &op, const ValuePtr &a,
                            const ValuePtr &b) {
  if (op == "&&" || op == "||" || op == "==>" || op == "<==>") {
    if (a->kind != K::Bool || b->kind != K::Bool)
      throw MetaError{site_, "'" + op + "' needs bools"};
    if (op == "&&") return boolValue(a->b && b->b);
    if (op == "||") return boolValue(a->b || b->b);
    if (op == "==>") return boolValue(!a->b || b->b);
    return boolValue(a->b == b->b);
  }
  if (op == "=" || op == "<>") {
    bool eq;
    if (a->kind != b->kind)
      throw MetaError{site_, "'" + op + "' compares values of one kind, found " +
                                 kindName(a->kind) + " and " +
                                 kindName(b->kind)};
    switch (a->kind) {
      case K::Int: eq = a->i == b->i; break;
      case K::Bool: eq = a->b == b->b; break;
      case K::Str: case K::Type: eq = a->s == b->s; break;
      case K::Unit: eq = true; break;
      default:
        throw MetaError{site_, std::string("'") + op + "' cannot compare " +
                                   kindName(a->kind)};
    }
    return boolValue(op == "=" ? eq : !eq);
  }
  if (a->kind != K::Int || b->kind != K::Int)
    throw MetaError{site_, "'" + op + "' needs integers in a metaprogram"};
  int64_t x = a->i, y = b->i;
  if (op == "+") return intValue(x + y);
  if (op == "-") return intValue(x - y);
  if (op == "*") return intValue(x * y);
  if (op == "/" || op == "%" || op == "mod") {
    if (y == 0) throw MetaError{site_, "division by zero in a metaprogram"};
    return intValue(op == "/" ? x / y : x % y);
  }
  if (op == "<") return boolValue(x < y);
  if (op == ">") return boolValue(x > y);
  if (op == "<=") return boolValue(x <= y);
  if (op == ">=") return boolValue(x >= y);
  throw MetaError{site_, "the operator '" + op +
                             "' is not supported in metaprograms yet"};
}

ValuePtr Interpreter::apply(const ValuePtr &fnIn, std::vector<ValuePtr> args) {
  ValuePtr fn = fnIn;
  size_t next = 0;
  while (next < args.size()) {
    if (fn->kind != K::Closure && fn->kind != K::Builtin)
      throw MetaError{site_, std::string("cannot apply ") + kindName(fn->kind) +
                                 " to arguments"};
    size_t arity = fn->kind == K::Closure ? fn->params.size()
                                          : metaBuiltins().at(fn->s);
    std::vector<ValuePtr> bound = fn->list;
    while (bound.size() < arity && next < args.size())
      bound.push_back(args[next++]);
    if (bound.size() < arity) {
      Value partial = *fn;
      partial.list = std::move(bound);
      return make(std::move(partial));
    }
    if (fn->kind == K::Builtin) {
      fn = callBuiltin(fn->s, bound, nullptr);
      continue;
    }
    EnvPtr env = fn->env;
    for (size_t i = 0; i < arity; ++i) {
      if (fn->params[i].empty()) continue;
      auto e = std::make_shared<Env>();
      e->name = fn->params[i];
      e->value = bound[i];
      e->parent = env;
      env = e;
    }
    if (!fn->name.empty()) ran_.push_back(fn->name);
    fn = eval(*fn->body, env);
  }
  return fn;
}

NodePtr Interpreter::toCode(const ValuePtr &v, const std::string &who) {
  switch (v->kind) {
  case K::Syntax:
    if (v->syntax && v->syntax->kind != NodeKind::Program)
      return clone(*v->syntax);
    break;
  case K::Str:
    return makeNode(NodeKind::Name, site_, v->s);
  case K::Int:
    if (v->i >= 0)
      return makeNode(NodeKind::IntLit, site_, std::to_string(v->i));
    // A negative integer is the negation of its magnitude, as the
    // parser reads `-5`.
    if (v->i != INT64_MIN) {
      auto neg = makeNode(NodeKind::Neg, site_);
      neg->add(makeNode(NodeKind::IntLit, site_, std::to_string(-v->i)));
      return neg;
    }
    break;
  case K::Bool:
    return makeNode(NodeKind::BoolLit, site_, v->b ? "true" : "false");
  default:
    break;
  }
  throw MetaError{site_,
                  "'" + who + "' cannot make code of " + kindName(v->kind)};
}

const Node *Interpreter::findTypeItem(const ValuePtr &t) {
  if (const Node *item = typeItem(*t))
    return item;
  std::string wanted;
  if (t->kind == K::Str || t->kind == K::Type)
    wanted = t->s;
  else if (t->kind == K::Syntax && t->syntax &&
           (t->syntax->kind == NodeKind::TypeName ||
            t->syntax->kind == NodeKind::Name))
    wanted = t->syntax->text;
  if (wanted.empty())
    return nullptr;
  for (const Node *item : listing_)
    if (item->kind == NodeKind::LetItem && item->text == wanted &&
        item->kids.size() > 3 && item->kids[3]->kind == NodeKind::TypeValue)
      return item;
  return nullptr;
}

ValuePtr Interpreter::rangeOf(const ValuePtr &t) {
  auto bounds = [&](int64_t lo, int64_t hi) {
    return listValue({intValue(lo), intValue(hi)});
  };
  auto ofName = [&](const std::string &n) -> ValuePtr {
    static const std::map<std::string, std::pair<int64_t, int64_t>> ints = {
        {"u8", {0, UINT8_MAX}},          {"u16", {0, UINT16_MAX}},
        {"u32", {0, UINT32_MAX}},        {"i8", {INT8_MIN, INT8_MAX}},
        {"i16", {INT16_MIN, INT16_MAX}}, {"i32", {INT32_MIN, INT32_MAX}},
        {"i64", {INT64_MIN, INT64_MAX}}, {"isize", {INT64_MIN, INT64_MAX}},
    };
    if (auto it = ints.find(n); it != ints.end())
      return bounds(it->second.first, it->second.second);
    // Metaprogram integers are 64-bit and signed (docs/meta.md).
    if (n == "u64" || n == "usize")
      throw MetaError{site_, "'range_of': the upper bound of " + n +
                                 " does not fit a metaprogram integer"};
    return nullptr;
  };
  // A range type's bound, as written: a literal, or a negated one.
  auto bound = [&](const Node &b) -> int64_t {
    ValuePtr v = eval(b, nullptr);
    if (v->kind != K::Int)
      throw MetaError{site_, "'range_of' needs a range with integer bounds"};
    return v->i;
  };
  if (t->kind == K::Syntax && t->syntax) {
    const Node &n = *t->syntax;
    if (n.kind == NodeKind::RangeType && n.kids.size() == 2)
      return bounds(bound(*n.kids[0]), bound(*n.kids[1]));
    if (n.kind == NodeKind::TypeName || n.kind == NodeKind::Name)
      if (ValuePtr v = ofName(n.text))
        return v;
  }
  if (t->kind == K::Str || t->kind == K::Type) {
    if (ValuePtr v = ofName(t->s))
      return v;
    // A type value spells a range as `int{lo..hi}`.
    size_t open = t->s.find('{'), dots = t->s.find(".."),
           close = t->s.rfind('}');
    if (open != std::string::npos && dots != std::string::npos &&
        close == t->s.size() - 1 && open < dots) {
      try {
        return bounds(std::stoll(t->s.substr(open + 1, dots - open - 1)),
                      std::stoll(t->s.substr(dots + 2, close - dots - 2)));
      } catch (...) {
      }
    }
  }
  throw MetaError{site_, "'range_of' needs an integer type with bounds"};
}

ValuePtr Interpreter::callBuiltin(const std::string &name,
                                  const std::vector<ValuePtr> &args,
                                  const Node *) {
  auto needList = [&](const ValuePtr &v) -> const std::vector<ValuePtr> & {
    if (v->kind != K::List)
      throw MetaError{site_, "'" + name + "' needs a list, found " +
                                 kindName(v->kind)};
    return v->list;
  };
  if (name == "map") {
    std::vector<ValuePtr> out;
    for (const ValuePtr &x : needList(args[1]))
      out.push_back(apply(args[0], {x}));
    return listValue(std::move(out));
  }
  if (name == "fold") {
    ValuePtr acc = args[1];
    for (const ValuePtr &x : needList(args[2])) acc = apply(args[0], {acc, x});
    return acc;
  }
  if (name == "length")
    return intValue(static_cast<int64_t>(needList(args[0]).size()));
  if (name == "nth") {
    const std::vector<ValuePtr> &xs = needList(args[0]);
    if (args[1]->kind != K::Int)
      throw MetaError{site_, std::string("'nth' needs an integer index, "
                                         "found ") +
                                 kindName(args[1]->kind)};
    if (args[1]->i < 0 || static_cast<size_t>(args[1]->i) >= xs.size())
      throw MetaError{site_, "'nth' index " + std::to_string(args[1]->i) +
                                 " is outside a list of " +
                                 std::to_string(xs.size())};
    return xs[static_cast<size_t>(args[1]->i)];
  }
  if (name == "zip") {
    const std::vector<ValuePtr> &xs = needList(args[0]);
    const std::vector<ValuePtr> &ys = needList(args[1]);
    // Unequal lengths are a mistake in a generator, such as a domain list
    // with one entry too few, so they are an error rather than truncated.
    if (xs.size() != ys.size())
      throw MetaError{site_, "'zip' needs lists of one length, found " +
                                 std::to_string(xs.size()) + " and " +
                                 std::to_string(ys.size())};
    std::vector<ValuePtr> out;
    for (size_t i = 0; i < xs.size(); ++i)
      out.push_back(listValue({xs[i], ys[i]}));
    return listValue(std::move(out));
  }
  if (name == "range") {
    if (args[0]->kind != K::Int || args[0]->i < 0)
      throw MetaError{site_, "'range' needs a non-negative integer"};
    std::vector<ValuePtr> out;
    for (int64_t i = 0; i < args[0]->i; ++i) {
      tick(Node{});
      out.push_back(intValue(i));
    }
    return listValue(std::move(out));
  }
  if (name == "reverse") {
    std::vector<ValuePtr> out = needList(args[0]);
    std::reverse(out.begin(), out.end());
    return listValue(std::move(out));
  }
  if (name == "filter") {
    std::vector<ValuePtr> out;
    for (const ValuePtr &x : needList(args[1])) {
      ValuePtr keep = apply(args[0], {x});
      if (keep->kind != K::Bool)
        throw MetaError{site_, std::string("'filter' needs a function that "
                                           "returns a bool, found ") +
                                   kindName(keep->kind)};
      if (keep->b)
        out.push_back(x);
    }
    return listValue(std::move(out));
  }
  if (name == "product") {
    // The cartesian product of a list of lists, the first list varying
    // slowest: every combination of one element from each.
    std::vector<std::vector<ValuePtr>> rows = {{}};
    for (const ValuePtr &d : needList(args[0])) {
      std::vector<std::vector<ValuePtr>> next;
      for (const std::vector<ValuePtr> &row : rows)
        for (const ValuePtr &x : needList(d)) {
          tick(Node{});
          next.push_back(row);
          next.back().push_back(x);
        }
      rows = std::move(next);
    }
    std::vector<ValuePtr> out;
    for (std::vector<ValuePtr> &row : rows)
      out.push_back(listValue(std::move(row)));
    return listValue(std::move(out));
  }
  if (name == "fields") {
    const Node *item = typeItem(*args[0]);
    const Node *record =
        item ? item->kids[3]->kids[0].get() : nullptr;
    if (!record || record->kind != NodeKind::RecordType)
      throw MetaError{site_, "'fields' needs a record type"};
    // Fields are only visible once every type they mention is defined
    // (design.md, "Stages").
    std::vector<std::string> types;
    collectTypeNames(*record, types);
    for (const std::string &t : types)
      if (!isTypeDefined_(t)) throw Deferred{t};
    std::vector<ValuePtr> out;
    for (const NodePtr &f : record->kids) out.push_back(strValue(f->text));
    return listValue(std::move(out));
  }
  if (name == "range_of")
    return rangeOf(args[0]);
  if (name == "constructors") {
    const Node *item = findTypeItem(args[0]);
    const Node *variants = item && !item->kids[3]->kids.empty()
                               ? item->kids[3]->kids[0].get()
                               : nullptr;
    if (!variants || variants->kind != NodeKind::Variants)
      throw MetaError{site_, "'constructors' needs a variant type"};
    std::vector<ValuePtr> out;
    for (const NodePtr &c : variants->kids)
      out.push_back(strValue(c->text));
    return listValue(std::move(out));
  }
  // A core builtin, as a `where` predicate's operators expand to.
  static const std::map<std::string, std::string> ops = {
      {"eq", "="},  {"ne", "<>"},  {"lt", "<"},  {"gt", ">"},
      {"le", "<="}, {"ge", ">="},  {"add", "+"}, {"sub", "-"},
      {"mul", "*"}, {"div", "/"},  {"rem", "%"}, {"and", "&&"},
      {"or", "||"}, {"implies", "==>"},          {"iff", "<==>"},
  };
  if (auto op = ops.find(name); op != ops.end())
    return binop(op->second, args[0], args[1]);
  if (name == "size_of" || name == "type_kind" || name == "element" ||
      name == "field_types" || name == "type_args") {
    if (args[0]->kind != K::Type)
      throw MetaError{site_, "'" + name + "' needs a type, found " +
                                 kindName(args[0]->kind)};
    if (!host_.info)
      throw MetaError{site_, "'" + name + "' is only available in types and "
                             "constraints"};
    const std::string &t = args[0]->s;
    TypeInfo info = host_.info(t);
    auto types = [](const std::vector<std::string> &ts) {
      std::vector<ValuePtr> out;
      for (const std::string &x : ts) out.push_back(typeValue(x));
      return listValue(std::move(out));
    };
    if (name == "type_kind") return strValue(info.kind);
    if (name == "field_types") {
      if (info.kind != "record" && info.kind != "variant")
        throw MetaError{site_, "'field_types' needs a record or a variant, "
                               "found " + t};
      return types(info.fields);
    }
    if (name == "type_args") return types(info.args);
    if (name == "element") {
      if (!info.element)
        throw MetaError{site_, "'element' needs an array or a slice, found " +
                                   t};
      return typeValue(*info.element);
    }
    if (info.size) return intValue(*info.size);
    throw MetaError{site_, "the type " + t + " has no fixed size"};
  }
  if (name == "name") {
    const Value &v = *args[0];
    if (v.kind == K::Str) return args[0];
    if (v.kind == K::Type) return strValue(v.s);
    if (v.kind == K::Syntax && v.syntax &&
        (v.syntax->kind == NodeKind::LetItem ||
         v.syntax->kind == NodeKind::Name ||
         v.syntax->kind == NodeKind::TypeName))
      return strValue(v.syntax->text);
    throw MetaError{site_, std::string("'name' needs an item or a name, found ") +
                               kindName(v.kind)};
  }
  if (name == "concat") {
    const Value &a = *args[0], &b = *args[1];
    if (a.kind == K::List && b.kind == K::List) {
      std::vector<ValuePtr> out = a.list;
      out.insert(out.end(), b.list.begin(), b.list.end());
      return listValue(std::move(out));
    }
    auto str = [&](const Value &v) {
      if (v.kind == K::Str) return v.s;
      if (v.kind == K::Int) return std::to_string(v.i);
      throw MetaError{site_, std::string("'concat' needs strings or lists, "
                                         "found ") +
                                 kindName(v.kind)};
    };
    return strValue(str(a) + str(b));
  }
  auto needSyntax = [&](const ValuePtr &v) -> const Node & {
    if (v->kind != K::Syntax || !v->syntax)
      throw MetaError{site_, "'" + name + "' needs syntax, found " +
                                 kindName(v->kind)};
    return *v->syntax;
  };
  auto needComment = [&](const ValuePtr &v) -> const Node & {
    const Node &n = needSyntax(v);
    if (n.kind != NodeKind::Comment)
      throw MetaError{site_, "'" + name + "' needs a comment, found " +
                                 syntax::nodeKindName(n.kind)};
    return n;
  };
  if (name == "listing") {
    std::vector<ValuePtr> out;
    for (const Node *item : listing_) out.push_back(syntaxValue(clone(*item)));
    if (program_)
      for (const NodePtr &c : program_->comments)
        out.push_back(syntaxValue(clone(*c)));
    return listValue(std::move(out));
  }
  if (name == "comments") {
    std::vector<ValuePtr> out;
    for (const NodePtr &c : needSyntax(args[0]).comments)
      out.push_back(syntaxValue(clone(*c)));
    return listValue(std::move(out));
  }
  if (name == "doc") return strValue(syntax::docText(needSyntax(args[0])));
  if (name == "text") {
    if (args[0]->kind == K::Str) return args[0];
    const Node &n = needSyntax(args[0]);
    if (n.kind == NodeKind::StringLit) return strValue(unescape(n.text));
    return strValue(needComment(args[0]).text);
  }
  if (name == "style") return strValue(syntax::commentStyle(needComment(args[0])));
  if (name == "place") return strValue(syntax::commentPlace(needComment(args[0])));
  if (name == "kind")
    return strValue(syntax::nodeKindName(needSyntax(args[0]).kind));
  // A goal is the lemma it is the goal of (ADR 0036, step 6): its
  // hypotheses are its `requires`, its conclusion its `ensures`.
  auto needGoal = [&](const ValuePtr &v) -> const Node & {
    const Node &n = needSyntax(v);
    if (n.kind != NodeKind::LetItem || n.kids.size() < 3)
      throw MetaError{site_, "'" + name + "' needs a goal, found " +
                                 syntax::nodeKindName(n.kind)};
    return n;
  };
  if (name == "hypotheses" || name == "conclusion") {
    const Node &g = needGoal(args[0]);
    NodeKind want = name == "hypotheses" ? NodeKind::Requires : NodeKind::Ensures;
    std::vector<ValuePtr> out;
    NodePtr all;
    // Clauses joined in the form they are written in. Before expansion
    // (a tactic's goal) that is the operator `&&`; once operators have
    // expanded (an item from `listing`) it is a call of `and`, so code
    // that walks the conclusion sees one form throughout.
    bool expanded = !hasBinary(*g.kids[2]) && hasPreludeCall(*g.kids[2]);
    for (const NodePtr &c : g.kids[2]->kids) {
      if (c->kind != want || c->kids.empty()) continue;
      out.push_back(syntaxValue(clone(*c->kids[0])));
      if (!all) {
        all = clone(*c->kids[0]);
      } else if (expanded) {
        auto both = makeNode(NodeKind::Apply, c->loc);
        both->add(makeNode(NodeKind::Name, c->loc, "and"))->flags = "prelude";
        both->add(std::move(all));
        both->add(clone(*c->kids[0]));
        all = std::move(both);
      } else {
        auto both = makeNode(NodeKind::Binary, c->loc, "&&");
        both->add(std::move(all));
        both->add(clone(*c->kids[0]));
        all = std::move(both);
      }
    }
    if (name == "hypotheses") return listValue(std::move(out));
    if (!all) all = makeNode(NodeKind::BoolLit, g.loc, "true");
    return syntaxValue(std::move(all));
  }
  if (name == "params") {
    std::vector<ValuePtr> out;
    for (const NodePtr &p : needGoal(args[0]).kids[0]->kids)
      if (p->kind == NodeKind::Param) out.push_back(strValue(p->text));
    return listValue(std::move(out));
  }
  // A function's signature (ADR 0056): the type of each parameter, and
  // the return type, as written.
  if (name == "param_types") {
    std::vector<ValuePtr> out;
    for (const NodePtr &p : needGoal(args[0]).kids[0]->kids) {
      if (p->kind != NodeKind::Param)
        continue;
      const Node *annot = p->kids.empty() ? nullptr : p->kids[0].get();
      if (!annot || annot->kind != NodeKind::Annot || annot->kids.size() < 2)
        throw MetaError{site_, "'param_types': the parameter '" + p->text +
                                   "' has no type"};
      out.push_back(syntaxValue(clone(*annot->kids[1])));
    }
    return listValue(std::move(out));
  }
  if (name == "return_type") {
    const Node &g = needGoal(args[0]);
    const Node &ret = *g.kids[1];
    if (ret.kind != NodeKind::RetAnnot || ret.kids.empty() ||
        ret.kids[0]->kind != NodeKind::Annot || ret.kids[0]->kids.size() < 2)
      throw MetaError{site_, "'return_type': '" + g.text +
                                 "' has no return type written"};
    return syntaxValue(clone(*ret.kids[0]->kids[1]));
  }
  if (name == "subst") {
    // No shadowing in Pia (ADR 0022), so every free occurrence of the
    // name is the one meant, and a plain replacement is capture-free.
    const Node &e = needSyntax(args[0]);
    if (args[1]->kind != K::Str)
      throw MetaError{site_, std::string("'subst' needs a name as a string, "
                                         "found ") +
                                 kindName(args[1]->kind)};
    const std::string &from = args[1]->s;
    NodePtr to = toCode(args[2], "subst");
    NodePtr out = clone(e);
    std::function<void(NodePtr &)> walk = [&](NodePtr &n) {
      if (n->kind == NodeKind::Name && n->text == from) {
        n = clone(*to);
        return;
      }
      for (NodePtr &k : n->kids)
        walk(k);
    };
    walk(out);
    return syntaxValue(std::move(out));
  }
  if (name == "children") {
    std::vector<ValuePtr> out;
    for (const NodePtr &k : needSyntax(args[0]).kids)
      out.push_back(syntaxValue(clone(*k)));
    return listValue(std::move(out));
  }
  if (name == "op") {
    const Node &n = needSyntax(args[0]);
    if (n.kind == NodeKind::Binary || n.kind == NodeKind::Name)
      return strValue(n.text);
    if (n.kind == NodeKind::Apply && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::Name)
      return strValue(n.kids[0]->text);
    return strValue("");
  }
  if (name == "make_call") {
    auto code = [&](const ValuePtr &v) { return toCode(v, "make_call"); };
    if (args[1]->kind != K::List)
      throw MetaError{site_, std::string("'make_call' needs a list of "
                                         "arguments, found ") +
                                 kindName(args[1]->kind)};
    NodePtr head = code(args[0]);
    if (args[1]->list.empty()) return syntaxValue(std::move(head));
    auto call = makeNode(NodeKind::Apply, site_);
    call->add(std::move(head));
    for (const ValuePtr &a : args[1]->list) call->add(code(a));
    return syntaxValue(std::move(call));
  }
  if (name == "with_doc") {
    if (args[0]->kind != K::Str)
      throw MetaError{site_, std::string("'with_doc' needs a string, found ") +
                                 kindName(args[0]->kind)};
    NodePtr copy = clone(needSyntax(args[1]));
    Node *target = copy.get();
    if (target->kind == NodeKind::Program) {
      if (target->kids.empty())
        throw MetaError{site_, "'with_doc' needs code to document"};
      target = target->kids[0].get();
    }
    if (target->kind == NodeKind::Comment)
      throw MetaError{site_, "'with_doc' needs code to document"};
    target->comments.insert(
        target->comments.begin(),
        syntax::makeComment(site_, args[0]->s, "doc", "leading"));
    return syntaxValue(std::move(copy));
  }
  if (name == "redefine") {
    // Marks each definition in the code as replacing the environment's
    // definition of that name. The REPL verifies the replacement like a
    // :redef cell before it commits it (docs/repl.md).
    if (!live_)
      throw MetaError{site_, "'redefine' is part of Pia.Live, which only the "
                             "REPL provides"};
    NodePtr copy = clone(needSyntax(args[0]));
    std::vector<Node *> items;
    if (copy->kind == NodeKind::Program)
      for (NodePtr &k : copy->kids) items.push_back(k.get());
    else
      items.push_back(copy.get());
    for (Node *item : items) {
      if (item->kind != NodeKind::LetItem)
        throw MetaError{site_, "'redefine' needs definitions, found " +
                                   std::string(syntax::nodeKindName(item->kind))};
      item->flags += item->flags.empty() ? "redef" : " redef";
    }
    return syntaxValue(std::move(copy));
  }
  if (name == "fail") {
    if (args[0]->kind != K::Str)
      throw MetaError{site_, std::string("'fail' needs a string, found ") +
                                 kindName(args[0]->kind)};
    throw MetaError{site_, args[0]->s};
  }
  throw MetaError{site_, "unknown builtin '" + name + "'"};
}

// Builds the code a quote stands for (docs/meta.md, "Quotes and splices").
class QuoteBuilder {
 public:
  QuoteBuilder(Interpreter &in, const EnvPtr &env) : in_(in), env_(env) {}

  NodePtr build(const Node &quote) {
    for (const NodePtr &k : quote.kids) collectBinders(*k, /*top=*/true);
    if (quote.kids.size() == 1) return copy(*quote.kids[0], false);
    auto items = makeNode(NodeKind::Program, in_.site_);
    for (const NodePtr &k : quote.kids) items->add(copy(*k, false));
    return items;
  }

 private:
  // Names the quote binds get fresh names, so they cannot capture names in
  // spliced code. Item names stay, since they are meant to be seen.
  void collectBinders(const Node &n, bool top) {
    if (n.kind == NodeKind::Splice) return;
    bool binds = n.kind == NodeKind::LetIn || n.kind == NodeKind::Param ||
                 n.kind == NodeKind::PVar || n.kind == NodeKind::PAs ||
                 n.kind == NodeKind::Binder ||
                 n.kind == NodeKind::RangeBinder ||
                 (n.kind == NodeKind::LetItem && !top);
    if (binds && !n.text.empty() && n.text[0] != '$' &&
        !renamed_.count(n.text))
      renamed_[n.text] = n.text + "#" + std::to_string(++in_.fresh_);
    // A theory's or model's members are items, meant to be seen, so their
    // names stay; their parameters and binders are renamed (ADR 0036).
    bool members = n.kind == NodeKind::Theory || n.kind == NodeKind::Model;
    for (const NodePtr &k : n.kids) collectBinders(*k, members);
  }

  ValuePtr var(const std::string &spliced) {
    syntax::Node name;
    name.kind = NodeKind::Name;
    name.text = spliced.substr(1);
    return in_.lookup(name, env_);
  }

  std::string text(const ValuePtr &v) {
    if (v->kind == K::Str) return v->s;
    if (v->kind == K::Syntax && v->syntax &&
        (v->syntax->kind == NodeKind::Name ||
         v->syntax->kind == NodeKind::TypeName ||
         v->syntax->kind == NodeKind::LetItem ||
         v->syntax->kind == NodeKind::PVar))
      return v->syntax->text;
    throw MetaError{in_.site_, std::string("cannot splice ") +
                                   kindName(v->kind) + " as a name"};
  }

  NodePtr fromValue(const ValuePtr &v, bool typePos) {
    syntax::SourceLoc site = in_.site_;
    switch (v->kind) {
      case K::Syntax: {
        const Node &n = *v->syntax;
        if (n.kind == NodeKind::Program)
          throw MetaError{site, "a list of items can only be spliced at the "
                                "top level"};
        if (n.kind == NodeKind::Comment)
          throw MetaError{site, "a comment cannot be spliced into code; use "
                                "'with_doc' to document generated code"};
        if (typePos && n.kind == NodeKind::LetItem)
          return makeNode(NodeKind::TypeName, site, n.text);
        return clone(n);
      }
      case K::Str:
        return makeNode(typePos ? NodeKind::TypeName : NodeKind::Name, site,
                        v->s);
      case K::Int: {
        if (v->i >= 0)
          return makeNode(NodeKind::IntLit, site, std::to_string(v->i));
        auto neg = makeNode(NodeKind::Neg, site);
        neg->add(makeNode(NodeKind::IntLit, site, std::to_string(-v->i)));
        return neg;
      }
      case K::Bool:
        return makeNode(NodeKind::BoolLit, site, v->b ? "true" : "false");
      case K::Unit:
        return makeNode(NodeKind::Unit, site);
      default:
        throw MetaError{site, std::string("cannot splice ") +
                                  kindName(v->kind) + " into code"};
    }
  }
  // A quote's comments come along, at the expansion site (ADR 0029).
  // Hygiene never looks inside them.
  void copyComments(const Node &from, Node &to, bool front) {
    std::vector<NodePtr> cs;
    for (const NodePtr &c : from.comments) {
      cs.push_back(clone(*c));
      cs.back()->loc = in_.site_;
    }
    to.comments.insert(front ? to.comments.begin() : to.comments.end(),
                       std::make_move_iterator(cs.begin()),
                       std::make_move_iterator(cs.end()));
  }

  NodePtr copy(const Node &n, bool typePos) {
    syntax::SourceLoc site = in_.site_;
    if (n.kind == NodeKind::Splice) {
      NodePtr out;
      if (n.text.rfind("$!", 0) == 0) {
        out = makeNode(typePos ? NodeKind::TypeName : NodeKind::Name, site,
                       n.text.substr(2));
      } else {
        ValuePtr v = n.text.empty() ? in_.eval(*n.kids[0], env_) : var(n.text);
        out = fromValue(v, typePos);
      }
      // A comment on the splice moves to the code that replaces it.
      copyComments(n, *out, /*front=*/true);
      return out;
    }
    if (n.kind == NodeKind::Quote)
      throw MetaError{site, "nested quotes are not supported yet"};
    auto out = makeNode(n.kind, site, n.text);
    out->flags = n.flags;
    copyComments(n, *out, /*front=*/false);
    if (n.kind == NodeKind::PSplice) {
      out->kind = NodeKind::PVar;
      out->text = n.text.rfind("$!", 0) == 0 ? n.text.substr(2)
                                             : text(var(n.text));
    } else if (hasBinderText(n.kind) && n.text.rfind("$!", 0) == 0) {
      out->text = n.text.substr(2);
    } else if (hasBinderText(n.kind) && !n.text.empty() && n.text[0] == '$') {
      out->text = text(var(n.text));
    } else if (n.kind != NodeKind::Field && n.kind != NodeKind::FieldInit &&
               n.kind != NodeKind::PField &&
               (hasBinderText(n.kind) || n.kind == NodeKind::Name)) {
      auto r = renamed_.find(n.text);
      if (r != renamed_.end()) {
        out->text = r->second;
      } else if (n.kind == NodeKind::Name) {
        // A free name means what it means where the metaprogram is defined:
        // a core builtin, or a top-level definition, never a local at the
        // expansion site.
        out->flags = Interpreter::isCoreBuiltin(n.text) ? "prelude" : "toplevel";
      }
    }
    bool members = n.kind == NodeKind::Theory || n.kind == NodeKind::Model;
    for (size_t i = 0; i < n.kids.size(); ++i) {
      // `$xs` among a theory's or model's members splices a list of them.
      if (members && n.kids[i]->kind == NodeKind::Splice) {
        const Node &sp = *n.kids[i];
        ValuePtr v = sp.text.empty() ? in_.eval(*sp.kids[0], env_)
                                     : var(sp.text);
        std::vector<ValuePtr> parts;
        if (v->kind == K::List)
          parts = v->list;
        else
          parts.push_back(v);
        for (const ValuePtr &part : parts) {
          if (part->kind != K::Syntax || !part->syntax)
            throw MetaError{site, std::string("a theory's or model's members "
                                              "are items, not ") +
                                      kindName(part->kind)};
          const Node &p = *part->syntax;
          if (p.kind == NodeKind::Program)
            for (const NodePtr &k : p.kids) out->add(clone(*k));
          else
            out->add(clone(p));
        }
        continue;
      }
      out->add(copy(*n.kids[i], isTypePosition(n.kind, i)));
    }
    return out;
  }

  Interpreter &in_;
  EnvPtr env_;
  std::map<std::string, std::string> renamed_;
};

ValuePtr Interpreter::quote(const Node &n, const EnvPtr &env) {
  return syntaxValue(QuoteBuilder(*this, env).build(n));
}

}  // namespace pia::meta
