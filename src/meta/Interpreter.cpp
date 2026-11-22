#include "meta/Interpreter.h"

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
  static const std::map<std::string, size_t> table = {
      {"map", 2},   {"fold", 3},   {"fields", 1},
      {"name", 1},  {"concat", 2}, {"length", 1},
      // Comments and literate programs (ADR 0029).
      {"listing", 1}, {"comments", 1}, {"doc", 1},   {"text", 1},
      {"style", 1},   {"place", 1},    {"kind", 1},  {"with_doc", 2},
      {"fail", 1},
      // Pia.Live, in the REPL only (ADR 0031).
      {"redefine", 1},
      // Types, in type-level metaprograms (ADR 0035).
      {"size_of", 1},
      // The core builtins that operators expand to, so a `where`
      // predicate, which is expanded code, can run (ADR 0035).
      {"eq", 2}, {"ne", 2}, {"lt", 2}, {"gt", 2}, {"le", 2}, {"ge", 2},
      {"add", 2}, {"sub", 2}, {"mul", 2}, {"div", 2}, {"rem", 2},
      {"and", 2}, {"or", 2}, {"implies", 2}, {"iff", 2},
  };
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
    case NodeKind::TypeApp: case NodeKind::UnionType: case NodeKind::TypeInst:
      return true;
    default: return false;
  }
}

// Kinds whose text is a binder name, which may be spliced (`let $n`).
bool hasBinderText(NodeKind k) {
  switch (k) {
    case NodeKind::LetItem: case NodeKind::LetIn: case NodeKind::Param:
    case NodeKind::PVar: case NodeKind::Binder: case NodeKind::RangeBinder:
    case NodeKind::Field: case NodeKind::FieldInit: case NodeKind::PField:
    case NodeKind::QuotedDecl:
      return true;
    default:
      return false;
  }
}

}  // namespace

bool Interpreter::isCoreBuiltin(const std::string &name) {
  static const std::set<std::string> names = {
      "add", "sub", "add_sat", "sub_sat", "mul", "div", "rem",
      "eq",  "ne",  "lt",      "gt",      "le",  "ge",
      "and", "or",  "implies", "iff",     "len", "old",
      "band", "bor", "bxor", "bnot", "shl", "shr", "abort",
  };
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
  throw MetaError{site_, "unknown name '" + n.text + "' in a metaprogram"};
}

ValuePtr Interpreter::eval(const Node &n, const EnvPtr &env) {
  tick(n);
  switch (n.kind) {
    case NodeKind::IntLit: {
      std::string digits;
      for (char c : n.text) {
        if (c == '_') continue;
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
    case NodeKind::Quote:
      return quote(n, env);
    case NodeKind::Splice:
      throw MetaError{site_, "a splice is only allowed inside a quote"};
    default:
      throw MetaError{site_, std::string("'") + syntax::nodeKindName(n.kind) +
                                 "' is not supported in metaprograms yet"};
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
  // A core builtin, as a `where` predicate's operators expand to.
  static const std::map<std::string, std::string> ops = {
      {"eq", "="},  {"ne", "<>"},  {"lt", "<"},  {"gt", ">"},
      {"le", "<="}, {"ge", ">="},  {"add", "+"}, {"sub", "-"},
      {"mul", "*"}, {"div", "/"},  {"rem", "%"}, {"and", "&&"},
      {"or", "||"}, {"implies", "==>"},          {"iff", "<==>"},
  };
  if (auto op = ops.find(name); op != ops.end())
    return binop(op->second, args[0], args[1]);
  if (name == "size_of") {
    if (args[0]->kind != K::Type)
      throw MetaError{site_, std::string("'size_of' needs a type, found ") +
                                 kindName(args[0]->kind)};
    if (!host_.sizeOf)
      throw MetaError{site_, "'size_of' is only available in types and "
                             "constraints"};
    if (std::optional<int64_t> n = host_.sizeOf(args[0]->s))
      return intValue(*n);
    throw MetaError{site_, "the type " + args[0]->s + " has no fixed size"};
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
                 n.kind == NodeKind::PVar || n.kind == NodeKind::Binder ||
                 n.kind == NodeKind::RangeBinder ||
                 (n.kind == NodeKind::LetItem && !top);
    if (binds && !n.text.empty() && n.text[0] != '$' &&
        !renamed_.count(n.text))
      renamed_[n.text] = n.text + "#" + std::to_string(++in_.fresh_);
    for (const NodePtr &k : n.kids) collectBinders(*k, false);
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
    for (size_t i = 0; i < n.kids.size(); ++i)
      out->add(copy(*n.kids[i], isTypePosition(n.kind, i)));
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
