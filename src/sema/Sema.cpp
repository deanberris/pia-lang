#include "sema/Sema.h"

#include <algorithm>
#include <cctype>
#include <set>

#include "dialect/PiaDialect.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/IR/BuiltinTypes.h"

namespace pia::sema {

using syntax::Node;
using syntax::NodeKind;

namespace {

constexpr unsigned kWidth = 128;

llvm::APInt signedMin(unsigned bits) {
  return llvm::APInt::getSignedMinValue(bits).sext(kWidth);
}
llvm::APInt signedMax(unsigned bits) {
  return llvm::APInt::getSignedMaxValue(bits).sext(kWidth);
}
llvm::APInt unsignedMax(unsigned bits) {
  return llvm::APInt::getMaxValue(bits).zext(kWidth);
}

const char *const kSuffixes[] = {"usize", "isize", "u8",  "u16", "u32",
                                 "u64",   "i8",    "i16", "i32", "i64"};

}  // namespace

std::optional<IntLiteral> parseIntLiteral(std::string_view s) {
  IntLiteral lit;
  for (const char *suffix : kSuffixes) {
    std::string_view sv(suffix);
    if (s.size() > sv.size() && s.substr(s.size() - sv.size()) == sv) {
      // `0x1u8` has no hex digit 'u', so the suffix check is safe for hex
      // except for spellings like 0xe8 (which has no 'u' or 'i' either).
      lit.suffix = suffix;
      s.remove_suffix(sv.size());
      break;
    }
  }
  unsigned radix = 10;
  if (s.size() > 2 && s[0] == '0' &&
      (s[1] == 'x' || s[1] == 'o' || s[1] == 'b')) {
    radix = s[1] == 'x' ? 16 : s[1] == 'o' ? 8 : 2;
    s.remove_prefix(2);
  }
  std::string digits;
  for (char c : s)
    if (c != '_') digits.push_back(c);
  if (digits.empty()) return std::nullopt;
  llvm::APInt v(kWidth, 0);
  llvm::APInt base(kWidth, radix);
  for (char c : digits) {
    unsigned d;
    if (std::isdigit(static_cast<unsigned char>(c)))
      d = c - '0';
    else if (std::isxdigit(static_cast<unsigned char>(c)))
      d = std::tolower(static_cast<unsigned char>(c)) - 'a' + 10;
    else
      return std::nullopt;
    if (d >= radix) return std::nullopt;
    v = v * base + llvm::APInt(kWidth, d);
    if (v.ugt(unsignedMax(64))) return std::nullopt;  // larger than any type
  }
  lit.value = v;
  return lit;
}

std::string typeName(mlir::Type t) {
  if (!t) return "?";
  if (mlir::isa<mlir::NoneType>(t)) return "unit";
  if (t.isInteger(1)) return "bool";
  if (mlir::isa<mlir::IndexType>(t)) return "index";
  if (auto it = mlir::dyn_cast<IntType>(t)) {
    llvm::APInt lo = it.getLo().sextOrTrunc(kWidth);
    llvm::APInt hi = it.getHi().sextOrTrunc(kWidth);
    for (unsigned bits : {8u, 16u, 32u, 64u}) {
      if (lo.isZero() && hi == unsignedMax(bits))
        return bits == 64 ? "usize" : "u" + std::to_string(bits);
      if (lo == signedMin(bits) && hi == signedMax(bits))
        return "i" + std::to_string(bits);
    }
    return "int{" + llvm::toString(lo, 10, true) + ".." +
           llvm::toString(hi, 10, true) + "}";
  }
  if (auto a = mlir::dyn_cast<ArrayType>(t))
    return "[" + typeName(a.getElementType()) + "; " +
           std::to_string(a.getLength()) + "]";
  if (auto s = mlir::dyn_cast<SliceType>(t))
    return "[" + typeName(s.getElementType()) + "]";
  if (auto r = mlir::dyn_cast<RecordType>(t)) return r.getName().str();
  std::string out;
  llvm::raw_string_ostream os(out);
  t.print(os);
  return out;
}

bool hasModifier(std::string_view modifiers, std::string_view word) {
  size_t pos = 0;
  while (pos < modifiers.size()) {
    size_t end = modifiers.find(' ', pos);
    if (end == std::string_view::npos) end = modifiers.size();
    if (modifiers.substr(pos, end - pos) == word) return true;
    pos = end + 1;
  }
  return false;
}

mlir::Type TypeResolver::builtin(std::string_view name) {
  auto make = [&](llvm::APInt lo, llvm::APInt hi) -> mlir::Type {
    return IntType::get(&ctx_, lo, hi);
  };
  if (name == "usize") return make(llvm::APInt(kWidth, 0), unsignedMax(64));
  if (name == "isize") return make(signedMin(64), signedMax(64));
  for (unsigned bits : {8u, 16u, 32u, 64u}) {
    std::string b = std::to_string(bits);
    if (name == "u" + b) return make(llvm::APInt(kWidth, 0), unsignedMax(bits));
    if (name == "i" + b) return make(signedMin(bits), signedMax(bits));
  }
  if (name == "bool") return boolType();
  if (name == "unit") return unitType();
  return {};
}

mlir::Type TypeResolver::boolType() { return mlir::IntegerType::get(&ctx_, 1); }
mlir::Type TypeResolver::unitType() { return mlir::NoneType::get(&ctx_); }
bool TypeResolver::isUnit(mlir::Type t) const {
  return t && mlir::isa<mlir::NoneType>(t);
}

std::optional<llvm::APInt> TypeResolver::constantBound(const Node &n) {
  if (n.kind == NodeKind::IntLit) {
    auto lit = parseIntLiteral(n.text);
    if (lit && lit->suffix.empty()) return lit->value;
  } else if (n.kind == NodeKind::Neg && n.kids.size() == 1 &&
             n.kids[0]->kind == NodeKind::IntLit) {
    auto lit = parseIntLiteral(n.kids[0]->text);
    if (lit && lit->suffix.empty()) return -lit->value;
  }
  diags_.error(n.loc, "a range bound must be an integer literal for now");
  return std::nullopt;
}

mlir::Type TypeResolver::resolve(const Node &type) {
  switch (type.kind) {
    case NodeKind::TypeName: {
      for (auto it = typeScopes_.rbegin(); it != typeScopes_.rend(); ++it)
        if (auto p = it->find(type.text); p != it->end()) return p->second;
      if (mlir::Type t = builtin(type.text)) return t;
      if (mlir::Type t = named(type.text)) return t;
      if (const Generic *g = generic(type.text)) {
        diags_.error(type.loc, "'" + type.text + "' is generic: it takes " +
                                   std::to_string(g->params.size()) +
                                   " type argument" +
                                   (g->params.size() == 1 ? "" : "s") +
                                   ", as in '" + type.text + " u8'");
        return {};
      }
      diags_.error(type.loc, "unknown type '" + type.text + "'");
      return {};
    }
    case NodeKind::TypeApp: {
      const Node &head = *type.kids[0];
      if (head.kind != NodeKind::TypeName || !generic(head.text)) {
        diags_.error(head.loc, "only a generic type can take type arguments");
        return {};
      }
      llvm::SmallVector<mlir::Type> args;
      for (size_t i = 1; i < type.kids.size(); ++i) {
        mlir::Type a = resolve(*type.kids[i]);
        if (!a) return {};
        args.push_back(a);
      }
      return instantiate(head.text, args, type.loc);
    }
    case NodeKind::UnitType:
      return unitType();
    case NodeKind::RangeType: {
      if (type.text != "int") {
        diags_.error(type.loc, "only 'int' takes a range, as in int{0..255}");
        return {};
      }
      auto lo = constantBound(*type.kids[0]);
      auto hi = constantBound(*type.kids[1]);
      if (!lo || !hi) return {};
      if (lo->sgt(*hi)) {
        diags_.error(type.loc, "the range's lower bound exceeds its upper bound");
        return {};
      }
      if (lo->slt(signedMin(64)) || hi->sgt(unsignedMax(64))) {
        diags_.error(type.loc, "a range must lie within [-2^63, 2^64 - 1]");
        return {};
      }
      return IntType::get(&ctx_, *lo, *hi);
    }
    case NodeKind::ArrayType: {
      mlir::Type elem = resolve(*type.kids[0]);
      if (!elem) return {};
      const Node &len = *type.kids[1];
      auto lit = len.kind == NodeKind::IntLit ? parseIntLiteral(len.text)
                                              : std::nullopt;
      if (!lit || !lit->suffix.empty()) {
        diags_.error(len.loc,
                     "an array length must be an integer literal for now");
        return {};
      }
      return ArrayType::get(&ctx_, lit->value.getZExtValue(), elem);
    }
    case NodeKind::SliceType: {
      mlir::Type elem = resolve(*type.kids[0]);
      if (!elem) return {};
      return SliceType::get(&ctx_, elem);
    }
    default:
      diags_.error(type.loc, std::string("the type form '") +
                                 syntax::nodeKindName(type.kind) +
                                 "' is not supported yet");
      return {};
  }
}

mlir::Type TypeResolver::resolveAnnot(const Node &annot) {
  if (annot.kids.size() > 2 && annot.kids[2]->kind != NodeKind::None) {
    diags_.error(annot.kids[2]->loc, "refinements ('where') are not supported yet");
    return {};
  }
  return resolve(*annot.kids[1]);
}

bool isTypeItem(const Node &item) {
  return item.kind == NodeKind::LetItem && item.kids.size() > 3 &&
         item.kids[0]->kids.empty() && item.kids[3]->kind == NodeKind::TypeValue;
}

bool isGenericTypeItem(const Node &item) {
  if (item.kind != NodeKind::LetItem || item.kids.size() < 4 ||
      !item.kids[0]->kids.empty())
    return false;
  const Node &value = *item.kids[3];
  if (value.kind != NodeKind::Lambda || value.kids.empty() ||
      value.kids.back()->kind != NodeKind::TypeValue)
    return false;
  for (size_t i = 0; i + 1 < value.kids.size(); ++i) {
    const Node &p = *value.kids[i];
    if (p.kind != NodeKind::LParam || p.kids.size() < 2 ||
        p.kids[0]->kind != NodeKind::PVar ||
        p.kids[1]->kind != NodeKind::Annot ||
        p.kids[1]->kids[1]->kind != NodeKind::TypeKind)
      return false;
  }
  return true;
}

// The parameter names of a generic type item.
static std::vector<std::string> genericParams(const Node &item) {
  std::vector<std::string> out;
  const Node &value = *item.kids[3];
  for (size_t i = 0; i + 1 < value.kids.size(); ++i)
    out.push_back(value.kids[i]->kids[0]->text);
  return out;
}

bool TypeResolver::unify(const Node &written, mlir::Type actual,
                         const std::vector<std::string> &params,
                         std::map<std::string, mlir::Type> &bound) const {
  if (!actual) return true;
  switch (written.kind) {
    case NodeKind::TypeName: {
      if (std::find(params.begin(), params.end(), written.text) == params.end())
        return true;  // a concrete type: coercion checks it later
      auto [it, fresh] = bound.emplace(written.text, actual);
      return fresh || it->second == actual;
    }
    case NodeKind::TypeApp: {
      const Instance *inst = instanceOf(actual);
      if (!inst || written.kids[0]->text != inst->generic ||
          inst->args.size() + 1 != written.kids.size())
        return true;
      for (size_t i = 0; i < inst->args.size(); ++i)
        if (!unify(*written.kids[i + 1], inst->args[i], params, bound))
          return false;
      return true;
    }
    case NodeKind::ArrayType:
    case NodeKind::SliceType: {
      mlir::Type elem;
      if (auto a = mlir::dyn_cast<ArrayType>(actual)) elem = a.getElementType();
      if (auto sl = mlir::dyn_cast<SliceType>(actual)) elem = sl.getElementType();
      return !elem || unify(*written.kids[0], elem, params, bound);
    }
    case NodeKind::Annot:
      return unify(*written.kids[1], actual, params, bound);
    default:
      return true;
  }
}

bool isCoreBuiltin(std::string_view name) {
  static const std::set<std::string, std::less<>> names = {
      "add", "sub", "add_sat", "sub_sat", "mul", "div", "rem",
      "eq",  "ne",  "lt",      "gt",      "le",  "ge",
      "and", "or",  "implies", "iff",     "len", "old",
      "band", "bor", "bxor", "bnot", "shl", "shr", "abort",
  };
  return names.count(name);
}

namespace {

// `let shape = type | Circle of u32 | Empty`: a record with a `tag` and one
// field per payload (struct Ctor in Sema.h).
mlir::Type buildVariant(const std::string &name, const Node &body,
                        TypeResolver &types, syntax::Diagnostics &diags,
                        bool instance) {
  mlir::MLIRContext *ctx = types.boolType().getContext();
  std::vector<std::pair<std::string, mlir::Type>> ctors;
  for (const syntax::NodePtr &c : body.kids) {
    if (!instance && types.isCtorName(c->text)) {
      diags.error(c->loc, "the constructor '" + c->text +
                              "' is already defined by another type");
      return {};
    }
    for (auto &[name, t] : ctors)
      if (name == c->text) {
        diags.error(c->loc, "the constructor '" + c->text +
                                "' is already declared");
        return {};
      }
    mlir::Type payload;
    if (!c->kids.empty() && c->kids[0]->kind != NodeKind::None) {
      payload = types.resolve(*c->kids[0]);
      if (!payload) return {};
      // `Ok of unit`, as in `result unit e`, carries nothing.
      if (types.isUnit(payload)) payload = {};
      if (payload && mlir::isa<ArrayType, SliceType>(payload)) {
        diags.error(c->kids[0]->loc,
                    "a constructor's payload of type " + typeName(payload) +
                        " is not supported yet");
        return {};
      }
    }
    ctors.push_back({c->text, payload});
  }
  if (ctors.empty()) {
    diags.error(body.loc, "a variant needs at least one constructor");
    return {};
  }
  llvm::SmallVector<mlir::StringAttr> names{mlir::StringAttr::get(ctx, "tag")};
  llvm::SmallVector<mlir::Type> fieldTypes{IntType::get(
      ctx, llvm::APInt(kWidth, 0), llvm::APInt(kWidth, ctors.size() - 1))};
  for (auto &[name, t] : ctors)
    if (t) {
      names.push_back(mlir::StringAttr::get(ctx, name));
      fieldTypes.push_back(t);
    }
  mlir::Type variant = RecordType::get(ctx, name, names, fieldTypes);
  if (types.isVariant(variant)) return variant;  // made before
  for (unsigned i = 0; i < ctors.size(); ++i)
    types.defineCtor(Ctor{ctors[i].first, variant, i, ctors[i].second},
                     !instance);
  return variant;
}

}  // namespace

// The type a `type <body>` value denotes, named `name`: a record, a
// variant, or another type. An instance's constructors are not global.
static mlir::Type buildType(const std::string &name, const Node &value,
                     TypeResolver &types, syntax::Diagnostics &diags,
                     bool instance) {
  const Node &body = *value.kids[0];
  if (!value.kids[1]->kids.empty()) {
    const Node &attr = *value.kids[1]->kids[0];
    diags.error(attr.loc, "the attribute @" + attr.text +
                              " on a type is not supported yet");
  }
  if (value.kids.size() > 2 && value.kids[2]->kind != NodeKind::None) {
    diags.error(value.kids[2]->loc,
                "refinements ('where') are not supported yet");
    return {};
  }
  mlir::MLIRContext *ctx = types.boolType().getContext();
  if (body.kind == NodeKind::Variants)
    return buildVariant(name, body, types, diags, instance);
  if (body.kind != NodeKind::RecordType) return types.resolve(body);
  llvm::SmallVector<mlir::StringAttr> names;
  llvm::SmallVector<mlir::Type> fieldTypes;
  for (const syntax::NodePtr &f : body.kids) {
    mlir::Type t = types.resolveAnnot(*f->kids[0]);
    if (!t) return {};
    if (!f->kids[0]->kids[0]->text.empty()) {
      diags.error(f->loc, "a field cannot have modifiers");
      return {};
    }
    if (types.isUnit(t)) {
      diags.error(f->loc, "a field cannot have type unit");
      return {};
    }
    if (mlir::isa<ArrayType, SliceType>(t)) {
      diags.error(f->loc, "a record field cannot be an array or slice yet");
      return {};
    }
    for (mlir::StringAttr n : names)
      if (n.getValue() == f->text) {
        diags.error(f->loc, "the field '" + f->text + "' is already declared");
        return {};
      }
    names.push_back(mlir::StringAttr::get(ctx, f->text));
    fieldTypes.push_back(t);
  }
  if (names.empty()) {
    diags.error(body.loc, "a record needs at least one field");
    return {};
  }
  return RecordType::get(ctx, name, names, fieldTypes);
}

mlir::Type TypeResolver::instantiate(const std::string &name,
                                     llvm::ArrayRef<mlir::Type> args,
                                     syntax::SourceLoc at) {
  const Generic *g = generic(name);
  if (!g) return {};
  if (args.size() != g->params.size()) {
    diags_.error(at, "'" + name + "' takes " + std::to_string(g->params.size()) +
                         " type argument" + (g->params.size() == 1 ? "" : "s") +
                         ", given " + std::to_string(args.size()));
    return {};
  }
  std::string key = name + "<";
  for (size_t i = 0; i < args.size(); ++i)
    key += (i ? ", " : "") + typeName(args[i]);
  key += ">";
  if (auto it = instances_.find(key); it != instances_.end()) return it->second;
  if (instantiating_.count(key)) {
    diags_.error(at, "the generic type '" + name + "' contains itself; "
                     "recursive types are not supported yet");
    return {};
  }
  instantiating_.insert(key);
  std::map<std::string, mlir::Type> scope;
  for (size_t i = 0; i < args.size(); ++i) scope[g->params[i]] = args[i];
  // The body sees only its parameters and top-level names.
  std::vector<std::map<std::string, mlir::Type>> saved;
  saved.swap(typeScopes_);
  pushTypeScope(std::move(scope));
  mlir::Type t = buildType(key, *g->value, *this, diags_, /*instance=*/true);
  typeScopes_.swap(saved);
  instantiating_.erase(key);
  if (!t) return {};
  instances_[key] = t;
  // An alias such as `let id = let (t : type) => type t` makes no new type.
  if (auto r = mlir::dyn_cast<RecordType>(t); r && r.getName() == key)
    instanceOf_.try_emplace(
        t, Instance{name, std::vector<mlir::Type>(args.begin(), args.end())});
  return t;
}

namespace {

// `let name = type <body>`: a record, or another name for a type.
void defineType(const Node &item, TypeResolver &types,
                syntax::Diagnostics &diags) {
  if (types.named(item.text) || types.builtin(item.text) ||
      types.generic(item.text)) {
    diags.error(item.loc, "the type '" + item.text + "' is already defined");
    return;
  }
  mlir::Type t = buildType(item.text, *item.kids[3], types, diags, false);
  if (t) types.define(item.text, t);
}

// `let name = let (t : type) ... => type <body>`: recorded, and made
// for each list of arguments it is used with. Its constructors are known
// by name now, so a constructor can choose the instance from its payload.
void defineGenericType(const Node &item, TypeResolver &types,
                       syntax::Diagnostics &diags) {
  if (types.named(item.text) || types.builtin(item.text) ||
      types.generic(item.text)) {
    diags.error(item.loc, "the type '" + item.text + "' is already defined");
    return;
  }
  const Node &value = *item.kids[3]->kids.back();
  Generic g{item.text, genericParams(item), &value, item.loc};
  std::set<std::string> seen;
  for (const std::string &p : g.params)
    if (!seen.insert(p).second) {
      diags.error(item.loc, "the type parameter '" + p + "' is declared twice");
      return;
    }
  const Node &body = *value.kids[0];
  if (body.kind == NodeKind::Variants) {
    for (size_t i = 0; i < body.kids.size(); ++i) {
      const Node &c = *body.kids[i];
      if (types.isCtorName(c.text)) {
        diags.error(c.loc, "the constructor '" + c.text +
                               "' is already defined by another type");
        return;
      }
      const Node *payload = !c.kids.empty() && c.kids[0]->kind != NodeKind::None
                                ? c.kids[0].get()
                                : nullptr;
      types.defineGenericCtor(
          GenericCtor{c.text, item.text, static_cast<unsigned>(i), payload});
    }
  }
  types.defineGeneric(std::move(g));
}

void typeNames(const Node &n, std::set<std::string> &out) {
  if (n.kind == NodeKind::TypeName) out.insert(n.text);
  for (const syntax::NodePtr &k : n.kids) typeNames(*k, out);
}

// Defines each type after the types it mentions, so a type may use one
// defined later in the file, as metaprograms often produce. Types left in a
// cycle are defined in source order, which reports the unknown name.
void defineTypes(const Node &program, TypeResolver &types,
                 syntax::Diagnostics &diags) {
  for (const syntax::NodePtr &item : program.kids)
    if (isGenericTypeItem(*item)) defineGenericType(*item, types, diags);
  std::vector<const Node *> pending;
  std::set<std::string> declared;
  for (const syntax::NodePtr &item : program.kids)
    if (isTypeItem(*item)) {
      pending.push_back(item.get());
      declared.insert(item->text);
    }
  std::set<std::string> done;
  while (!pending.empty()) {
    std::vector<const Node *> blocked;
    for (const Node *item : pending) {
      std::set<std::string> uses;
      typeNames(*item->kids[3], uses);
      bool ready = true;
      for (const std::string &u : uses)
        if (u != item->text && declared.count(u) && !done.count(u))
          ready = false;
      if (ready) {
        defineType(*item, types, diags);
        done.insert(item->text);
      } else {
        blocked.push_back(item);
      }
    }
    if (blocked.size() == pending.size()) {
      for (const Node *item : blocked) defineType(*item, types, diags);
      break;
    }
    pending = std::move(blocked);
  }
}

}  // namespace

bool isTypeParam(const Node &p) {
  return p.kind == NodeKind::Param && !p.kids.empty() &&
         p.kids[0]->kind == NodeKind::Annot &&
         p.kids[0]->kids[1]->kind == NodeKind::TypeKind;
}

bool resolveSignature(FuncSig &sig, TypeResolver &types,
                      syntax::Diagnostics &diags) {
  const Node &item = *sig.item;
  sig.params.clear();
  std::vector<std::map<std::string, mlir::Type>> saved;
  if (!sig.typeArgs.empty()) saved = types.replaceTypeScopes({sig.typeArgs});
  bool ok = true;
  for (const syntax::NodePtr &p : item.kids[0]->kids) {
    if (p->kind == NodeKind::ParamUnit) continue;
    if (isTypeParam(*p)) continue;
    if (p->kind != NodeKind::Param) {
      diags.error(p->loc, "this parameter form is not supported yet");
      ok = false;
      continue;
    }
    if (p->kids.empty() || p->kids[0]->kind == NodeKind::None) {
      diags.error(p->loc, "parameter '" + p->text +
                              "' needs a type annotation for now");
      ok = false;
      continue;
    }
    const Node &annot = *p->kids[0];
    Param param;
    param.name = p->text;
    param.modifiers = annot.kids[0]->text;
    param.loc = p->loc;
    param.type = types.resolveAnnot(annot);
    if (!param.type) {
      ok = false;
      continue;
    }
    if (types.isUnit(param.type)) {
      diags.error(p->loc, "a parameter cannot have type unit");
      ok = false;
      continue;
    }
    sig.params.push_back(std::move(param));
  }
  const Node &ret = *item.kids[1];
  if (ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
      ret.kids[0]->kind == NodeKind::Annot) {
    sig.result = types.resolveAnnot(*ret.kids[0]);
    if (!sig.result) ok = false;
  }
  if (!sig.typeArgs.empty()) types.replaceTypeScopes(std::move(saved));
  return ok;
}

std::map<std::string, FuncSig> collectSignatures(const Node &program,
                                                 TypeResolver &types,
                                                 syntax::Diagnostics &diags) {
  defineTypes(program, types, diags);
  std::vector<FuncSig> all;
  // An adapter's functions are named after it, `by_red.same`.
  std::vector<std::pair<const Node *, std::string>> items;
  for (const syntax::NodePtr &item : program.kids) {
    if (item->kind != NodeKind::Adapter) {
      items.emplace_back(item.get(), "");
      continue;
    }
    for (size_t i = 1; i < item->kids.size(); ++i)
      items.emplace_back(item->kids[i].get(), item->text);
  }
  for (auto &[itemPtr, adapter] : items) {
    const Node *item = itemPtr;
    if (isTypeItem(*item) || isGenericTypeItem(*item)) {
      if (!adapter.empty())
        diags.error(item->loc, "an adapter holds functions; define types "
                               "outside it");
      continue;
    }
    if (item->kind != NodeKind::LetItem) {
      diags.error(item->loc, std::string("'") + syntax::nodeKindName(item->kind) +
                                 "' items are not supported yet");
      continue;
    }
    // Concepts are checked by IRGen, at each use (ADR 0034).
    if (syntax::isConceptItem(*item) && adapter.empty()) continue;
    if (item->flags.find("meta") != std::string::npos) {
      diags.error(item->loc, "metaprograms are not supported yet");
      continue;
    }
    FuncSig sig;
    sig.name = adapter.empty() ? item->text : adapter + "." + item->text;
    sig.item = item;
    sig.adapter = adapter;
    for (const syntax::NodePtr &p : item->kids[0]->kids)
      if (isTypeParam(*p)) {
        if (std::find(sig.typeParams.begin(), sig.typeParams.end(), p->text) !=
            sig.typeParams.end())
          diags.error(p->loc, "the type parameter '" + p->text +
                                  "' is declared twice");
        sig.typeParams.push_back(p->text);
      }
    // A generic function's types are resolved for each instance.
    bool ok = sig.isGeneric() || resolveSignature(sig, types, diags);
    if (isCoreBuiltin(sig.name)) {
      diags.error(item->loc, "'" + sig.name + "' is a core builtin; Pia does "
                             "not allow shadowing (ADR 0022), so rename it "
                             "to " + sig.name + "'");
      continue;
    }
    if (types.named(sig.name) || types.generic(sig.name)) {
      diags.error(item->loc, "'" + sig.name + "' is already defined");
      continue;
    }
    if (ok) all.push_back(std::move(sig));
  }

  // Functions that share a name are overloads (ADR 0034). Each needs its
  // own parameter types, and a definition with no parameters is a value,
  // which cannot be overloaded. Overloads are named after their parameter
  // types, `eq(u8, u8)`; a lone function keeps its name, and so does the
  // generic overload, whose instances are named after their arguments.
  std::map<std::string, std::vector<size_t>> byName;
  for (size_t i = 0; i < all.size(); ++i) byName[all[i].name].push_back(i);
  std::vector<bool> drop(all.size(), false);
  // Reported in source order once every set is checked.
  std::vector<std::pair<syntax::SourceLoc, std::string>> errors;
  auto error = [&](syntax::SourceLoc at, std::string message) {
    errors.emplace_back(at, std::move(message));
  };
  for (auto &[name, group] : byName) {
    if (group.size() == 1) continue;
    unsigned generics = 0;
    for (size_t k = 0; k < group.size(); ++k) {
      FuncSig &sig = all[group[k]];
      const Node &item = *sig.item;
      bool valueLike = true;
      for (const syntax::NodePtr &p : item.kids[0]->kids)
        if (p->kind != NodeKind::ParamUnit) valueLike = false;
      if (valueLike && item.kids[0]->kids.empty()) {
        error(item.loc, "'" + name + "' is already defined; a "
                              "definition with no parameters cannot be "
                              "overloaded");
        drop[group[k]] = true;
        continue;
      }
      // Generic overloads are told apart by their parameter patterns and
      // constraints (ADR 0034); the first keeps the name, the others are
      // numbered, `sort#2`, and their instances are named after that.
      if (sig.isGeneric()) {
        if (++generics > 1) sig.name = name + "#" + std::to_string(generics);
        continue;
      }
      // Overloads with the same parameter types are told apart by their
      // preconditions (ADR 0034); IRGen checks that they can be. The
      // second and later are numbered, `copy(out [u8], [u8])#2`.
      unsigned twins = 0;
      for (size_t j = 0; j < k; ++j) {
        const FuncSig &other = all[group[j]];
        if (drop[group[j]] || other.isGeneric() ||
            other.params.size() != sig.params.size())
          continue;
        bool same = true;
        for (size_t i = 0; i < sig.params.size(); ++i)
          same = same && sig.params[i].type == other.params[i].type;
        twins += same;
        // With no precondition on either, nothing could tell them apart.
        auto hasRequires = [](const Node &it) {
          for (const syntax::NodePtr &c : it.kids[2]->kids)
            if (c->kind == NodeKind::Requires) return true;
          return false;
        };
        if (same && !hasRequires(item) && !hasRequires(*other.item)) {
          error(item.loc, "'" + name + "' is already defined with these "
                                "parameter types, and neither has a "
                                "precondition to tell them apart");
          drop[group[k]] = true;
          break;
        }
      }
      if (drop[group[k]]) continue;
      std::string symbol = name + "(";
      for (size_t i = 0; i < sig.params.size(); ++i)
        symbol += (i ? ", " : "") + typeName(sig.params[i].type);
      sig.name = symbol + ")";
      if (twins) sig.name += "#" + std::to_string(twins + 1);
    }
    for (size_t k : group) all[k].overloaded = true;
  }
  std::stable_sort(errors.begin(), errors.end(), [](auto &a, auto &b) {
    return std::make_pair(a.first.line, a.first.column) <
           std::make_pair(b.first.line, b.first.column);
  });
  for (auto &[at, message] : errors) diags.error(at, message);
  std::map<std::string, FuncSig> sigs;
  for (size_t i = 0; i < all.size(); ++i)
    if (!drop[i]) sigs.emplace(all[i].name, std::move(all[i]));
  return sigs;
}

}  // namespace pia::sema
