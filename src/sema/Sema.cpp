#include "sema/Sema.h"

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
      if (mlir::Type t = builtin(type.text)) return t;
      if (mlir::Type t = named(type.text)) return t;
      diags_.error(type.loc, "unknown type '" + type.text + "'");
      return {};
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
      if (mlir::isa<RecordType>(elem)) {
        diags_.error(type.loc, "arrays of records are not supported yet");
        return {};
      }
      return ArrayType::get(&ctx_, lit->value.getZExtValue(), elem);
    }
    case NodeKind::SliceType: {
      mlir::Type elem = resolve(*type.kids[0]);
      if (!elem) return {};
      if (mlir::isa<RecordType>(elem)) {
        diags_.error(type.loc, "slices of records are not supported yet");
        return {};
      }
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

bool isCoreBuiltin(std::string_view name) {
  static const std::set<std::string, std::less<>> names = {
      "add", "sub", "add_sat", "sub_sat", "mul", "div", "rem",
      "eq",  "ne",  "lt",      "gt",      "le",  "ge",
      "and", "or",  "implies", "iff",     "len", "old",
  };
  return names.count(name);
}

namespace {

// `let name = type <body>`: a record, or another name for a type.
void defineType(const Node &item, TypeResolver &types,
                syntax::Diagnostics &diags) {
  const Node &value = *item.kids[3];
  const Node &body = *value.kids[0];
  if (!value.kids[1]->kids.empty()) {
    const Node &attr = *value.kids[1]->kids[0];
    diags.error(attr.loc, "the attribute @" + attr.text +
                              " on a type is not supported yet");
  }
  if (value.kids.size() > 2 && value.kids[2]->kind != NodeKind::None) {
    diags.error(value.kids[2]->loc,
                "refinements ('where') are not supported yet");
    return;
  }
  if (types.named(item.text) || types.builtin(item.text)) {
    diags.error(item.loc, "the type '" + item.text + "' is already defined");
    return;
  }
  mlir::MLIRContext *ctx = types.boolType().getContext();
  if (body.kind != NodeKind::RecordType) {
    mlir::Type t = types.resolve(body);
    if (t) types.define(item.text, t);
    return;
  }
  llvm::SmallVector<mlir::StringAttr> names;
  llvm::SmallVector<mlir::Type> fieldTypes;
  for (const syntax::NodePtr &f : body.kids) {
    mlir::Type t = types.resolveAnnot(*f->kids[0]);
    if (!t) return;
    if (!f->kids[0]->kids[0]->text.empty()) {
      diags.error(f->loc, "a field cannot have modifiers");
      return;
    }
    if (types.isUnit(t)) {
      diags.error(f->loc, "a field cannot have type unit");
      return;
    }
    if (mlir::isa<ArrayType, SliceType>(t)) {
      diags.error(f->loc, "a record field cannot be an array or slice yet");
      return;
    }
    for (mlir::StringAttr n : names)
      if (n.getValue() == f->text) {
        diags.error(f->loc, "the field '" + f->text + "' is already declared");
        return;
      }
    names.push_back(mlir::StringAttr::get(ctx, f->text));
    fieldTypes.push_back(t);
  }
  if (names.empty()) {
    diags.error(body.loc, "a record needs at least one field");
    return;
  }
  types.define(item.text, RecordType::get(ctx, item.text, names, fieldTypes));
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

std::map<std::string, FuncSig> collectSignatures(const Node &program,
                                                 TypeResolver &types,
                                                 syntax::Diagnostics &diags) {
  defineTypes(program, types, diags);
  std::map<std::string, FuncSig> sigs;
  for (const syntax::NodePtr &item : program.kids) {
    if (isTypeItem(*item)) continue;
    if (item->kind != NodeKind::LetItem) {
      diags.error(item->loc, std::string("'") + syntax::nodeKindName(item->kind) +
                                 "' items are not supported yet");
      continue;
    }
    if (item->flags.find("meta") != std::string::npos) {
      diags.error(item->loc, "metaprograms are not supported yet");
      continue;
    }
    FuncSig sig;
    sig.name = item->text;
    sig.item = item.get();
    bool ok = true;
    for (const syntax::NodePtr &p : item->kids[0]->kids) {
      if (p->kind == NodeKind::ParamUnit) continue;
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
    const Node &ret = *item->kids[1];
    if (ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
        ret.kids[0]->kind == NodeKind::Annot) {
      sig.result = types.resolveAnnot(*ret.kids[0]);
      if (!sig.result) ok = false;
    }
    if (isCoreBuiltin(sig.name)) {
      diags.error(item->loc, "'" + sig.name + "' is a core builtin; Pia does "
                             "not allow shadowing (ADR 0022), so rename it "
                             "to " + sig.name + "'");
      continue;
    }
    if (sigs.count(sig.name) || types.named(sig.name)) {
      diags.error(item->loc, "'" + sig.name + "' is already defined");
      continue;
    }
    if (ok) sigs.emplace(sig.name, std::move(sig));
  }
  return sigs;
}

}  // namespace pia::sema
