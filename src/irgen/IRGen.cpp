#include "irgen/IRGen.h"

#include <algorithm>
#include <cstdlib>
#include <deque>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "dialect/ContractDialect.h"
#include "dialect/PiaDialect.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Verifier.h"
#include "meta/Interpreter.h"
#include "meta/Totality.h"
#include "sema/Sema.h"
#include "syntax/Parser.h"

namespace pia::irgen {

using mlir::Block;
using mlir::Location;
using mlir::OpBuilder;
using mlir::Type;
using mlir::Value;
using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

void loadDialects(mlir::MLIRContext &ctx) {
  ctx.loadDialect<PiaDialect, contract::ContractDialect, mlir::arith::ArithDialect,
                  mlir::func::FuncDialect, mlir::scf::SCFDialect>();
}

namespace {

constexpr unsigned kWidth = 128;

llvm::APInt widen(const llvm::APInt &v) { return v.sextOrTrunc(kWidth); }

// A lowered expression: its value and its type. Unit-typed expressions have
// no value and the type `none`.
struct TV {
  Value value;
  Type type;
};
using R = std::optional<TV>;

// A local name. Mutable locals are SSA values too: an assignment rebinds
// `value`, and structured control flow threads the binding through
// `scf.if` results and loop-carried values (docs/irgen.md).
struct Binding {
  std::string name;
  Value value;
  Type type;
  bool isMutable = false;
  std::string modifiers;  // a parameter's modifiers, empty for locals
  bool isParam = false;
};
using BindingPtr = std::shared_ptr<Binding>;

std::string plural(size_t n, const std::string &word) {
  return std::to_string(n) + " " + word + (n == 1 ? "" : "s");
}

bool isLiteral(const Node &n) {
  auto lit = [](const Node &k) {
    return k.kind == NodeKind::IntLit || k.kind == NodeKind::FloatLit;
  };
  return lit(n) || (n.kind == NodeKind::Neg && n.kids.size() == 1 &&
                    lit(*n.kids[0]));
}

// A literal with a decimal point or an exponent, such as `0.5` or `1.0e3`,
// as an exact rational in lowest terms: "n" or "n/d". Null if malformed.
std::optional<std::string> realLiteral(llvm::StringRef text, bool negate) {
  std::string digits;
  int exp10 = 0;
  size_t i = 0;
  bool point = false;
  for (; i < text.size(); ++i) {
    char c = text[i];
    if (c == '_') continue;
    if (c == '.') {
      if (point) return std::nullopt;
      point = true;
      continue;
    }
    if (c < '0' || c > '9') break;
    digits.push_back(c);
    if (point) --exp10;
  }
  if (i < text.size() && (text[i] == 'e' || text[i] == 'E')) {
    int e = 0;
    if (text.substr(i + 1).getAsInteger(10, e)) return std::nullopt;
    if (e > 4000 || e < -4000) return std::nullopt;
    exp10 += e;
  } else if (i != text.size()) {
    return std::nullopt;
  }
  if (digits.empty()) return std::nullopt;
  unsigned bits = 64 + static_cast<unsigned>(digits.size() * 4 +
                                             std::abs(exp10) * 4);
  llvm::APInt num(bits, digits, 10), den(bits, 1);
  llvm::APInt ten(bits, 10);
  for (; exp10 > 0; --exp10) num *= ten;
  for (; exp10 < 0; ++exp10) den *= ten;
  if (!num.isZero()) {
    llvm::APInt g = llvm::APIntOps::GreatestCommonDivisor(num, den);
    num = num.udiv(g);
    den = den.udiv(g);
  } else {
    den = llvm::APInt(bits, 1);
  }
  std::string out = (negate && !num.isZero() ? "-" : "") +
                    llvm::toString(num, 10, false);
  if (!den.isOne()) out += "/" + llvm::toString(den, 10, false);
  return out;
}

bool isComparison(const std::string &op) {
  return op == "=" || op == "<>" || op == "<" || op == "<=" || op == ">" ||
         op == ">=";
}

// The operator a core builtin stands for (src/syntax/Prelude.cpp), or null.
const char *builtinOperator(const std::string &name) {
  static const std::map<std::string, const char *> ops = {
      {"add", "+"},     {"sub", "-"},     {"add_sat", "+|"}, {"sub_sat", "-|"},
      {"mul", "*"},     {"div", "/"},     {"rem", "%"},      {"eq", "="},
      {"ne", "<>"},     {"lt", "<"},      {"gt", ">"},       {"le", "<="},
      {"ge", ">="},     {"and", "&&"},    {"or", "||"},      {"implies", "==>"},
      {"iff", "<==>"},  {"band", "&"},   {"bor", "|"},      {"bxor", "^"},
      {"shl", "<<"},    {"shr", ">>"},
  };
  auto it = ops.find(name);
  return it == ops.end() ? nullptr : it->second;
}

bool isLogic(const std::string &op) {
  return op == "&&" || op == "||" || op == "==>" || op == "<==>";
}

bool isArith(const std::string &op) {
  return op == "+" || op == "-" || op == "*" || op == "/" || op == "%" ||
         op == "mod" || op == "+|" || op == "-|" || op == "&" || op == "|" ||
         op == "^" || op == "<<" || op == ">>";
}

bool isShift(const std::string &op) { return op == "<<" || op == ">>"; }

// Every name assigned with `x <- ...` inside `n`.
void collectAssigned(const Node &n, std::set<std::string> &out) {
  if (n.kind == NodeKind::Assign && !n.kids.empty()) {
    const Node &place = *n.kids[0];
    if (place.kind == NodeKind::Name) out.insert(place.text);
    // `p.r <- v` rebinds the record `p`.
    if (place.kind == NodeKind::Field && !place.kids.empty() &&
        place.kids[0]->kind == NodeKind::Name)
      out.insert(place.kids[0]->text);
  }
  for (const syntax::NodePtr &k : n.kids) collectAssigned(*k, out);
}

class Gen {
 public:
  Gen(mlir::MLIRContext &ctx, std::string_view filename,
      syntax::Diagnostics &diags, const Options &options)
      : options_(options),
        ctx_(ctx),
        b_(&ctx),
        file_(mlir::StringAttr::get(&ctx, filename)),
        diags_(diags),
        types_(ctx, diags),
        interp_([](const std::string &) { return true; }) {}

  mlir::OwningOpRef<mlir::ModuleOp> run(const Node &program) {
    mlir::OwningOpRef<mlir::ModuleOp> module =
        mlir::ModuleOp::create(mlir::FileLineColLoc::get(file_, 1, 1));
    module_ = *module;
    collectTypeFunctions(program);
    // `result t e` comes with the language (ADR 0028), unless the program
    // brings its own `result`, `Ok` or `Err`.
    if (!definesResult(program)) {
      syntax::Diagnostics ignored;
      prelude_ = syntax::parseProgram(
          "let result = let (t : type) (e : type) => type | Ok of t | Err of "
          "e\n",
          ignored);
      if (prelude_) sema::defineTypeItems(*prelude_, types_, diags_);
    }
    sigs_ = sema::collectSignatures(program, types_, diags_);
    if (diags_.hasErrors()) return nullptr;
    collectConstants();
    if (diags_.hasErrors()) return nullptr;
    std::map<const Node *, std::string> symbolOf;
    for (auto &[symbol, sig] : sigs_) {
      symbolOf[sig.item] = symbol;
      if (sig.adapter.empty()) overloads_[sig.source()].push_back(symbol);
    }
    collectConcepts(program);
    if (diags_.hasErrors()) return nullptr;
    checkGenericOverloads();
    checkPreconditionOverloads();
    if (diags_.hasErrors()) return nullptr;
    // Each generic body is checked once, at its definition, against what
    // its constraints promise (ADR 0034, "Definition check").
    for (const syntax::NodePtr &item : program.kids)
      if (auto it = symbolOf.find(item.get()); it != symbolOf.end())
        if (sigs_.at(it->second).isGeneric()) checkDefinition(it->second);
    if (diags_.hasErrors()) return nullptr;
    for (const syntax::NodePtr &item : program.kids) {
      if (auto it = symbolOf.find(item.get()); it != symbolOf.end())
        genFunction(it->second);
      if (item->kind == NodeKind::Adapter)
        for (size_t i = 1; i < item->kids.size(); ++i)
          if (auto it = symbolOf.find(item->kids[i].get());
              it != symbolOf.end())
            genFunction(it->second);
    }
    // Each instance of a generic function is generated once, after the
    // function that first used it; an instance may use further instances.
    while (!diags_.hasErrors() && !pendingInstances_.empty()) {
      std::string key = pendingInstances_.front();
      pendingInstances_.pop_front();
      genFunction(key);
    }
    if (diags_.hasErrors()) return nullptr;
    checkGhosts();
    if (diags_.hasErrors()) return nullptr;
    if (mlir::failed(mlir::verify(*module))) return nullptr;
    return module;
  }

 private:
  // --- helpers --------------------------------------------------------

  // `OpTy::create(builder, ...)` replaced `builder.create<OpTy>(...)` in
  // LLVM 21; the second still works but is deprecated.
  template <typename OpTy, typename... Args>
  OpTy create(Location l, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
    return OpTy::create(b_, l, std::forward<Args>(args)...);
#else
    return b_.create<OpTy>(l, std::forward<Args>(args)...);
#endif
  }

  Location loc(const Node &n) {
    return mlir::FileLineColLoc::get(file_, n.loc.line, n.loc.column);
  }

  R fail(const Node &n, std::string message) {
    diags_.error(n.loc, std::move(message));
    return std::nullopt;
  }

  Type boolType() { return types_.boolType(); }
  Type unitType() { return types_.unitType(); }
  bool isUnit(Type t) { return types_.isUnit(t); }
  bool isBool(Type t) { return t && t.isInteger(1); }
  TV unit() { return {Value(), unitType()}; }

  std::string typeName(Type t) { return sema::typeName(t); }

  // The spec-only `int` and `real` (ADR 0036).
  static bool isExact(Type t) {
    return mlir::isa_and_nonnull<UnboundedIntType, RealType>(t);
  }
  TV exactConst(Location l, Type t, const std::string &value) {
    return TV{create<ExactConstantOp>(l, t, b_.getStringAttr(value)), t};
  }

  // Why `t`, which is or holds the spec-only `part`, cannot be in code:
  // "the spec-only type real; ..." or "type summary, which holds ...".
  std::string specOnlyMessage(Type t) {
    Type part = sema::specOnlyPart(t);
    std::string what =
        t == part ? "the spec-only type " + typeName(part)
                  : "type " + typeName(t) + ", which holds the spec-only "
                    "type " + typeName(part);
    return what + "; int and real can be used only in spec functions, "
           "lemmas, contracts and quantifiers, not in code (ADR 0036)";
  }

  // The smallest range type holding both.
  IntType join(IntType a, IntType b) {
    llvm::APInt alo = widen(a.getLo()), blo = widen(b.getLo());
    llvm::APInt ahi = widen(a.getHi()), bhi = widen(b.getHi());
    return IntType::get(&ctx_, alo.slt(blo) ? alo : blo,
                        ahi.sgt(bhi) ? ahi : bhi);
  }

  // Converts `v` to `target`: integers convert between range types
  // (narrowing becomes a proof obligation); other types must match.
  R coerce(const TV &v, Type target, const Node &at) {
    if (v.type == target) return v;
    // An array passes as a slice of all of it.
    if (auto a = mlir::dyn_cast<ArrayType>(v.type))
      if (auto sl = mlir::dyn_cast<SliceType>(target))
        if (a.getElementType() == sl.getElementType()) {
          Location l = loc(at);
          Value lo = create<mlir::arith::ConstantIndexOp>(l, 0);
          Value hi = create<mlir::arith::ConstantIndexOp>(
              l, static_cast<int64_t>(a.getLength()));
          return TV{create<SliceOp>(l, sl, v.value, lo, hi), target};
        }
    // Every integer is an `int` (ADR 0036): the conversion is exact.
    if (mlir::isa<IntType>(v.type) && mlir::isa<UnboundedIntType>(target))
      return TV{create<ExactConvertOp>(loc(at), target, v.value), target};
    if (mlir::isa<IntType>(v.type) && mlir::isa<IntType>(target)) {
      Value c = create<ConvertOp>(
          loc(at), target, v.value,
          OverflowModeAttr::get(&ctx_, OverflowMode::proof));
      return TV{c, target};
    }
    if (inErrorSet(v.type, target)) return widenError(v, target, at);
    return fail(at, "expected " + typeName(target) + ", found " +
                        typeName(v.type));
  }

  // Whether `member` is one of the variants of the error set `set`.
  bool inErrorSet(Type member, Type set) const {
    const std::vector<Type> *ms = types_.unionMembers(set);
    return ms && std::find(ms->begin(), ms->end(), member) != ms->end();
  }

  // A value of a member variant as a value of the error set: its
  // constructors are a block of the set's, so its tag moves up by where the
  // block starts, and its payload fields carry over.
  R widenError(const TV &v, Type set, const Node &at) {
    Location l = loc(at);
    auto from = mlir::cast<RecordType>(v.type);
    auto to = mlir::cast<RecordType>(set);
    std::vector<const sema::Ctor *> mine = types_.ctorsOf(v.type);
    const sema::Ctor *first = types_.ctorIn(mine[0]->name, set);
    if (!first) return fail(at, "internal error in an error set");
    Type ft = from.getFieldTypes()[*from.fieldIndex("tag")];
    Type tt = to.getFieldTypes()[*to.fieldIndex("tag")];
    Value tag = create<FieldOp>(l, ft, v.value, b_.getStringAttr("tag"));
    auto mode = OverflowModeAttr::get(&ctx_, OverflowMode::proof);
    tag = create<ConvertOp>(l, tt, tag, mode);
    if (first->tag) {
      Value k = create<ConstantOp>(
          l, tt,
          b_.getIntegerAttr(b_.getIntegerType(kWidth),
                            llvm::APInt(kWidth, first->tag)));
      tag = create<AddOp>(l, tt, tag, k, mode);
    }
    llvm::SmallVector<Value> fields;
    for (auto [name, t] : llvm::zip(to.getFieldNames(), to.getFieldTypes())) {
      if (name.getValue() == "tag") {
        fields.push_back(tag);
      } else if (from.fieldIndex(name.getValue())) {
        fields.push_back(create<FieldOp>(l, t, v.value, name));
      } else {
        Value d = defaultValue(l, t);
        if (!d)
          return fail(at, "cannot build a value of " + typeName(t) +
                              " for an unused payload");
        fields.push_back(d);
      }
    }
    return TV{create<RecordOp>(l, to, fields).getResult(), set};
  }

  Value boolConst(Location l, bool v) {
    return create<mlir::arith::ConstantOp>(l, b_.getBoolAttr(v));
  }

  Value implies(Location l, Value a, Value c) {
    Value notA = create<mlir::arith::XOrIOp>(l, a, boolConst(l, true));
    return create<mlir::arith::OrIOp>(l, notA, c);
  }

  Value cmp(Location l, CmpPredicate p, Value a, Value c) {
    return create<CmpOp>(l, b_.getI1Type(),
                            CmpPredicateAttr::get(&ctx_, p), a, c);
  }

  Value toIndex(Location l, Value v) {
    return create<ToIndexOp>(l, b_.getIndexType(), v);
  }

  // --- scopes ---------------------------------------------------------

  void pushScope() { scopes_.emplace_back(); }
  void popScope() { scopes_.pop_back(); }

  BindingPtr bind(const std::string &name, Value v, Type t, bool isMutable) {
    auto b = std::make_shared<Binding>();
    b->name = name;
    b->value = v;
    b->type = t;
    b->isMutable = isMutable;
    scopes_.back()[name] = b;
    return b;
  }

  // Pia has no shadowing (ADR 0022): a binding written in the source may not
  // reuse the name of a local in scope, a function, a type or a core
  // builtin. Names a quote binds carry a `#` and are always fresh.
  bool checkFresh(const std::string &name, syntax::SourceLoc at) {
    if (name.find('#') != std::string::npos) return true;
    std::string what;
    if (lookup(name)) what = "a local of the same name";
    else if (overloads_.count(name)) what = "the function '" + name + "'";
    else if (consts_.count(name)) what = "the constant '" + name + "'";
    else if (types_.isCtorName(name)) what = "the constructor '" + name + "'";
    else if (types_.named(name) || types_.builtin(name))
      what = "the type '" + name + "'";
    else if (sema::isCoreBuiltin(name)) what = "a core builtin";
    else return true;
    diags_.error(at, "'" + name + "' shadows " + what +
                         "; Pia does not allow shadowing (ADR 0022), so "
                         "rename it to " + primed(name));
    return false;
  }

  // The first of `x'`, `x''`, ... that nothing in scope uses.
  std::string primed(const std::string &name) {
    std::string p = name + "'";
    while (lookup(p) || overloads_.count(p) || consts_.count(p) ||
           types_.named(p))
      p += "'";
    return p;
  }

  BindingPtr lookup(const std::string &name) {
    for (auto it = scopes_.rbegin(); it != scopes_.rend(); ++it) {
      auto found = it->find(name);
      if (found != it->end()) return found->second;
    }
    return nullptr;
  }

  // The mutable locals that the given subtrees assign, in name order. These
  // become `scf.if` results and loop-carried values.
  std::vector<BindingPtr> carried(std::initializer_list<const Node *> nodes) {
    std::set<std::string> names;
    for (const Node *n : nodes)
      if (n) collectAssigned(*n, names);
    std::vector<BindingPtr> out;
    for (const std::string &name : names) {
      BindingPtr b = lookup(name);
      if (b && b->isMutable && !mlir::isa<ArrayType, SliceType>(b->type))
        out.push_back(b);
    }
    return out;
  }

  static llvm::SmallVector<Value> values(const std::vector<BindingPtr> &bs) {
    llvm::SmallVector<Value> out;
    for (const BindingPtr &b : bs) out.push_back(b->value);
    return out;
  }

  static void setValues(const std::vector<BindingPtr> &bs,
                        mlir::ValueRange vs) {
    for (size_t i = 0; i < bs.size(); ++i) bs[i]->value = vs[i];
  }

  // --- functions ------------------------------------------------------

  // `let crc_table : [u32; 256] = [...]`: a top-level array of literals is
  // constant data, not a function. Each use reads it from read-only data.
  void collectConstants() {
    for (auto it = sigs_.begin(); it != sigs_.end();) {
      const sema::FuncSig &sig = it->second;
      auto arr = mlir::dyn_cast_or_null<ArrayType>(sig.result);
      const Node &body = *sig.item->kids[3];
      // One with contracts stays a function, so they are proved.
      if (!sig.params.empty() || !arr || body.kind != NodeKind::ListLit ||
          !sig.item->kids[2]->kids.empty()) {
        ++it;
        continue;
      }
      if (auto values = constValues(body, arr))
        consts_[sig.name] = {arr, *values};
      it = sigs_.erase(it);
    }
  }

  // The values of an array literal of integer literals, checked against
  // the array type.
  std::optional<mlir::ArrayAttr> constValues(const Node &lit, ArrayType arr) {
    auto elem = mlir::dyn_cast<IntType>(arr.getElementType());
    if (!elem) {
      fail(lit, "constant arrays of " + typeName(arr.getElementType()) +
                    " are not supported yet");
      return std::nullopt;
    }
    if (lit.kids.size() != arr.getLength()) {
      fail(lit, "an array literal for " + typeName(arr) + " needs " +
                    plural(arr.getLength(), "element") + ", found " +
                    std::to_string(lit.kids.size()));
      return std::nullopt;
    }
    llvm::SmallVector<mlir::Attribute> values;
    for (const syntax::NodePtr &k : lit.kids) {
      const Node *n = k.get();
      bool negative = false;
      if (n->kind == NodeKind::Neg && n->kids.size() == 1) {
        negative = true;
        n = n->kids[0].get();
      }
      if (n->kind != NodeKind::IntLit) {
        fail(*k, "an array literal's elements must be integer literals for "
                 "now");
        return std::nullopt;
      }
      auto v = sema::parseIntLiteral(n->text);
      if (!v) {
        fail(*k, "invalid integer literal");
        return std::nullopt;
      }
      llvm::APInt x = negative ? -v->value : v->value;
      if (!elem.contains(x)) {
        fail(*k, llvm::toString(x, 10, true) + " does not fit in " +
                     typeName(elem));
        return std::nullopt;
      }
      values.push_back(b_.getIntegerAttr(b_.getIntegerType(kWidth), x));
    }
    return b_.getArrayAttr(values);
  }

  struct Constant {
    ArrayType type;
    mlir::ArrayAttr values;
  };

  void genFunction(const std::string &name) {
    auto it = sigs_.find(name);
    if (it == sigs_.end() || it->second.isGeneric()) return;
    sema::FuncSig &sig = it->second;
    const Node &item = *sig.item;
    Location l = loc(item);
    // An instance's body sees its type parameters as their arguments.
    struct TypeScope {
      sema::TypeResolver &types;
      std::vector<std::map<std::string, Type>> saved;
      ~TypeScope() { types.replaceTypeScopes(std::move(saved)); }
    } typeScope{types_, types_.replaceTypeScopes({})};
    if (!sig.typeArgs.empty()) types_.pushTypeScope(sig.typeArgs);
    adapted_ = sig.adapted;
    adapterFor_ = sig.adapterFor;

    llvm::SmallVector<Type> argTypes;
    for (const sema::Param &p : sig.params) argTypes.push_back(p.type);
    auto resultTypes = [&](Type t) {
      return t && !isUnit(t) ? llvm::SmallVector<Type>{t}
                             : llvm::SmallVector<Type>{};
    };

    b_.setInsertionPointToEnd(module_.getBody());
    auto fn = create<mlir::func::FuncOp>(
        l, sig.name, b_.getFunctionType(argTypes, resultTypes(sig.result)));
    // An instance is internal: C calls the generic's instances only through
    // Pia functions, which name concrete types.
    if (!sig.typeArgs.empty()) fn.setPrivate();
    for (size_t i = 0; i < sig.params.size(); ++i)
      if (!sig.params[i].modifiers.empty())
        fn.setArgAttr(i, PiaDialect::getModifiersAttrName(),
                      b_.getStringAttr(sig.params[i].modifiers));
    Block *entry = fn.addEntryBlock();
    b_.setInsertionPointToStart(entry);

    scopes_.clear();
    pushScope();
    for (size_t i = 0; i < sig.params.size(); ++i) {
      const sema::Param &p = sig.params[i];
      // The verifier names counterexample values after the parameters.
      entry->getArgument(i).setLoc(mlir::NameLoc::get(
          b_.getStringAttr(p.name),
          mlir::FileLineColLoc::get(file_, p.loc.line, p.loc.column)));
      checkFresh(p.name, p.loc);
      BindingPtr b = bind(p.name, entry->getArgument(i), p.type,
                          sema::hasModifier(p.modifiers, "mutable"));
      b->modifiers = p.modifiers;
      b->isParam = true;
    }

    overflow_ = OverflowMode::proof;
    fuel_ = 0;
    ghost_ = false;
    const Node &ret = *item.kids[1];
    if (ret.kind == NodeKind::RetAnnot && ret.kids.size() > 1 &&
        !genAttributes(*ret.kids[1]))
      return;
    bool isSpec = hasFlag(item, "spec"), isLemma = hasFlag(item, "lemma");
    ghost_ = isSpec || isLemma;
    // `int` and `real` exist only for the verifier, so code can neither
    // take nor return them, even inside a record (ADR 0036).
    if (!ghost_) {
      for (const sema::Param &p : sig.params)
        if (sema::specOnlyPart(p.type)) {
          diags_.error(p.loc, "the parameter '" + p.name + "' has " +
                                  specOnlyMessage(p.type));
          return;
        }
      if (sema::specOnlyPart(sig.result)) {
        fail(ret, "'" + name + "' returns a value of " +
                      specOnlyMessage(sig.result));
        return;
      }
    }
    if (fuel_ && !isSpec) {
      fail(item, "@fuel applies only to a spec function");
      return;
    }
    if (isSpec || isLemma) {
      // Specification code only says what other code means: it cannot
      // write through its parameters (docs/verification.md).
      for (const sema::Param &p : sig.params)
        if (sema::hasModifier(p.modifiers, "out") ||
            sema::hasModifier(p.modifiers, "inout") ||
            sema::hasModifier(p.modifiers, "mutable")) {
          diags_.error(p.loc, std::string("a parameter of a ") +
                                  (isSpec ? "spec function" : "lemma") +
                                  " cannot be out, inout or mutable");
          return;
        }
      fn->setAttr(isSpec ? PiaDialect::getSpecAttrName()
                         : PiaDialect::getLemmaAttrName(),
                  b_.getUnitAttr());
      if (fuel_)
        fn->setAttr(PiaDialect::getFuelAttrName(),
                    b_.getI64IntegerAttr(fuel_));
    }

    const Node &contracts = *item.kids[2];
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind == NodeKind::Requires) {
        R p = genPredicate(*c->kids[0]);
        if (!p) return;
        create<contract::RequiresOp>(loc(*c), p->value);
      } else if (c->kind == NodeKind::Decreases) {
        R m = genContractExpr(*c->kids[0], Type());
        if (!m) return;
        create<contract::DecreasesOp>(loc(*c), m->value);
      } else if (c->kind == NodeKind::Invariant) {
        fail(*c, "'invariant' belongs to a state, which only the REPL "
                 "supports yet (ADR 0031)");
        return;
      }
    }

    // A spec function's body is specification, like a contract: it may
    // use quantifiers, and it is never compiled.
    const Node &bodyNode = *item.kids[3];
    // The body is the first scope a `?` can leave (ADR 0028).
    struct FrameScope {
      std::deque<Frame> &frames;
      std::deque<Frame> saved;
      ~FrameScope() { frames = std::move(saved); }
    } frameScope{frames_, std::move(frames_)};
    frames_.clear();
    frames_.emplace_back();
    frames_.back().result = sig.result;
    frames_.back().function = sig.source();
    if (!isSpec) addTails(bodyNode);
    R body = isSpec ? genContractExpr(bodyNode, sig.result)
                    : genExpr(bodyNode, sig.result);
    if (!body) return;
    Type result = sig.result;
    if (!result) {
      result = body->type;
      sig.result = result;
      fn.setType(b_.getFunctionType(argTypes, resultTypes(result)));
    }
    if (isSpec && isUnit(result)) {
      fail(item, "a spec function must return a value");
      return;
    }
    if (isLemma && !isUnit(result)) {
      fail(item, "a lemma returns unit: what it proves goes in 'ensures'");
      return;
    }
    llvm::SmallVector<Value> rets;
    if (!isUnit(result)) {
      if (isUnit(body->type)) {
        fail(bodyNode, "'" + name + "' returns " + typeName(result) +
                           ", but its body has type unit");
        return;
      }
      R v = coerce(*body, result, bodyNode);
      if (!v) return;
      rets.push_back(v->value);
    } else if (!isUnit(body->type)) {
      fail(bodyNode, "'" + name + "' returns unit, but its body has type " +
                         typeName(body->type));
      return;
    }

    pushScope();
    if (!rets.empty()) bind("result", rets[0], result, false);
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind != NodeKind::Ensures) continue;
      R p = genPredicate(*c->kids[0]);
      if (!p) return;
      create<contract::EnsuresOp>(loc(*c), p->value);
    }
    popScope();
    create<mlir::func::ReturnOp>(l, rets);
  }

  static bool hasFlag(const Node &item, llvm::StringRef flag) {
    llvm::SmallVector<llvm::StringRef> words;
    llvm::StringRef(item.flags).split(words, ' ', -1, false);
    return llvm::is_contained(words, flag);
  }

  syntax::SourceLoc sourceLoc(Location l) {
    syntax::SourceLoc at;
    if (auto f = mlir::dyn_cast<mlir::FileLineColLoc>(l)) {
      at.line = f.getLine();
      at.column = f.getColumn();
    } else if (auto n = mlir::dyn_cast<mlir::NameLoc>(l)) {
      return sourceLoc(n.getChildLoc());
    }
    return at;
  }

  // A spec function is pure and total, so the verifier can give its
  // definition to the solver: no loops, no writes, no `abort`, and calls
  // only to other spec functions. A recursive one needs a `decreases`
  // measure, and spec functions cannot be mutually recursive yet. Lemmas
  // are erased from code, so code cannot use what they compute.
  void checkGhosts() {
    auto isSpec = [](mlir::func::FuncOp f) {
      return f && f->hasAttr(PiaDialect::getSpecAttrName());
    };
    std::map<std::string, std::vector<std::string>> calls;
    for (auto f : module_.getOps<mlir::func::FuncOp>()) {
      if (!isSpec(f)) continue;
      std::string name = f.getSymName().str();
      f.walk([&](mlir::Operation *op) {
        if (mlir::isa<mlir::scf::ForOp, mlir::scf::WhileOp>(op))
          diags_.error(sourceLoc(op->getLoc()),
                       "a spec function cannot contain a loop; write it "
                       "with recursion and 'decreases'");
        else if (mlir::isa<StoreOp>(op))
          diags_.error(sourceLoc(op->getLoc()),
                       "a spec function cannot write to a buffer");
        else if (mlir::isa<AbortOp>(op))
          diags_.error(sourceLoc(op->getLoc()),
                       "a spec function cannot 'abort'; give it a "
                       "precondition instead");
        else if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op)) {
          auto callee =
              module_.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
          if (!isSpec(callee))
            diags_.error(sourceLoc(op->getLoc()),
                         "a spec function can call only spec functions, "
                         "and '" + call.getCallee().str() + "' is not one");
          else
            calls[name].push_back(call.getCallee().str());
        }
      });
      bool recursive = llvm::is_contained(calls[name], name);
      bool measured = !f.getBody().front().getOps<contract::DecreasesOp>().empty();
      if (recursive && !measured)
        diags_.error(sourceLoc(f.getLoc()),
                     "the recursive spec function '" + name +
                         "' needs a 'decreases' measure");
    }
    // A cycle through two or more spec functions.
    for (auto &[name, callees] : calls) {
      std::set<std::string> seen;
      std::vector<std::string> work;
      for (const std::string &c : callees)
        if (c != name) work.push_back(c);
      while (!work.empty()) {
        std::string c = work.back();
        work.pop_back();
        if (!seen.insert(c).second) continue;
        if (c == name) {
          auto f = module_.lookupSymbol<mlir::func::FuncOp>(name);
          diags_.error(sourceLoc(f.getLoc()),
                       "spec functions cannot be mutually recursive yet: '" +
                           name + "' calls itself through other spec functions");
          break;
        }
        for (const std::string &d : calls[c]) work.push_back(d);
      }
    }
  }

  // `@overflow(wrap)` on the return annotation sets the function's mode.
  bool genAttributes(const Node &attrs) {
    for (const syntax::NodePtr &a : attrs.kids) {
      if (a->text == "overflow" && a->kids.size() == 1 &&
          a->kids[0]->kind == NodeKind::Name) {
        const std::string &m = a->kids[0]->text;
        if (m == "proof") overflow_ = OverflowMode::proof;
        else if (m == "wrap") overflow_ = OverflowMode::wrap;
        else if (m == "saturate") overflow_ = OverflowMode::saturate;
        else if (m == "trap") overflow_ = OverflowMode::trap;
        else {
          fail(*a, "@overflow takes proof, wrap, saturate or trap");
          return false;
        }
        continue;
      }
      if (a->text == "fuel" && a->kids.size() == 1 &&
          a->kids[0]->kind == NodeKind::IntLit) {
        auto lit = sema::parseIntLiteral(a->kids[0]->text);
        if (!lit || !lit->suffix.empty() || lit->value.isZero() ||
            lit->value.ugt(16)) {
          fail(*a, "@fuel takes a number from 1 to 16");
          return false;
        }
        fuel_ = static_cast<unsigned>(lit->value.getZExtValue());
        continue;
      }
      // `@allow(range_requires)` silences a lint (ADR 0037); lints run on
      // the syntax tree, so there is nothing to generate.
      if (a->text == "allow" && !a->kids.empty()) {
        bool names = true;
        for (const syntax::NodePtr &k : a->kids)
          names &= k->kind == NodeKind::Name;
        if (names) continue;
        fail(*a, "@allow takes lint names, such as @allow(range_requires)");
        return false;
      }
      fail(*a, "the attribute @" + a->text + " is not supported yet");
      return false;
    }
    return true;
  }

  // --- expressions ----------------------------------------------------

  R genPredicate(const Node &n) {
    R p = genContractExpr(n, boolType());
    if (!p) return p;
    if (!isBool(p->type))
      return fail(n, "a contract must be a bool, found " + typeName(p->type));
    return p;
  }

  R genContractExpr(const Node &n, Type expected) {
    bool saved = contract_;
    contract_ = true;
    R r = genExpr(n, expected);
    contract_ = saved;
    return r;
  }

  // Every expression in code is checked for a spec-only type, so neither
  // `int` nor `real` reaches code generation (ADR 0036).
  R genExpr(const Node &n, Type expected) {
    R r = genExprOf(n, expected);
    if (r && !contract_ && !ghost_)
      if (sema::specOnlyPart(r->type))
        return fail(n, "this expression has " + specOnlyMessage(r->type));
    return r;
  }

  R genExprOf(const Node &n, Type expected) {
    if (!frames_.empty() && frames_.back().tails.count(&n))
      if (const Node *t = hoistable(n)) return genTry(n, *t, expected);
    switch (n.kind) {
      case NodeKind::IntLit: {
        auto lit = sema::parseIntLiteral(n.text);
        // An int literal has no bounds (ADR 0036).
        if (!lit && isExact(expected)) {
          std::string digits;
          for (char c : n.text)
            if (c != '_') digits.push_back(c);
          if (!digits.empty() &&
              llvm::all_of(digits, [](char c) { return c >= '0' && c <= '9'; }))
            return exactConst(loc(n), expected,
                              llvm::toString(llvm::APInt(8 + 4 * digits.size(),
                                                         digits, 10),
                                             10, false));
        }
        if (!lit) return fail(n, "invalid integer literal '" + n.text + "'");
        return genIntConst(n, lit->value, lit->suffix, expected);
      }
      case NodeKind::FloatLit:
        return genRealConst(n, n.text, false, expected);
      case NodeKind::BoolLit:
        return TV{boolConst(loc(n), n.text == "true"), boolType()};
      case NodeKind::Unit:
        return unit();
      case NodeKind::Name:
        return genName(n, expected);
      case NodeKind::Binary:
        return genBinary(n, n.text, *n.kids[0], *n.kids[1], expected);
      case NodeKind::Neg:
        return genNeg(n, expected);
      case NodeKind::Apply:
        return genApply(n, expected);
      case NodeKind::Instantiate: {
        const Node &f = *n.kids[0];
        auto set = f.kind == NodeKind::Name
                       ? overloadSet(f.text)
                       : std::vector<sema::FuncSig *>{};
        if (set.size() > 1)
          return genOverloadedCall(n, f.text, set, &n, {}, expected);
        if (set.empty() || !set[0]->isGeneric())
          return fail(n, "only a generic function takes type arguments here");
        return genGenericCall(n, *set[0], &n, {}, expected);
      }
      case NodeKind::Index:
        return genIndex(n);
      case NodeKind::ListLit: {
        auto arr = mlir::dyn_cast_or_null<ArrayType>(expected);
        if (!arr)
          return fail(n, "an array literal needs its type from the context, "
                         "as in 'let t : [u8; 3] = [1; 2; 3]'");
        auto values = constValues(n, arr);
        if (!values) return std::nullopt;
        auto op = create<ConstArrayOp>(loc(n), arr, *values,
                                       mlir::StringAttr());
        return TV{op.getResult(), arr};
      }
      case NodeKind::RecordLit:
        return genRecordLit(n, expected);
      case NodeKind::Field:
        return genField(n);
      case NodeKind::Assign:
        return genAssign(n);
      case NodeKind::If:
        return genIf(n, expected);
      case NodeKind::For:
        return genFor(n);
      case NodeKind::While:
        return genWhile(n);
      case NodeKind::Sequence: {
        if (n.kids[0]->kind == NodeKind::Defer) return genDefer(n, expected);
        R first = genExpr(*n.kids[0], Type());
        if (!first) return first;
        if (!mustUse(*first, *n.kids[0])) return std::nullopt;
        return genExpr(*n.kids[1], expected);
      }
      case NodeKind::Try:
        return fail(n, tryMisplaced());
      case NodeKind::Handle:
        return genHandle(n, expected);
      case NodeKind::Defer:
        return fail(n, "'defer' registers cleanup for the rest of its "
                       "sequence, so something must follow it, as in "
                       "'defer close f; use f'");
      case NodeKind::Cleanup:
        return genCleanup(n, expected);
      case NodeKind::LetIn:
        return genLetIn(n, expected);
      case NodeKind::Assert:
      case NodeKind::Assume: {
        R p = genPredicate(*n.kids[0]);
        if (!p) return p;
        if (n.kind == NodeKind::Assert)
          create<contract::AssertOp>(loc(n), p->value);
        else
          create<contract::AssumeOp>(loc(n), p->value);
        return unit();
      }
      case NodeKind::Quantifier:
        if (!contract_)
          return fail(n, "quantifiers are only allowed in contracts and "
                         "assertions");
        return genQuantifier(n, 0);
      case NodeKind::Range:
        return fail(n, "a range is only allowed in a for loop or a "
                       "quantifier for now");
      case NodeKind::Match:
        return genMatch(n, expected);
      default:
        return fail(n, std::string("'") + syntax::nodeKindName(n.kind) +
                           "' is not supported yet (IRGen covers the scalar "
                           "subset)");
    }
  }

  R genIntConst(const Node &n, llvm::APInt v, const std::string &suffix,
                Type expected) {
    Type t;
    if (suffix.empty() && isExact(expected))
      return exactConst(loc(n), expected, llvm::toString(v, 10, true));
    if (!suffix.empty()) {
      t = types_.builtin(suffix);
    } else if (mlir::isa_and_nonnull<IntType>(expected)) {
      t = expected;
    } else {
      // No context: i32 as in the design's `sum [1; 2; 3]`, else the
      // first of i64 and u64 that holds the value.
      for (const char *name : {"i32", "i64", "u64"}) {
        t = types_.builtin(name);
        if (mlir::cast<IntType>(t).contains(v)) break;
      }
    }
    auto it = mlir::cast<IntType>(t);
    if (!it.contains(v))
      return fail(n, llvm::toString(v, 10, true) + " does not fit in " +
                         typeName(t));
    Value c = create<ConstantOp>(
        loc(n), t, b_.getIntegerAttr(b_.getIntegerType(kWidth), v));
    return TV{c, t};
  }

  // `0.5`, `1.0e3`: a real, exact. Pia has no floating-point types yet.
  R genRealConst(const Node &n, llvm::StringRef text, bool negate,
                 Type expected) {
    size_t f = text.find_first_of("fiu");
    if (f != llvm::StringRef::npos)
      return fail(n, "'" + text.str() + "': floating-point types are not "
                     "supported yet; a literal with a decimal point is a "
                     "spec-only real, with no suffix");
    std::optional<std::string> v = realLiteral(text, negate);
    if (!v) return fail(n, "invalid real literal '" + text.str() + "'");
    (void)expected;  // a mismatch is reported where the value is used
    return exactConst(loc(n), RealType::get(&ctx_), *v);
  }

  R genName(const Node &n, Type expected) {
    if (n.flags.empty())
      if (BindingPtr b = lookup(n.text)) return TV{b->value, b->type};
    if (types_.isCtorName(n.text)) {
      const sema::Ctor *c = ctorFor(n, n.text, expected, std::nullopt);
      if (!c) return std::nullopt;
      if (c->payload)
        return fail(n, "'" + n.text + "' takes a payload of type " +
                           typeName(c->payload) + ", as in '" + n.text +
                           " x'");
      return genCtor(n, *c, std::nullopt);
    }
    if (auto c = consts_.find(n.text); c != consts_.end()) {
      auto op = create<ConstArrayOp>(loc(n), c->second.type, c->second.values,
                                     b_.getStringAttr(n.text));
      return TV{op.getResult(), c->second.type};
    }
    auto set = overloadSet(n.text);
    if (set.size() > 1)
      return genOverloadedCall(n, n.text, set, nullptr, {}, expected);
    if (!set.empty()) {
      sema::FuncSig &sig = *set[0];
      if (sig.isGeneric())
        return genGenericCall(n, sig, nullptr, {}, expected);
      if (!sig.params.empty())
        return fail(n, "functions as values are not supported yet; apply '" +
                           n.text + "' to all its arguments");
      return genCall(n, sig, {});
    }
    return fail(n, "unknown name '" + n.text + "'");
  }

  // Lowers both operands. A literal takes its type from the other side, so
  // `0 < x` and `x < 0` both compare at x's type.
  std::optional<std::pair<TV, TV>> genOperands(const Node &lhs, const Node &rhs,
                                               Type expected) {
    if (isLiteral(lhs) && !isLiteral(rhs)) {
      R r = genExpr(rhs, expected);
      if (!r) return std::nullopt;
      R l = genExpr(lhs, r->type);
      if (!l) return std::nullopt;
      return std::make_pair(*l, *r);
    }
    R l = genExpr(lhs, expected);
    if (!l) return std::nullopt;
    R r = genExpr(rhs, l->type);
    if (!r) return std::nullopt;
    return std::make_pair(*l, *r);
  }

  // Brings two integers to their joined type.
  std::optional<std::pair<TV, TV>> unify(TV a, TV c, const Node &n,
                                         const std::string &op,
                                         const Node &lhs, const Node &rhs) {
    if (isExact(a.type) || isExact(c.type)) {
      // An integer joins `int` exactly; a real meets only a real.
      Type t = mlir::isa<RealType>(c.type) || !isExact(a.type) ? c.type
                                                                 : a.type;
      auto fits = [&](Type x) {
        return x == t || (mlir::isa<IntType>(x) &&
                          mlir::isa<UnboundedIntType>(t));
      };
      bool ok = fits(a.type) && fits(c.type);
      if (!ok) {
        std::string hint = mlir::isa<RealType>(t)
                               ? "; convert an integer with 'real x'"
                               : "";
        fail(n, "'" + op + "' needs operands of one type, found " +
                    typeName(a.type) + " and " + typeName(c.type) + hint);
        return std::nullopt;
      }
      R a2 = coerce(a, t, lhs);
      R c2 = coerce(c, t, rhs);
      if (!a2 || !c2) return std::nullopt;
      return std::make_pair(*a2, *c2);
    }
    auto at = mlir::dyn_cast<IntType>(a.type);
    auto ct = mlir::dyn_cast<IntType>(c.type);
    if (!at || !ct) {
      fail(n, "'" + op + "' needs integer operands, found " +
                  typeName(a.type) + " and " + typeName(c.type));
      return std::nullopt;
    }
    IntType j = join(at, ct);
    R a2 = coerce(a, j, lhs);
    R c2 = coerce(c, j, rhs);
    if (!a2 || !c2) return std::nullopt;
    return std::make_pair(*a2, *c2);
  }

  // A binary operation. After metaprogram expansion it arrives as a call of
  // a core builtin, such as `add a b` for `a + b` (docs/meta.md); `n` is the
  // node it is reported at.
  R genBinary(const Node &n, const std::string &op, const Node &lhsNode,
              const Node &rhsNode, Type expected) {
    if (isLogic(op)) return genLogic(n, op, lhsNode, rhsNode);
    if (isComparison(op)) {
      auto ops = genOperands(lhsNode, rhsNode, Type());
      if (!ops) return std::nullopt;
      auto [a, c] = *ops;
      Location l = loc(n);
      if (isBool(a.type) && isBool(c.type) && (op == "=" || op == "<>")) {
        Value v = create<mlir::arith::CmpIOp>(
            l,
            op == "=" ? mlir::arith::CmpIPredicate::eq
                      : mlir::arith::CmpIPredicate::ne,
            a.value, c.value);
        return TV{v, boolType()};
      }
      if (archetypes_.count(a.type) || archetypes_.count(c.type)) {
        // A contract may compare values of a type parameter's type: what
        // it means is decided for each instance.
        if (contract_ && a.type == c.type && (op == "=" || op == "<>"))
          return TV{boolConst(l, true), boolType()};
        Type t = archetypes_.count(a.type) ? a.type : c.type;
        return fail(n, "'" + op + "' is not defined for every '" +
                           typeName(t) + "'; a generic body can use only "
                           "what its constraints promise");
      }
      if (contract_ && a.type == c.type && (op == "=" || op == "<>") &&
          (mlir::isa<ArrayType>(a.type) || mlir::isa<SliceType>(a.type)))
        return genBufferEq(n, op, a, c);
      if (mlir::isa<RecordType>(a.type) || mlir::isa<RecordType>(c.type))
        return genRecordEq(n, op, a, lhsNode, c, rhsNode);
      auto u = unify(a, c, n, op, lhsNode, rhsNode);
      if (!u) return std::nullopt;
      CmpPredicate p = op == "="    ? CmpPredicate::eq
                       : op == "<>" ? CmpPredicate::ne
                       : op == "<"  ? CmpPredicate::lt
                       : op == "<=" ? CmpPredicate::le
                       : op == ">"  ? CmpPredicate::gt
                                    : CmpPredicate::ge;
      if (isExact(u->first.type))
        return TV{create<ExactCmpOp>(l, b_.getI1Type(),
                                     CmpPredicateAttr::get(&ctx_, p),
                                     u->first.value, u->second.value),
                  boolType()};
      return TV{cmp(l, p, u->first.value, u->second.value), boolType()};
    }
    if (isArith(op)) {
      auto ops = genOperands(lhsNode, rhsNode,
                             mlir::isa_and_nonnull<IntType>(expected) ||
                                     isExact(expected)
                                 ? expected
                                 : Type());
      if (!ops) return std::nullopt;
      if (isExact(ops->first.type) || isExact(ops->second.type))
        return genExactArith(n, op, ops->first, ops->second, lhsNode,
                             rhsNode);
      // Arithmetic happens at the join of the operand types and, when the
      // context expects a wider integer, at that type: `dst.[i] <- src.[i] * 3`
      // with u8 `src` and u16 `dst` multiplies at u16.
      TV lhs = ops->first, rhs = ops->second;
      // A shift happens at the type of the value shifted, widened to what
      // the context expects; the amount keeps its own type.
      if (isShift(op)) return genShift(n, op, lhs, rhs, lhsNode, expected);
      if (auto want = mlir::dyn_cast_or_null<IntType>(expected)) {
        auto lt = mlir::dyn_cast<IntType>(lhs.type);
        auto rt = mlir::dyn_cast<IntType>(rhs.type);
        if (lt && rt) {
          IntType j = join(join(lt, rt), want);
          R l2 = coerce(lhs, j, lhsNode);
          R r2 = coerce(rhs, j, rhsNode);
          if (!l2 || !r2) return std::nullopt;
          lhs = *l2;
          rhs = *r2;
        }
      }
      auto u = unify(lhs, rhs, n, op, lhsNode, rhsNode);
      if (!u) return std::nullopt;
      Value a = u->first.value, c = u->second.value;
      Type t = u->first.type;
      Location l = loc(n);
      OverflowMode m =
          op == "+|" || op == "-|" ? OverflowMode::saturate : overflow_;
      auto mode = OverflowModeAttr::get(&ctx_, m);
      Value v;
      if (op == "+" || op == "+|") v = create<AddOp>(l, t, a, c, mode);
      else if (op == "-" || op == "-|") v = create<SubOp>(l, t, a, c, mode);
      else if (op == "*") v = create<MulOp>(l, t, a, c, mode);
      else if (op == "/") v = create<DivOp>(l, t, a, c, mode);
      else if (op == "&") v = create<BAndOp>(l, t, a, c, mode);
      else if (op == "|") v = create<BOrOp>(l, t, a, c, mode);
      else if (op == "^") v = create<BXorOp>(l, t, a, c, mode);
      else v = create<RemOp>(l, t, a, c, mode);
      return TV{v, t};
    }
    return fail(n, "the operator '" + op + "' is not supported yet");
  }

  // `+ - *` on `int` and `real`, and `/` on `real`: exact, so there is
  // nothing to overflow (ADR 0036).
  R genExactArith(const Node &n, const std::string &op, TV lhs, TV rhs,
                  const Node &lhsNode, const Node &rhsNode) {
    if (op != "+" && op != "-" && op != "*" && op != "/")
      return fail(n, "'" + op + "' is not defined on " +
                         typeName(isExact(lhs.type) ? lhs.type : rhs.type) +
                         "; int and real have + - * and comparisons, and "
                         "real also has /");
    auto u = unify(lhs, rhs, n, op, lhsNode, rhsNode);
    if (!u) return std::nullopt;
    Type t = u->first.type;
    Value a = u->first.value, c = u->second.value;
    Location l = loc(n);
    Value v;
    if (op == "+") v = create<ExactAddOp>(l, t, a, c);
    else if (op == "-") v = create<ExactSubOp>(l, t, a, c);
    else if (op == "*") v = create<ExactMulOp>(l, t, a, c);
    else if (mlir::isa<RealType>(t)) v = create<ExactDivOp>(l, t, a, c);
    else
      return fail(n, "'/' is not defined on int; convert to real with "
                     "'real x' to divide");
    return TV{v, t};
  }

  // `int x` and `real x`: an integer as an exact int or real.
  R genExactConversion(const Node &n, const std::string &to, const Node &arg) {
    Type target = to == "int" ? Type(UnboundedIntType::get(&ctx_))
                              : Type(RealType::get(&ctx_));
    if (isLiteral(arg)) return genExpr(arg, target);
    R v = genExpr(arg, Type());
    if (!v) return v;
    if (v->type == target) return v;
    bool ok = mlir::isa<IntType>(v->type) ||
              (mlir::isa<UnboundedIntType>(v->type) &&
               mlir::isa<RealType>(target));
    if (!ok)
      return fail(arg, "'" + to + "' converts an integer" +
                           std::string(to == "real" ? " or an int" : "") +
                           ", not " + typeName(v->type));
    return TV{create<ExactConvertOp>(loc(n), target, v->value), target};
  }

  R genShift(const Node &n, const std::string &op, TV lhs, TV rhs,
             const Node &lhsNode, Type expected) {
    auto lt = mlir::dyn_cast<IntType>(lhs.type);
    auto rt = mlir::dyn_cast<IntType>(rhs.type);
    if (!lt || !rt)
      return fail(n, "'" + op + "' needs integer operands, found " +
                         typeName(lhs.type) + " and " + typeName(rhs.type));
    if (auto want = mlir::dyn_cast_or_null<IntType>(expected)) {
      IntType j = join(lt, want);
      R l2 = coerce(lhs, j, lhsNode);
      if (!l2) return std::nullopt;
      lhs = *l2;
      lt = j;
    }
    auto mode = OverflowModeAttr::get(&ctx_, overflow_);
    Value v = op == "<<" ? Value(create<ShlOp>(loc(n), lt, lhs.value,
                                               rhs.value, mode))
                         : Value(create<ShrOp>(loc(n), lt, lhs.value,
                                               rhs.value, mode));
    return TV{v, lt};
  }

  // The instance of the generic that owns constructor `name`, when the
  // expected type is one.
  Type instanceFor(const std::string &name, Type expected) {
    const sema::GenericCtor *g = types_.genericCtor(name);
    const sema::Instance *inst = expected ? types_.instanceOf(expected) : nullptr;
    return g && inst && inst->generic == g->generic ? expected : Type();
  }

  // The constructor `name` builds: of its own variant, or of the instance
  // of its generic that the expected type or the payload's type gives.
  const sema::Ctor *ctorFor(const Node &at, const std::string &name,
                            Type expected, std::optional<Type> payload) {
    if (const sema::Ctor *c = types_.ctor(name)) return c;
    const sema::GenericCtor *g = types_.genericCtor(name);
    if (!g) {
      fail(at, "unknown constructor '" + name + "'");
      return nullptr;
    }
    Type variant = instanceFor(name, expected);
    if (!variant) {
      const sema::Generic *gen = types_.generic(g->generic);
      std::map<std::string, Type> bound;
      if (payload && *payload && g->payload &&
          !types_.unify(*g->payload, *payload, gen->params, bound)) {
        fail(at, "cannot tell which " + g->generic + " '" + name +
                     "' builds from a payload of type " + typeName(*payload));
        return nullptr;
      }
      llvm::SmallVector<Type> args;
      for (const std::string &p : gen->params) {
        auto it = bound.find(p);
        if (it == bound.end()) {
          fail(at, "cannot tell which " + g->generic + " '" + name +
                       "' builds: '" + p + "' is unknown; give the type, as "
                       "in 'let r : " + g->generic + " ... = " + name + " ...'");
          return nullptr;
        }
        args.push_back(it->second);
      }
      variant = types_.instantiate(g->generic, args, at.loc);
      if (!variant) return nullptr;
    }
    const sema::Ctor *c = types_.ctorIn(name, variant);
    if (!c) fail(at, "internal error: no constructor '" + name + "' in " +
                         typeName(variant));
    return c;
  }

  // A variant value: its tag, the payload in its constructor's field, and a
  // fixed value in every other payload field, which nothing reads.
  R genCtor(const Node &n, const sema::Ctor &c, std::optional<TV> payload) {
    Location l = loc(n);
    auto rt = mlir::cast<RecordType>(c.variant);
    llvm::SmallVector<Value> fields;
    for (auto [name, ft] : llvm::zip(rt.getFieldNames(), rt.getFieldTypes())) {
      if (name.getValue() == "tag") {
        fields.push_back(create<ConstantOp>(
            l, ft,
            b_.getIntegerAttr(b_.getIntegerType(kWidth),
                              llvm::APInt(kWidth, c.tag))));
      } else if (name.getValue() == c.name && payload) {
        fields.push_back(payload->value);
      } else {
        Value d = defaultValue(l, ft);
        if (!d)
          return fail(n, "cannot build a value of " + typeName(ft) +
                             " for an unused payload");
        fields.push_back(d);
      }
    }
    return TV{create<RecordOp>(l, rt, fields).getResult(), rt};
  }

  // Some value of `t`: its lowest integer, false, or a record of those.
  Value defaultValue(Location l, Type t) {
    if (auto it = mlir::dyn_cast<IntType>(t)) {
      llvm::APInt v = it.contains(llvm::APInt(kWidth, 0))
                          ? llvm::APInt(kWidth, 0)
                          : it.getLo().sextOrTrunc(kWidth);
      return create<ConstantOp>(
          l, it, b_.getIntegerAttr(b_.getIntegerType(kWidth), v));
    }
    if (isBool(t)) return boolConst(l, false);
    if (auto rt = mlir::dyn_cast<RecordType>(t)) {
      llvm::SmallVector<Value> fields;
      for (Type ft : rt.getFieldTypes()) {
        Value d = defaultValue(l, ft);
        if (!d) return Value();
        fields.push_back(d);
      }
      return create<RecordOp>(l, rt, fields).getResult();
    }
    return Value();
  }

  // `match e with | C x -> a | D -> b | _ -> c` on a variant. It becomes a
  // chain of `if`s on the tag, each arm binding its payload, so carried
  // mutable locals and result types work as they do for `if`. The arms must
  // cover every constructor, and none may be redundant.
  R genMatch(const Node &n, Type expected) {
    R s = genExpr(*n.kids[0], Type());
    if (!s) return s;
    if (!types_.isVariant(s->type))
      return fail(*n.kids[0], "'match' on " + typeName(s->type) +
                                  " is not supported yet; it works on "
                                  "variants");
    std::vector<const sema::Ctor *> ctors = types_.ctorsOf(s->type);
    std::string hidden = "#match" + std::to_string(matchCounter_++);

    // Each arm: the constructor it tests (null for a catch-all) and the name
    // it binds (empty for none, or `_`).
    struct ArmInfo {
      const sema::Ctor *ctor = nullptr;
      std::string bind;
      std::string as;  // `p as x` binds `x` to the whole value
      syntax::SourceLoc asAt;
      const Node *contracts = nullptr;  // `requires` and `ensures` (ADR 0035)
      const Node *body = nullptr;
      const Node *at = nullptr;
    };
    std::vector<ArmInfo> arms;
    std::set<std::string> covered;
    bool catchAll = false;
    for (size_t i = 1; i < n.kids.size(); ++i) {
      const Node &arm = *n.kids[i];
      const Node &pat = corePattern(*arm.kids[0]);
      ArmInfo a;
      if (arm.kids.size() > 2) a.contracts = arm.kids[2].get();
      if (arm.kids[0]->kind == NodeKind::PAs) {
        a.as = arm.kids[0]->text;
        a.asAt = arm.kids[0]->loc;
      }
      a.body = arm.kids[1].get();
      a.at = &pat;
      if (catchAll)
        return fail(pat, "this arm is never reached: an earlier arm "
                         "matches everything");
      if (pat.kind == NodeKind::PVar && !types_.isCtorName(pat.text)) {
        catchAll = true;
        if (pat.text != "_") a.bind = pat.text;
      } else if (pat.kind == NodeKind::PVar ||
                 (pat.kind == NodeKind::PCtor)) {
        const sema::Ctor *c = types_.ctorIn(pat.text, s->type);
        if (!c && !types_.isCtorName(pat.text))
          return fail(pat, "unknown constructor '" + pat.text + "'");
        if (!c) {
          if (const sema::Ctor *other = types_.ctor(pat.text))
            return fail(pat, "'" + pat.text + "' is a constructor of " +
                                 typeName(other->variant) + ", not of " +
                                 typeName(s->type));
          return fail(pat, "'" + pat.text + "' is not a constructor of " +
                               typeName(s->type));
        }
        if (covered.count(c->name))
          return fail(pat, "'" + c->name + "' is already matched by an "
                           "earlier arm");
        size_t subs = pat.kind == NodeKind::PCtor ? pat.kids.size() : 0;
        // `Ok ()` matches a constructor whose payload is unit.
        bool unitSub = subs == 1 && !c->payload &&
                       pat.kids[0]->kind == NodeKind::PLit &&
                       pat.kids[0]->text == "()";
        if (subs > (c->payload || unitSub ? 1u : 0u))
          return fail(pat, "'" + c->name + "' has " +
                               (c->payload ? "one payload" : "no payload"));
        if (subs == 1 && !unitSub) {
          const Node &sub = *pat.kids[0];
          // A constructor that is its variant's only one matches every
          // payload, as `OutOfMemory` does in `Err OutOfMemory`.
          bool only = sub.kind == NodeKind::PVar &&
                      types_.ctorIn(sub.text, c->payload) &&
                      types_.ctorsOf(c->payload).size() == 1;
          if (!only && (sub.kind != NodeKind::PVar ||
                        types_.isCtorName(sub.text)))
            return fail(sub, "only a name, '_' or a variant's only "
                             "constructor can match a payload for now");
          if (!only && sub.text != "_") a.bind = sub.text;
        }
        covered.insert(c->name);
        a.ctor = c;
      } else {
        return fail(pat, "this pattern is not supported yet; match a "
                         "constructor, a name or '_'");
      }
      arms.push_back(a);
    }
    if (!catchAll) {
      std::string missing;
      for (const sema::Ctor *c : ctors)
        if (!covered.count(c->name))
          missing += (missing.empty() ? "" : ", ") + c->name;
      if (!missing.empty())
        return fail(n, "the match does not cover " + missing +
                           "; add an arm for each, or '_'");
    } else if (covered.size() == ctors.size()) {
      return fail(*arms.back().at, "this arm is never reached: the arms "
                                   "before it cover every constructor");
    }

    // The chain, built as syntax over the hidden name: the last arm needs
    // no test, since the arms are exhaustive.
    syntax::SourceLoc at = n.loc;
    auto hiddenName = [&]() {
      return syntax::makeNode(NodeKind::Name, at, hidden);
    };
    auto letIn = [&](const std::string &name, syntax::SourceLoc l,
                     syntax::NodePtr value, syntax::NodePtr body) {
      auto let = syntax::makeNode(NodeKind::LetIn, l, name);
      let->add(syntax::makeNode(NodeKind::Params, l));
      let->add(syntax::makeNode(NodeKind::None, l));
      let->add(syntax::makeNode(NodeKind::Contracts, l));
      let->add(std::move(value));
      let->add(std::move(body));
      return let;
    };
    bool tail = !frames_.empty() && frames_.back().tails.count(&n);
    auto armBody = [&](const ArmInfo &a) -> syntax::NodePtr {
      syntax::NodePtr body = syntax::clone(*a.body);
      if (a.contracts) body = withArmContracts(*a.contracts, std::move(body));
      // An arm of a match that ends its scope ends it too, so a `?` there
      // can end it as well.
      if (tail) addTails(*body);
      if (!a.bind.empty()) {
        syntax::NodePtr value;
        if (a.ctor) {
          value = syntax::makeNode(NodeKind::Apply, a.at->loc);
          auto fn = syntax::makeNode(NodeKind::Name, a.at->loc, "#payload");
          fn->flags = "prelude";
          value->add(std::move(fn));
          value->add(hiddenName());
          value->add(
              syntax::makeNode(NodeKind::Name, a.at->loc, a.ctor->name));
        } else {
          value = hiddenName();
        }
        body = letIn(a.bind, a.at->loc, std::move(value), std::move(body));
      }
      if (!a.as.empty())
        body = letIn(a.as, a.asAt, hiddenName(), std::move(body));
      return body;
    };
    syntax::NodePtr chain = armBody(arms.back());
    for (size_t i = arms.size() - 1; i-- > 0;) {
      auto test = syntax::makeNode(NodeKind::Apply, arms[i].at->loc);
      auto fn = syntax::makeNode(NodeKind::Name, arms[i].at->loc, "#is");
      fn->flags = "prelude";
      test->add(std::move(fn));
      test->add(hiddenName());
      test->add(syntax::makeNode(NodeKind::Name, arms[i].at->loc,
                                 arms[i].ctor->name));
      auto ifNode = syntax::makeNode(NodeKind::If, arms[i].at->loc);
      ifNode->add(std::move(test));
      ifNode->add(armBody(arms[i]));
      ifNode->add(std::move(chain));
      chain = std::move(ifNode);
    }
    pushScope();
    bind(hidden, s->value, s->type, false);
    R r = genExpr(*chain, expected);
    popScope();
    matchTrees_.push_back(std::move(chain));  // diagnostics may point into it
    return r;
  }

  // An arm's contracts (ADR 0035) as assertions: each `requires` is proved
  // for every value that reaches the arm, before its body, and each
  // `ensures` of the arm's value, named `result` there.
  syntax::NodePtr withArmContracts(const Node &contracts,
                                   syntax::NodePtr body) {
    syntax::SourceLoc at = contracts.loc;
    std::string value = "#arm" + std::to_string(matchCounter_++);
    std::vector<const Node *> ensures;
    for (const syntax::NodePtr &c : contracts.kids)
      if (c->kind == NodeKind::Ensures) ensures.push_back(c.get());
    if (!ensures.empty()) {
      syntax::NodePtr rest = syntax::makeNode(NodeKind::Name, at, value);
      for (auto it = ensures.rbegin(); it != ensures.rend(); ++it) {
        auto assert = syntax::makeNode(NodeKind::Assert, (*it)->loc);
        assert->add(renamed(*(*it)->kids[0], "result", value));
        auto seq = syntax::makeNode(NodeKind::Sequence, (*it)->loc);
        seq->add(std::move(assert));
        seq->add(std::move(rest));
        rest = std::move(seq);
      }
      auto let = syntax::makeNode(NodeKind::LetIn, at, value);
      let->add(syntax::makeNode(NodeKind::Params, at));
      let->add(syntax::makeNode(NodeKind::None, at));
      let->add(syntax::makeNode(NodeKind::Contracts, at));
      let->add(std::move(body));
      let->add(std::move(rest));
      body = std::move(let);
    }
    for (size_t i = contracts.kids.size(); i-- > 0;) {
      const Node &c = *contracts.kids[i];
      if (c.kind != NodeKind::Requires) continue;
      auto assert = syntax::makeNode(NodeKind::Assert, c.loc);
      assert->add(syntax::clone(*c.kids[0]));
      auto seq = syntax::makeNode(NodeKind::Sequence, c.loc);
      seq->add(std::move(assert));
      seq->add(std::move(body));
      body = std::move(seq);
    }
    return body;
  }

  // A copy of `n` with the name `from` spelled `to`.
  static syntax::NodePtr renamed(const Node &n, const std::string &from,
                                 const std::string &to) {
    syntax::NodePtr c = syntax::clone(n);
    std::function<void(Node &)> go = [&](Node &x) {
      if (x.kind == NodeKind::Name && x.text == from) x.text = to;
      for (syntax::NodePtr &k : x.kids) go(*k);
    };
    go(*c);
    return c;
  }

  // `#is s C` and `#payload s C`, which only `match` produces.
  R genMatchBuiltin(const Node &n) {
    BindingPtr b = lookup(n.kids[1]->text);
    const sema::Ctor *c = b ? types_.ctorIn(n.kids[2]->text, b->type) : nullptr;
    if (!b || !c) return fail(n, "internal error in 'match'");
    auto rt = mlir::cast<RecordType>(b->type);
    Location l = loc(n);
    if (n.kids[0]->text == "#is") {
      Type tt = rt.getFieldTypes()[*rt.fieldIndex("tag")];
      Value tag = create<FieldOp>(l, tt, b->value, b_.getStringAttr("tag"));
      Value k = create<ConstantOp>(
          l, tt,
          b_.getIntegerAttr(b_.getIntegerType(kWidth),
                            llvm::APInt(kWidth, c->tag)));
      return TV{cmp(l, CmpPredicate::eq, tag, k), boolType()};
    }
    Value v = create<FieldOp>(l, c->payload, b->value,
                              b_.getStringAttr(c->name));
    return TV{v, c->payload};
  }

  // `abort ()`: proved unreachable. In a context that wants a value it has
  // that type, though it never produces one.
  R genAbort(const Node &n, Type expected) {
    Location l = loc(n);
    if (!expected || isUnit(expected)) {
      create<AbortOp>(l, mlir::TypeRange{});
      return unit();
    }
    if (!mlir::isa<IntType>(expected) && !isBool(expected))
      return fail(n, "'abort' where a " + typeName(expected) +
                         " is expected is not supported yet");
    auto op = create<AbortOp>(l, mlir::TypeRange{expected});
    return TV{op->getResult(0), expected};
  }

  // `~x`: every bit of x's representation flipped. On an unsigned type that
  // is `max - x` at x's machine width; on a signed one, `-1 - x`.
  R genBNot(const Node &n, const Node &operand, Type expected) {
    R v = genExpr(operand, expected);
    if (!v) return v;
    auto t = mlir::dyn_cast<IntType>(v->type);
    if (!t) return fail(n, "'~' needs an integer, found " + typeName(v->type));
    Location l = loc(n);
    auto mode = OverflowModeAttr::get(&ctx_, overflow_);
    if (t.isSigned()) {
      llvm::APInt m1 = llvm::APInt::getAllOnes(kWidth);
      auto kt = IntType::get(&ctx_, m1, m1);
      Value k = create<ConstantOp>(l, kt, b_.getIntegerAttr(
                                              b_.getIntegerType(kWidth), m1));
      Value r = create<SubOp>(l, t, k, v->value, mode);
      return TV{r, t};
    }
    llvm::APInt ones =
        llvm::APInt::getMaxValue(t.getStorageWidth()).zext(kWidth);
    auto full = IntType::get(&ctx_, llvm::APInt(kWidth, 0), ones);
    Value k = create<ConstantOp>(
        l, full, b_.getIntegerAttr(b_.getIntegerType(kWidth), ones));
    Value r = create<BXorOp>(l, full, v->value, k, mode);
    return TV{r, full};
  }

  // `&&`, `||` and `==>` short-circuit in code, so they lower to `scf.if`.
  // In contracts, which have no effects, they are plain `arith` logic.
  R genLogic(const Node &n, const std::string &op, const Node &lhsNode,
             const Node &rhsNode) {
    Location l = loc(n);
    R a = genExpr(lhsNode, boolType());
    if (!a) return a;
    if (!isBool(a->type))
      return fail(lhsNode, "'" + op + "' needs bool operands, found " +
                               typeName(a->type));
    auto genRhs = [&]() -> R {
      R c = genExpr(rhsNode, boolType());
      if (!c) return c;
      if (!isBool(c->type))
        return fail(rhsNode, "'" + op + "' needs bool operands, found " +
                                    typeName(c->type));
      return c;
    };
    if (contract_ || op == "<==>") {
      R c = genRhs();
      if (!c) return c;
      Value v;
      if (op == "&&") v = create<mlir::arith::AndIOp>(l, a->value, c->value);
      else if (op == "||") v = create<mlir::arith::OrIOp>(l, a->value, c->value);
      else if (op == "==>") v = implies(l, a->value, c->value);
      else
        v = create<mlir::arith::CmpIOp>(l, mlir::arith::CmpIPredicate::eq,
                                           a->value, c->value);
      return TV{v, boolType()};
    }
    std::set<std::string> assigned;
    collectAssigned(rhsNode, assigned);
    if (!assigned.empty())
      return fail(rhsNode, "an assignment on the right of '" + op +
                                  "' is not supported");
    // && : if a then rhs else false;  || : if a then true else rhs;
    // ==> : if a then rhs else true.
    bool rhsInThen = op != "||";
    auto rhsBlock = std::make_unique<Block>();
    auto constBlock = std::make_unique<Block>();
    {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(rhsBlock.get());
      R c = genRhs();
      if (!c) return c;
      create<mlir::scf::YieldOp>(l, mlir::ValueRange{c->value});
      b_.setInsertionPointToEnd(constBlock.get());
      Value k = boolConst(l, op != "&&");
      create<mlir::scf::YieldOp>(l, mlir::ValueRange{k});
    }
    auto ifOp = makeIf(l, {boolType()}, a->value,
                       rhsInThen ? std::move(rhsBlock) : std::move(constBlock),
                       rhsInThen ? std::move(constBlock) : std::move(rhsBlock));
    return TV{ifOp.getResult(0), boolType()};
  }

  // Creates `scf.if` and moves the prepared blocks into its regions.
  mlir::scf::IfOp makeIf(Location l, mlir::TypeRange types, Value cond,
                         std::unique_ptr<Block> thenBlock,
                         std::unique_ptr<Block> elseBlock) {
    auto op = create<mlir::scf::IfOp>(l, types, cond,
                                         /*withElseRegion=*/true);
    op.getThenRegion().getBlocks().clear();
    op.getThenRegion().push_back(thenBlock.release());
    op.getElseRegion().getBlocks().clear();
    op.getElseRegion().push_back(elseBlock.release());
    return op;
  }

  R genNeg(const Node &n, Type expected) {
    const Node &operand = *n.kids[0];
    if (operand.kind == NodeKind::FloatLit)
      return genRealConst(n, operand.text, true, expected);
    if (operand.kind == NodeKind::IntLit && !isExact(expected)) {
      auto lit = sema::parseIntLiteral(operand.text);
      if (!lit) return fail(operand, "invalid integer literal");
      return genIntConst(n, -lit->value, lit->suffix, expected);
    }
    R v = genExpr(operand, expected);
    if (!v) return v;
    if (isExact(v->type)) {
      TV zero = exactConst(loc(n), v->type, "0");
      return TV{create<ExactSubOp>(loc(n), v->type, zero.value, v->value),
                v->type};
    }
    auto t = mlir::dyn_cast<IntType>(v->type);
    if (!t) return fail(n, "'-' needs an integer, found " + typeName(v->type));
    Value zero = create<ConstantOp>(
        loc(n), t, b_.getIntegerAttr(b_.getIntegerType(kWidth), 0));
    if (!t.contains(llvm::APInt(kWidth, 0)))
      return fail(n, "cannot negate a value of " + typeName(t) +
                         ", whose range does not include 0");
    Value r = create<SubOp>(loc(n), t, zero, v->value,
                               OverflowModeAttr::get(&ctx_, overflow_));
    return TV{r, t};
  }

  R genApply(const Node &n, Type expected) {
    // `f<u8> x` names the type arguments; the rest are deduced.
    const Node *targs = nullptr;
    const Node *callee = n.kids[0].get();
    if (callee->kind == NodeKind::Instantiate) {
      targs = callee;
      callee = callee->kids[0].get();
    }
    const Node &fn = *callee;
    if (fn.kind != NodeKind::Name)
      return fail(fn, "only named functions can be called for now");
    size_t argc = n.kids.size() - 1;
    Location l = loc(n);
    // A name a quote made resolves where the metaprogram was defined, never
    // to a local at the expansion site (docs/meta.md, "Hygiene").
    bool local = fn.flags.empty() && lookup(fn.text);
    if (!local && fn.flags != "prelude") {
      auto set = overloadSet(fn.text);
      if (set.empty() && checking_ && !types_.isCtorName(fn.text))
        if (std::string hint = notPromised(fn.text, {}); !hint.empty())
          return fail(fn, hint);
      if (!set.empty()) {
        std::vector<const Node *> args;
        for (size_t i = 1; i < n.kids.size(); ++i)
          args.push_back(n.kids[i].get());
        // In a generic body, a call with an argument of a type parameter's
        // type must find what it calls among what the constraints promise.
        if (set.size() > 1 || (checking_ && !set[0]->isGeneric()))
          return genOverloadedCall(n, fn.text, set, targs, args, expected);
        sema::FuncSig &sig = *set[0];
        if (sig.isGeneric())
          return genGenericCall(n, sig, targs, args, expected);
        if (targs)
          return fail(*targs, "'" + fn.text + "' is not generic, so it takes "
                              "no type arguments");
        return genCall(n, sig, args);
      }
    }
    if (targs)
      return fail(*targs, "only a generic function takes type arguments here; "
                          "a constructor takes them from its type, as in "
                          "'let r : option u8 = Some x'");
    if (!local && fn.flags != "prelude" && types_.isCtorName(fn.text)) {
      if (argc != 1) return fail(n, "'" + fn.text + "' takes one payload");
      const Node &arg = *n.kids[1];
      // A generic constructor with no expected instance takes its type
      // arguments from the payload: `Some x` with x : u8 is option<u8>.
      std::optional<TV> early;
      const sema::Ctor *c = nullptr;
      if (!types_.ctor(fn.text) && !instanceFor(fn.text, expected)) {
        if (arg.kind != NodeKind::Unit) {
          early = genExpr(arg, Type());
          if (!early) return std::nullopt;
        }
        c = ctorFor(fn, fn.text, expected, early ? early->type : Type());
      } else {
        c = ctorFor(fn, fn.text, expected, std::nullopt);
      }
      if (!c) return std::nullopt;
      // `Ok ()` is `Ok` when the payload type is unit.
      if (!c->payload) {
        if (arg.kind == NodeKind::Unit) return genCtor(n, *c, std::nullopt);
        return fail(n, "'" + fn.text + "' takes no payload");
      }
      R v = early ? early : genExpr(arg, c->payload);
      if (!v) return v;
      R cv = coerce(*v, c->payload, arg);
      if (!cv) return cv;
      return genCtor(n, *c, *cv);
    }
    if (fn.flags == "prelude" && (fn.text == "#is" || fn.text == "#payload"))
      return genMatchBuiltin(n);
    if (!local) {
      if (fn.text == "abort") {
        if (argc != 1 || n.kids[1]->kind != NodeKind::Unit)
          return fail(n, "'abort' takes '()'");
        return genAbort(n, expected);
      }
      if (fn.text == "bnot") {
        if (argc != 1) return fail(n, "'bnot' takes one argument");
        return genBNot(n, *n.kids[1], expected);
      }
      if (const char *op = builtinOperator(fn.text)) {
        if (argc != 2)
          return fail(n, "'" + fn.text + "' takes two arguments");
        return genBinary(n, op, *n.kids[1], *n.kids[2], expected);
      }
      if (fn.text == "int" || fn.text == "real") {
        if (argc != 1) return fail(n, "'" + fn.text + "' takes one argument");
        return genExactConversion(n, fn.text, *n.kids[1]);
      }
      if (fn.text == "len") {
        if (argc != 1) return fail(n, "'len' takes one argument");
        R buf = genExpr(*n.kids[1], Type());
        if (!buf) return buf;
        if (!mlir::isa<ArrayType, SliceType>(buf->type))
          return fail(*n.kids[1], "'len' needs an array or slice, found " +
                                      typeName(buf->type));
        Value i = create<LenOp>(l, b_.getIndexType(), buf->value);
        Type usize = types_.usize();
        return TV{create<FromIndexOp>(l, usize, i), usize};
      }
      if (fn.text == "old") {
        if (!contract_) return fail(n, "'old' is only allowed in contracts");
        if (argc != 1) return fail(n, "'old' takes one argument");
        R v = genExpr(*n.kids[1], Type());
        if (!v) return v;
        return TV{create<contract::OldOp>(l, v->type, v->value), v->type};
      }
    }
    return fail(fn, "'" + fn.text + "' is not a function");
  }

  R genCall(const Node &n, const sema::FuncSig &sig,
            const std::vector<const Node *> &args,
            const std::vector<std::optional<TV>> *early = nullptr) {
    if (args.size() != sig.params.size())
      return fail(n, "'" + sig.name + "' takes " +
                         plural(sig.params.size(), "argument") + ", given " +
                         std::to_string(args.size()) +
                         "; partial application is not supported yet");
    if (!sig.result)
      return fail(n, "'" + sig.name + "' is used before its return type is "
                     "known; annotate it, as in 'let " + sig.name +
                     " ... : T = ...'");
    if (sig.item && hasFlag(*sig.item, "spec") && !contract_ && !ghost_)
      return fail(n, "'" + sig.name + "' is a spec function, so it can be "
                     "used only in contracts, spec functions and lemmas");
    if (sig.item && hasFlag(*sig.item, "lemma") && contract_)
      return fail(n, "'" + sig.name + "' is a lemma: call it as a statement, "
                     "and its postcondition holds after the call");
    // A lemma's call is erased from code, so its arguments are
    // specification, which may use spec functions, `int` and `real`.
    bool savedGhost = ghost_;
    if (sig.item && hasFlag(*sig.item, "lemma")) ghost_ = true;
    struct Restore {
      bool &flag, value;
      ~Restore() { flag = value; }
    } restoreGhost{ghost_, savedGhost};
    llvm::SmallVector<Value> operands;
    for (size_t i = 0; i < args.size(); ++i) {
      R a = early && (*early)[i] ? (*early)[i]
                                 : genExpr(*args[i], sig.params[i].type);
      if (!a) return a;
      R c = coerce(*a, sig.params[i].type, *args[i]);
      if (!c) return c;
      if (writes(sig.params[i]) && isConstantData(c->value))
        return fail(*args[i], "constant data cannot be passed to '" +
                                  sig.params[i].name + "', which is 'out' or "
                                  "'inout'");
      operands.push_back(c->value);
    }
    return emitCall(n, sig, operands);
  }

  // A call of a generic function: the type arguments come from `targs`
  // (`f<u8, t = u16>`), then from the arguments whose written types mention
  // a type parameter, then from the type the call is expected to have. The
  // call goes to the instance for those arguments, `f<u8>`, which is made
  // on first use and generated after the current function.
  R genGenericCall(const Node &n, const sema::FuncSig &generic,
                   const Node *targs, const std::vector<const Node *> &args,
                   Type expected) {
    const std::vector<std::string> &params = generic.typeParams;
    std::map<std::string, Type> bound;
    std::map<std::string, std::string> named;
    if (!bindTypeArgs(generic, targs, bound, &named)) return std::nullopt;

    std::vector<const Node *> valueParams = valueParamsOf(generic);
    if (args.size() != valueParams.size())
      return fail(n, "'" + generic.name + "' takes " +
                         plural(valueParams.size(), "argument") + ", given " +
                         std::to_string(args.size()) +
                         "; partial application is not supported yet");

    // Arguments whose types mention a type parameter not yet known are
    // generated first, on their own, and their types bind the parameters.
    std::vector<std::optional<TV>> early(args.size());
    for (size_t i = 0; i < args.size(); ++i) {
      const Node &p = *valueParams[i];
      if (p.kids.empty() || p.kids[0]->kind != NodeKind::Annot)
        return fail(p, "parameter '" + p.text +
                           "' needs a type annotation for now");
      const Node &annot = *p.kids[0];
      if (!mentionsUnbound(*annot.kids[1], params, bound)) continue;
      early[i] = genExpr(*args[i], Type());
      if (!early[i]) return std::nullopt;
      if (!types_.unify(annot, early[i]->type, params, bound))
        return fail(*args[i], "'" + p.text + "' cannot have type " +
                                  typeName(early[i]->type) + " here: " +
                                  clashMessage(annot, early[i]->type, bound));
    }
    if (const Node *retAnnot = retAnnotOf(generic))
      if (expected && !isUnit(expected))
        types_.unify(*retAnnot, expected, params, bound);
    for (const std::string &t : params)
      if (!bound.count(t))
        return fail(n, "cannot tell what '" + t + "' is in this call of '" +
                           generic.name + "'; give it, as in '" +
                           generic.name + "<" + t + " = u8>'");
    Choice choice;
    std::optional<std::string> why =
        constraintsUnmet(generic, bound, named, &choice);
    if (!why) {
      sema::FuncSig trialSig = generic;
      trialSig.typeArgs = bound;
      trialSig.result = Type();
      if (!substitute(trialSig, why) && !why) return std::nullopt;
    }
    if (options_.explanations && !checking_ &&
        n.loc.line == options_.explainLine) {
      options_.explanations->push_back(
          {n.loc, "the call of the generic '" + generic.name + "' has 1 "
                  "candidate"});
      options_.explanations->push_back(
          {n.loc, "  the generic '" + generic.name + "': " +
                      (why ? "removed: " + *why : "viable, and chosen")});
    }
    if (why) return fail(n, *why);
    sema::FuncSig *inst = genericInstance(generic, bound, choice);
    if (!inst) return std::nullopt;
    return genCall(n, *inst, args, &early);
  }

  // The functions a written name may call: one, or an overload set.
  std::vector<sema::FuncSig *> overloadSet(const std::string &name) {
    std::vector<sema::FuncSig *> out;
    // An instance made through an adapter calls the adapter's functions,
    // in place of any with the same parameter types.
    if (auto a = adapted_.find(name); a != adapted_.end())
      for (const std::string &symbol : a->second)
        if (auto s = sigs_.find(symbol); s != sigs_.end())
          out.push_back(&s->second);
    auto replaced = [&](const sema::FuncSig &f) {
      for (const sema::FuncSig *o : out) {
        if (o->params.size() != f.params.size() || f.isGeneric()) continue;
        bool same = true;
        for (size_t i = 0; same && i < f.params.size(); ++i)
          same = o->params[i].type == f.params[i].type;
        if (same) return true;
      }
      return false;
    };
    size_t adapters = out.size();
    auto it = overloads_.find(name);
    if (it != overloads_.end())
      for (const std::string &symbol : it->second)
        if (auto s = sigs_.find(symbol); s != sigs_.end())
          if (!adapters || !replaced(s->second)) out.push_back(&s->second);
    // In a generic body, the requirements its constraints promise.
    if (auto r = promisedFns_.find(name); r != promisedFns_.end())
      for (sema::FuncSig *sig : r->second) out.push_back(sig);
    return out;
  }

  // A call of an overloaded name (ADR 0034). Each argument that is not an
  // integer literal is generated once, at its own type. A candidate is
  // viable if it takes that many arguments, its type parameters can be
  // deduced, and each argument converts to its parameter. A candidate beats
  // another if it is as good for every argument and better for one (an
  // exact type over a conversion), or equal on all of them and not
  // generic while the other is. The unique candidate that beats every
  // other viable one is called.
  R genOverloadedCall(const Node &n, const std::string &name,
                      const std::vector<sema::FuncSig *> &set,
                      const Node *targs, const std::vector<const Node *> &args,
                      Type expected) {
    std::vector<std::optional<TV>> early(args.size());
    for (size_t i = 0; i < args.size(); ++i)
      if (!isLiteral(*args[i])) {
        early[i] = genExpr(*args[i], Type());
        if (!early[i]) return std::nullopt;
      }
    struct Candidate {
      sema::FuncSig *sig;  // the candidate, or a generic's instance
      bool generic = false;
      std::map<std::string, Type> bound;
      std::vector<int> score;  // per argument: 2 exact, 1 conversion
      const sema::FuncSig *origin = nullptr;  // the overload itself
      Choice choice;                          // its adapters
      std::string label;
    };
    // The signatures of generic instances that are only being considered:
    // an instance is made, and so generated and proved, only if it wins.
    std::deque<sema::FuncSig> trial;
    size_t generics = 0;
    for (sema::FuncSig *cand : set) generics += cand->isGeneric();
    std::vector<Candidate> viable;
    std::vector<std::string> rejected;
    auto argTypes = [&] {
      std::string out = "(";
      for (size_t i = 0; i < args.size(); ++i)
        out += (i ? ", " : "") +
               (early[i] ? typeName(early[i]->type) : "an integer literal");
      return out + ")";
    };
    for (sema::FuncSig *cand : set) {
      std::string label =
          !cand->isGeneric() ? "'" + cand->name + "'"
          : generics == 1    ? "the generic '" + name + "'"
                             : "the generic '" + name + "' at line " +
                                std::to_string(cand->item->loc.line);
      sema::FuncSig *sig = cand;
      std::map<std::string, Type> bound;
      // The adapters the call names, and those this candidate uses.
      std::map<std::string, std::string> named;
      Choice choice;
      if (cand->isGeneric()) {
        std::vector<const Node *> vps = valueParamsOf(*cand);
        if (vps.size() != args.size()) {
          rejected.push_back(label + " takes " +
                             plural(vps.size(), "argument"));
          continue;
        }
        if (!bindTypeArgs(*cand, targs, bound, &named)) return std::nullopt;
        bool clash = false;
        for (size_t i = 0; i < args.size() && !clash; ++i) {
          const Node &p = *vps[i];
          if (!early[i] || p.kids.empty() ||
              p.kids[0]->kind != NodeKind::Annot)
            continue;
          clash = !types_.unify(*p.kids[0], early[i]->type, cand->typeParams,
                                bound);
        }
        if (const Node *ra = retAnnotOf(*cand))
          if (expected && !isUnit(expected))
            types_.unify(*ra, expected, cand->typeParams, bound);
        std::string unknown;
        for (const std::string &t : cand->typeParams)
          if (!bound.count(t)) unknown = t;
        if (clash || !unknown.empty()) {
          rejected.push_back(label + (clash ? " does not fit these types"
                                            : ": '" + unknown +
                                                  "' cannot be deduced"));
          continue;
        }
        // A type that does not meet a constraint removes the candidate.
        if (std::optional<std::string> why =
                constraintsUnmet(*cand, bound, named, &choice)) {
          rejected.push_back(label + ": " + *why);
          continue;
        }
        trial.push_back(*cand);
        sig = &trial.back();
        sig->typeArgs = bound;
        sig->result = Type();
        // A signature that cannot be formed for these types removes the
        // candidate (ADR 0035, "What may fail softly").
        std::optional<std::string> soft;
        bool formed = substitute(*sig, soft);
        if (!formed && soft) {
          rejected.push_back(label + ": " + *soft);
          continue;
        }
        if (!formed) return std::nullopt;
      } else if (targs) {
        rejected.push_back(label + " is not generic");
        continue;
      } else if (sig->params.size() != args.size()) {
        rejected.push_back(label + " takes " +
                           plural(sig->params.size(), "argument"));
        continue;
      }
      Candidate c{sig, cand->isGeneric(), bound, {}, cand, choice, label};
      bool fits = true;
      for (size_t i = 0; i < args.size() && fits; ++i) {
        Type want = sig->params[i].type;
        int score = 0;
        if (!early[i])
          score = mlir::isa<IntType>(want) ? 2 : 0;
        else if (early[i]->type == want)
          score = 2;
        else if (converts(early[i]->type, want))
          score = 1;
        fits = score > 0;
        c.score.push_back(score);
      }
      if (!fits) {
        rejected.push_back(label + " does not take these types");
        continue;
      }
      viable.push_back(std::move(c));
    }
    // `--explain-overloads`: every candidate, why each one that was
    // removed was, and which one the call chose (ADR 0035).
    auto explain = [&](const Candidate *chosen, const std::string &outcome) {
      if (!options_.explanations || checking_ ||
          n.loc.line != options_.explainLine)
        return;
      auto note = [&](std::string m) {
        options_.explanations->push_back({n.loc, std::move(m)});
      };
      note("the call of '" + name + "' with " + argTypes() + " has " +
           plural(viable.size() + rejected.size(), "candidate"));
      for (const Candidate &c : viable)
        note("  " + c.label + ": " +
             (&c == chosen ? std::string("viable, and chosen")
                           : std::string("viable")));
      for (const std::string &r : rejected) note("  removed: " + r);
      if (!outcome.empty()) note("  " + outcome);
    };
    if (viable.empty()) explain(nullptr, "no candidate is left");
    if (viable.empty() && checking_) {
      std::vector<Type> abstract;
      for (const std::optional<TV> &e : early)
        if (e && archetypes_.count(e->type)) abstract.push_back(e->type);
      if (!abstract.empty()) return fail(n, notPromised(name, abstract));
    }
    if (viable.empty()) {
      std::string why = "no overload of '" + name + "' takes " + argTypes();
      for (const std::string &r : rejected) why += "; " + r;
      return fail(n, why);
    }
    auto beats = [&](const Candidate &a, const Candidate &b) {
      bool better = false;
      for (size_t i = 0; i < a.score.size(); ++i) {
        if (a.score[i] < b.score[i]) return false;
        better = better || a.score[i] > b.score[i];
      }
      if (better || (!a.generic && b.generic)) return true;
      // Between generics, the more specific parameter patterns, then the
      // stronger constraints.
      return a.generic && b.generic &&
             moreSpecific(*a.origin, *b.origin) > 0;
    };
    const Candidate *best = nullptr;
    for (const Candidate &c : viable) {
      bool all = true;
      for (const Candidate &o : viable)
        if (&o != &c && !beats(c, o)) all = false;
      if (all) best = &c;
    }
    if (!best) {
      // Candidates no other beats, all with the same parameter types:
      // overloads told apart by their preconditions (ADR 0034). The call
      // goes to the least specific; the verifier may choose a more
      // specific one whose precondition it proves at the call.
      std::vector<const Candidate *> top;
      for (const Candidate &c : viable) {
        bool beaten = false;
        for (const Candidate &o : viable)
          if (&o != &c && beats(o, c)) beaten = true;
        if (!beaten) top.push_back(&c);
      }
      auto twins = top.empty() ? preconditionOrder_.end()
                               : preconditionOrder_.find(top[0]->sig->name);
      bool tied = top.size() > 1 && twins != preconditionOrder_.end();
      for (const Candidate *c : top)
        tied = tied && !c->generic &&
               llvm::is_contained(twins->second, c->sig->name);
      if (tied) {
        std::vector<std::string> order;
        for (const std::string &sym : twins->second)
          for (const Candidate *c : top)
            if (c->sig->name == sym) order.push_back(sym);
        sema::FuncSig &general = sigs_.at(order.back());
        // A contract means the same in every build: it uses the general
        // overload.
        if (!contract_) {
          llvm::SmallVector<mlir::Attribute> refs;
          for (const std::string &sym : order)
            refs.push_back(mlir::FlatSymbolRefAttr::get(&ctx_, sym));
          openCandidates_ = b_.getArrayAttr(refs);
          openFor_ = order.back();
        }
        explain(nullptr, "the verifier chooses among them by precondition, "
                         "most specific first");
        return genCall(n, general, args, &early);
      }
      std::string why = "the call of '" + name + "' with " + argTypes() +
                        " is ambiguous between";
      bool generic = false;
      for (size_t i = 0; i < viable.size(); ++i) {
        const std::string &l = viable[i].label;
        bool quoted = !l.empty() && l[0] == '\'';
        why += (i ? (i + 1 == viable.size() ? " and " : ", ") : " ") +
               (quoted ? l : l.substr(4));
        generic = generic || viable[i].generic;
      }
      explain(nullptr, "none of them is the most specific");
      return fail(n, why + (generic ? "; neither is more specific than the "
                                      "other"
                                    : "; give the arguments' types, as in "
                                      "'let x : u8 = ...'"));
    }
    explain(best, "");
    sema::FuncSig *callee = best->sig;
    if (best->generic) {
      callee = genericInstance(*best->origin, best->bound, best->choice);
      if (!callee) return std::nullopt;
    }
    return genCall(n, *callee, args, &early);
  }

  // Whether `coerce` accepts a value of type `from` where `to` is wanted.
  static bool converts(Type from, Type to) {
    if (mlir::isa<IntType>(from) && mlir::isa<IntType>(to)) return true;
    if (auto a = mlir::dyn_cast<ArrayType>(from))
      if (auto sl = mlir::dyn_cast<SliceType>(to))
        return a.getElementType() == sl.getElementType();
    return false;
  }

  // The value parameters of a function as written: not `()` and not the
  // type parameters.
  static std::vector<const Node *> valueParamsOf(const sema::FuncSig &sig) {
    std::vector<const Node *> out;
    for (const syntax::NodePtr &p : sig.item->kids[0]->kids)
      if (p->kind != NodeKind::ParamUnit && !sema::isTypeParam(*p))
        out.push_back(p.get());
    return out;
  }

  static const Node *retAnnotOf(const sema::FuncSig &sig) {
    const Node &ret = *sig.item->kids[1];
    return ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
                   ret.kids[0]->kind == NodeKind::Annot
               ? ret.kids[0].get()
               : nullptr;
  }

  // --- concepts (ADR 0034) -------------------------------------------

  // Adapters by name: the concept and arguments each adapts, `Same<u8>`,
  // and its functions by name.
  struct AdapterInfo {
    std::string name;
    std::string key;      // `Same<u8>`
    std::string spelled;  // `Same u8`
    std::map<std::string, std::vector<std::string>> fns;
  };
  std::map<std::string, AdapterInfo> adapters_;
  // What a call's use check chose: the adapter for each concept and
  // arguments, and the names that call the adapters' functions.
  struct Choice {
    std::map<std::string, std::vector<std::string>> adapted;
    std::map<std::string, std::string> adapterFor;
  };

  // --- type-level metaprograms (ADR 0035, step 1) ---------------------

  // Resolves a candidate's signature for its type arguments. A type that a
  // metaprogram cannot form leaves its reason in `soft` instead of an
  // error, so the caller can remove the candidate (ADR 0035).
  bool substitute(sema::FuncSig &sig, std::optional<std::string> &soft) {
    std::optional<std::string> *saved = softFailure_;
    softFailure_ = &soft;
    bool ok = sema::resolveSignature(sig, types_, diags_);
    softFailure_ = saved;
    return ok;
  }

  // Makes every type-level metaprogram callable from types and `where`
  // predicates.
  void collectTypeFunctions(const Node &program) {
    for (const syntax::NodePtr &item : program.kids) {
      if (!syntax::isTypeLevelMetaItem(*item)) continue;
      const Node &ret = *item->kids[1]->kids[0]->kids[1];
      auto &table = ret.kind == NodeKind::TypeKind ? typeFns_ : typePredicates_;
      if (typeFns_.count(item->text) || typePredicates_.count(item->text)) {
        diags_.error(item->loc, "'" + item->text + "' is already defined");
        continue;
      }
      table[item->text] = item.get();
      interp_.define(*item);
    }
    checkTotality();
    meta::TypeHost host;
    host.named = [this](const std::string &name) -> std::optional<std::string> {
      Type t = types_.builtin(name);
      if (!t) t = types_.named(name);
      if (!t) return std::nullopt;
      return typeValue(t)->s;
    };
    host.info = [this](const std::string &spelling) {
      return typeInfo(typeValues_.at(spelling));
    };
    interp_.setTypeHost(std::move(host));
    types_.setTypeFunctions(
        [this](const std::string &name) { return typeFns_.count(name) != 0; },
        [this](const std::string &name, llvm::ArrayRef<Type> args,
               syntax::SourceLoc at) {
          return callTypeFunction(name, args, at);
        });
  }

  // Decides which type-level metaprograms terminate (ADR 0035, "Constraints
  // are total"): each one on its own, then through what it calls. One that
  // does not is only an error where a type or a constraint uses it.
  void checkTotality() {
    auto isMeta = [this](const std::string &n) {
      return typeFns_.count(n) || typePredicates_.count(n);
    };
    std::map<std::string, std::set<std::string>> callees;
    for (auto *table : {&typeFns_, &typePredicates_})
      for (auto &[name, item] : *table) {
        // A name a type-level metaprogram cannot call is caught when it
        // runs; only the metaprograms it can call matter here.
        if (std::optional<std::string> why =
                meta::checkOwnTotality(*item, isMeta, callees[name]))
          notTotal_[name] = *why;
      }
    // Through its callees: a cycle between metaprograms would need one
    // measure that all of them decrease, which is not supported yet.
    std::map<std::string, int> state;  // 1 visiting, 2 done
    std::function<void(const std::string &, std::vector<std::string> &)>
        visit = [&](const std::string &name, std::vector<std::string> &path) {
          state[name] = 1;
          path.push_back(name);
          for (const std::string &c : callees[name]) {
            if (state[c] == 1) {
              std::string cycle;
              auto from = std::find(path.begin(), path.end(), c);
              for (auto it = from; it != path.end(); ++it)
                cycle += "'" + *it + "' calls ";
              cycle += "'" + c + "'";
              for (auto it = from; it != path.end(); ++it)
                if (!notTotal_.count(*it))
                  notTotal_[*it] = "it is mutually recursive (" + cycle +
                                   "), which is not supported yet";
              continue;
            }
            if (state[c] == 0) visit(c, path);
            if (notTotal_.count(c) && !notTotal_.count(name))
              notTotal_[name] = "it calls '" + c + "', which may not "
                                "terminate: " + notTotal_.at(c);
          }
          path.pop_back();
          state[name] = 2;
        };
    for (auto &[name, cs] : callees) {
      std::vector<std::string> path;
      if (state[name] == 0) visit(name, path);
    }
  }

  // The error for a use of a metaprogram that may not terminate, or
  // nothing. `use` says where it is used: "a type" or "a constraint".
  bool reportNotTotal(const std::string &name, syntax::SourceLoc at,
                      const char *use) {
    auto it = notTotal_.find(name);
    if (it == notTotal_.end()) return false;
    std::string key = name + "@" + std::to_string(at.line) + ":" +
                      std::to_string(at.column);
    if (!reportedNotTotal_.insert(key).second) return true;
    diags_.error(at, "'" + name + "' is used in " + use +
                         ", so it must terminate, but " + it->second);
    return true;
  }

  // The type-level metaprograms that `n` names.
  void metaNamesIn(const Node &n, std::vector<const Node *> &out) const {
    if (n.kind == NodeKind::Name &&
        (typeFns_.count(n.text) || typePredicates_.count(n.text)))
      out.push_back(&n);
    for (const syntax::NodePtr &k : n.kids) metaNamesIn(*k, out);
  }

  // A metaprogram error, unless it ran out of steps, which no
  // metaprogram that is proved to terminate should, so that is the
  // compiler's fault (ADR 0035).
  static bool isInternal(const meta::MetaError &e) {
    return e.message.rfind("the metaprogram ran out of fuel", 0) == 0;
  }

  std::string metaFailure(const meta::MetaError &e) {
    if (isInternal(e))
      return "internal compiler error: a metaprogram that terminates ran "
             "out of steps (" + e.message + ")";
    return e.message;
  }

  // What a type is made of, for `type_kind`, `element`, `field_types`,
  // `type_args` and `size_of`.
  meta::TypeInfo typeInfo(Type t) {
    meta::TypeInfo info;
    info.size = byteSize(t);
    if (mlir::isa<IntType>(t)) {
      info.kind = "int";
    } else if (t == types_.boolType()) {
      info.kind = "bool";
    } else if (types_.isUnit(t)) {
      info.kind = "unit";
    } else if (auto a = mlir::dyn_cast<ArrayType>(t)) {
      info.kind = "array";
      info.element = typeValue(a.getElementType())->s;
      info.length = static_cast<int64_t>(a.getLength());
    } else if (auto sl = mlir::dyn_cast<SliceType>(t)) {
      info.kind = "slice";
      info.element = typeValue(sl.getElementType())->s;
    } else if (types_.isVariant(t)) {
      info.kind = "variant";
      for (const sema::Ctor *c : types_.ctorsOf(t))
        if (c->payload) info.fields.push_back(typeValue(c->payload)->s);
    } else if (auto r = mlir::dyn_cast<RecordType>(t)) {
      info.kind = standIns_.contains(t) ? "unknown" : "record";
      for (Type f : r.getFieldTypes())
        info.fields.push_back(typeValue(f)->s);
    } else {
      info.kind = "unknown";
    }
    if (const sema::Instance *inst = types_.instanceOf(t)) {
      info.generic = inst->generic;
      for (Type a : inst->args) info.args.push_back(typeValue(a)->s);
    }
    return info;
  }

  // A type as a metaprogram's value.
  meta::ValuePtr typeValue(Type t) {
    std::string spelling = sema::typeName(t);
    typeValues_[spelling] = t;
    return meta::Interpreter::typeValue(std::move(spelling));
  }

  // `size_of t`: the bytes a value takes. An integer takes the smallest of
  // 1, 2, 4 or 8 bytes that holds its range, a bool 1, an array its
  // elements', and a record the sum of its fields' (before layout packs
  // them, ADR 0030). A slice and a stand-in have no fixed size.
  std::optional<int64_t> byteSize(Type t) {
    if (standIns_.contains(t)) return std::nullopt;
    if (auto i = mlir::dyn_cast<IntType>(t)) {
      llvm::APInt lo = i.getLo(), hi = i.getHi();
      unsigned bits = lo.isNegative()
                          ? std::max(lo.getSignificantBits(),
                                     hi.getSignificantBits())
                          : hi.getActiveBits();
      for (unsigned w : {8u, 16u, 32u, 64u})
        if (bits <= w) return w / 8;
      return std::nullopt;
    }
    if (t == types_.boolType()) return 1;
    if (types_.isUnit(t)) return 0;
    if (auto a = mlir::dyn_cast<ArrayType>(t)) {
      std::optional<int64_t> e = byteSize(a.getElementType());
      if (!e) return std::nullopt;
      return *e * static_cast<int64_t>(a.getLength());
    }
    if (auto r = mlir::dyn_cast<RecordType>(t)) {
      int64_t total = 0;
      for (Type f : r.getFieldTypes()) {
        std::optional<int64_t> n = byteSize(f);
        if (!n) return std::nullopt;
        total += *n;
      }
      return total;
    }
    return std::nullopt;
  }

  // `widen u8` in a type: runs the metaprogram `widen` on u8. Its failure
  // is an error at the type for now; ADR 0035 step 3 makes it remove an
  // overload candidate instead.
  Type callTypeFunction(const std::string &name, llvm::ArrayRef<Type> args,
                        syntax::SourceLoc at) {
    std::string spelled = name;
    for (Type a : args) {
      std::string t = sema::typeName(a);
      spelled += t.find(' ') == std::string::npos ? " " + t : " (" + t + ")";
    }
    if (reportNotTotal(name, at, "a type")) return {};
    size_t arity = interp_.arity(name);
    if (args.size() != arity) {
      diags_.error(at, "'" + name + "' takes " + std::to_string(arity) +
                           " type argument" + (arity == 1 ? "" : "s") +
                           ", found " + std::to_string(args.size()));
      return {};
    }
    // A stand-in stands for every type, and so does what a metaprogram
    // makes of it: `widen t` is known only for each instance.
    for (Type a : args)
      if (standIns_.contains(a)) {
        Type r = RecordType::get(&ctx_, spelled, {}, {});
        standIns_.insert(r);
        if (checking_) opaqueStandIn_ = true;
        return r;
      }
    std::vector<meta::ValuePtr> values;
    for (Type a : args) values.push_back(typeValue(a));
    interp_.setSite(at);
    try {
      meta::ValuePtr v = interp_.call(name, std::move(values));
      if (v->kind != meta::Value::Kind::Type) {
        diags_.error(at, "'" + name + "' must return a type, but returned " +
                             meta::Interpreter::kindName(v->kind));
        return {};
      }
      return typeValues_.at(v->s);
    } catch (const meta::MetaError &e) {
      std::string why = "the type '" + spelled + "' cannot be formed: " +
                        metaFailure(e);
      // A failure removes the candidate being substituted; running out of
      // steps never does.
      if (softFailure_ && !isInternal(e)) {
        if (!*softFailure_) *softFailure_ = why;
      } else {
        diags_.error(at, why);
      }
    } catch (const meta::Deferred &d) {
      diags_.error(at, "the type '" + spelled + "' cannot be formed: it "
                       "needs the type '" + d.type + "'");
    }
    return {};
  }

  // A `where` predicate as written: `size_of t <= 8`. Only an argument of
  // a call is parenthesised.
  static std::string predicateText(const Node &n, bool nested = false) {
    static const std::map<std::string, std::string> infix = {
        {"eq", "="},  {"ne", "<>"}, {"lt", "<"},       {"gt", ">"},
        {"le", "<="}, {"ge", ">="}, {"add", "+"},      {"sub", "-"},
        {"mul", "*"}, {"div", "/"}, {"rem", "%"},      {"and", "&&"},
        {"or", "||"}, {"implies", "==>"},              {"iff", "<==>"},
    };
    switch (n.kind) {
      case NodeKind::Name: case NodeKind::IntLit: case NodeKind::BoolLit:
      case NodeKind::TypeName:
        return n.text;
      case NodeKind::StringLit:
        return "\"" + n.text + "\"";
      case NodeKind::Apply: {
        std::string out;
        auto op = n.kids[0]->kind == NodeKind::Name
                      ? infix.find(n.kids[0]->text)
                      : infix.end();
        if (op != infix.end() && n.kids.size() == 3)
          out = predicateText(*n.kids[1]) + " " + op->second + " " +
                predicateText(*n.kids[2]);
        else
          for (size_t i = 0; i < n.kids.size(); ++i)
            out += (i ? " " : "") + predicateText(*n.kids[i], true);
        return nested ? "(" + out + ")" : out;
      }
      default:
        return "...";
    }
  }

  // Why the predicate `q` of a `where` is false for the type arguments
  // `bound`, or nothing when it holds. With a stand-in among them, it holds
  // only when the generic being defined promises the same predicate.
  std::optional<std::string> predicateUnmet(
      const Node &q, const std::map<std::string, Type> &bound) {
    std::string text = predicateText(q);
    std::vector<const Node *> metas;
    metaNamesIn(q, metas);
    for (const Node *m : metas)
      if (reportNotTotal(m->text, m->loc, "a constraint"))
        return "its constraint '" + text + "' may not terminate";
    bool abstract = false;
    std::map<std::string, std::string> rename;
    for (auto &[name, t] : bound)
      if (archetypes_.count(t)) {
        abstract = true;
        rename[name] = archetypes_.at(t).name;
      }
    if (abstract) {
      auto dumped = [](const Node &n) {
        std::ostringstream os;
        syntax::dump(os, n);
        return os.str();
      };
      NodePtr copy = syntax::clone(q);
      renameNames(*copy, rename, nullptr);
      std::string want = dumped(*copy);
      for (auto &[t, a] : archetypes_)
        for (const Node *p : a.predicates)
          if (dumped(*p) == want) return std::nullopt;
      return "the constraint '" + text + "' is not promised by the "
             "constraints of the function being defined";
    }
    std::vector<std::pair<std::string, meta::ValuePtr>> env;
    std::string forTypes;
    for (auto &[name, t] : bound) {
      env.emplace_back(name, typeValue(t));
      forTypes += (forTypes.empty() ? "" : ", ") + name + " = " +
                  sema::typeName(t);
    }
    interp_.setSite(q.loc);
    try {
      meta::ValuePtr v = interp_.evalWith(q, env);
      if (v->kind != meta::Value::Kind::Bool) {
        diags_.error(q.loc, "the constraint '" + text + "' must be a bool, "
                            "but it is " +
                            meta::Interpreter::kindName(v->kind));
        return "its constraint '" + text + "' is not a bool";
      }
      if (v->b) return std::nullopt;
      return "the constraint '" + text + "' is false for " + forTypes;
    } catch (const meta::MetaError &e) {
      // The metaprograms a constraint uses terminate, so a failure removes
      // the candidate, with the reason (ADR 0035). Running out of steps
      // anyway is the compiler's fault.
      std::string why = "the constraint '" + text + "' cannot be checked "
                        "for " + forTypes + ": " + metaFailure(e);
      if (isInternal(e)) diags_.error(q.loc, why);
      return why;
    } catch (const meta::Deferred &d) {
      diags_.error(q.loc, "the constraint '" + text + "' needs the type '" +
                              d.type + "'");
    }
    return "its constraint '" + text + "' cannot be checked";
  }

  // Records every concept and checks its form, then checks that each
  // generic function's constraints name concepts with the right number of
  // type arguments.
  void collectConcepts(const Node &program) {
    // Reported in source order once everything is checked.
    std::vector<std::pair<syntax::SourceLoc, std::string>> errors;
    auto error = [&](syntax::SourceLoc at, std::string message) {
      errors.emplace_back(at, std::move(message));
    };
    for (const syntax::NodePtr &item : program.kids) {
      if (!syntax::isConceptItem(*item)) continue;
      const std::string &name = item->text;
      if (overloads_.count(name) || types_.named(name) ||
          types_.generic(name) || concepts_.count(name)) {
        error(item->loc, "'" + name + "' is already defined");
        continue;
      }
      bool ok = true;
      for (const syntax::NodePtr &p : item->kids[0]->kids)
        if (!sema::isTypeParam(*p)) {
          error(p->loc, "a concept's parameters are types, as in "
                               "'(t : type)'");
          ok = false;
        }
      const Node &body = *item->kids[3];
      if (body.kind != NodeKind::Sig) {
        error(body.loc, "a concept's body must be a 'sig ... end' "
                               "for now");
        continue;
      }
      for (const syntax::NodePtr &r : body.kids) {
        if (r->kind == NodeKind::SigVal) {
          const Node &annot = *r->kids[0];
          if (annot.kids[1]->kind != NodeKind::ArrowType) {
            error(r->loc, "the requirement '" + r->text +
                                     "' must be a function, as in 'let " +
                                     r->text + " : (a : t) -> bool'");
            ok = false;
          } else if (!r->kids[2]->kids.empty()) {
            for (const Node *d = annot.kids[1].get();
                 d->kind == NodeKind::ArrowType; d = d->kids[1].get())
              if (d->kids[0]->text.empty()) {
                error(r->loc, "the requirement '" + r->text +
                                         "' has a contract, so it must name "
                                         "its parameters, as in '(a : t) -> "
                                         "bool'");
                ok = false;
                break;
              }
          }
        } else if (r->kind == NodeKind::SigInclude) {
          // Checked once every concept is known.
        } else if (r->kind == NodeKind::SigLemma) {
        } else {
          error(r->loc, "a concept may hold functions, laws and "
                               "'include' for now; type requirements are not "
                               "supported yet");
          ok = false;
        }
      }
      if (ok) concepts_[name] = item.get();
    }
    for (auto &[name, item] : concepts_)
      for (const syntax::NodePtr &r : item->kids[3]->kids)
        if (r->kind == NodeKind::SigInclude)
          checkConceptUse(r->text, r->kids.size(), r->loc, errors);
    // Adapters: `let adapter name : C u8 = struct ... end`.
    for (const syntax::NodePtr &item : program.kids) {
      if (item->kind != NodeKind::Adapter) continue;
      const std::string &name = item->text;
      const Node &target = *item->kids[0];
      std::string cname;
      std::vector<const Node *> argNodes;
      if (target.kind == NodeKind::TypeApp) {
        cname = target.kids[0]->text;
        for (size_t i = 1; i < target.kids.size(); ++i)
          argNodes.push_back(target.kids[i].get());
      } else if (target.kind == NodeKind::TypeName) {
        cname = target.text;
      }
      if (overloads_.count(name) || concepts_.count(name) ||
          adapters_.count(name) || types_.named(name)) {
        error(item->loc, "'" + name + "' is already defined");
        continue;
      }
      size_t before = errors.size();
      checkConceptUse(cname, argNodes.size(), target.loc, errors);
      if (errors.size() != before) continue;
      AdapterInfo a;
      a.name = name;
      std::vector<Type> args;
      bool ok = true;
      for (const Node *n : argNodes) {
        Type t = types_.resolve(*n);
        ok = ok && t;
        args.push_back(t);
      }
      if (!ok) continue;
      a.key = cname + "<" + spellTypes(args) + ">";
      a.spelled = cname;
      for (Type t : args) a.spelled += " " + typeName(t);
      for (auto &[symbol, sig] : sigs_) {
        if (sig.adapter != name) continue;
        if (sig.isGeneric()) {
          error(sig.item->loc, "an adapter's functions are not generic for "
                               "now");
          ok = false;
        }
        a.fns[sig.source()].push_back(symbol);
      }
      if (ok) adapters_[name] = std::move(a);
    }
    for (auto &[symbol, sig] : sigs_) {
      if (!sig.isGeneric()) continue;
      for (const syntax::NodePtr &p : sig.item->kids[0]->kids) {
        const Node *pred = wherePredicate(*p);
        if (!pred) continue;
        std::vector<const Node *> cs, preds;
        if (!constraintsOf(*pred, cs, &preds)) {
          error(pred->loc, "a 'where' on a type parameter names "
                                  "concepts, as in 'where Ord t' or "
                                  "'where Eq t && Hash t', or states a "
                                  "predicate, as in 'where size_of t <= 8'");
          continue;
        }
        // A metaprogram a constraint uses must terminate (ADR 0035).
        for (const Node *q : preds) {
          std::vector<const Node *> metas;
          metaNamesIn(*q, metas);
          for (const Node *m : metas)
            reportNotTotal(m->text, m->loc, "a constraint");
        }
        // A concept is met or not, and only '&&' joins it to the rest.
        for (const Node *q : preds)
          if (const Node *c = conceptIn(*q))
            error(c->loc, "the concept '" + c->text + "' can only be "
                                 "joined to other constraints by '&&'");
        for (const Node *c : cs) {
          checkConceptUse(c->kids[0]->text, c->kids.size() - 1, c->loc, errors);
          for (size_t i = 1; i < c->kids.size(); ++i)
            if (c->kids[i]->kind != NodeKind::Name)
              error(c->kids[i]->loc,
                           "a concept's argument must be a type's name for "
                           "now");
        }
      }
    }
    std::stable_sort(errors.begin(), errors.end(), [](auto &a, auto &b) {
      return std::make_pair(a.first.line, a.first.column) <
             std::make_pair(b.first.line, b.first.column);
    });
    for (auto &[at, message] : errors) diags_.error(at, message);
  }

  void checkConceptUse(
      const std::string &name, size_t given, syntax::SourceLoc at,
      std::vector<std::pair<syntax::SourceLoc, std::string>> &errors) {
    auto error = [&](syntax::SourceLoc l, std::string message) {
      errors.emplace_back(l, std::move(message));
    };
    auto it = concepts_.find(name);
    if (it == concepts_.end()) {
      error(at, "'" + name + "' is not a concept");
      return;
    }
    size_t want = 0;
    for (const syntax::NodePtr &p : it->second->kids[0]->kids)
      if (sema::isTypeParam(*p)) ++want;
    if (want != given)
      error(at, "'" + name + "' takes " +
                           plural(want, "type argument") + ", given " +
                           std::to_string(given));
  }

  // The `where` of a type parameter, `(t : type where Ord t)`, or null.
  static const Node *wherePredicate(const Node &param) {
    if (!sema::isTypeParam(param)) return nullptr;
    const Node &annot = *param.kids[0];
    return annot.kids.size() > 2 && annot.kids[2]->kind != NodeKind::None
               ? annot.kids[2].get()
               : nullptr;
  }

  // The constraints of a `where`, joined by `&&` (which expands to
  // `and`): concepts, `C t`, go to `out`, and predicates over types, such
  // as `size_of t <= 8` (ADR 0035), to `preds`. False for anything else.
  bool constraintsOf(const Node &pred, std::vector<const Node *> &out,
                     std::vector<const Node *> *preds = nullptr) {
    if (isPredicate(pred)) {
      if (preds) preds->push_back(&pred);
      return true;
    }
    if (pred.kind != NodeKind::Apply || pred.kids.empty() ||
        pred.kids[0]->kind != NodeKind::Name)
      return false;
    if (pred.kids[0]->text == "and" && pred.kids.size() == 3)
      return constraintsOf(*pred.kids[1], out, preds) &&
             constraintsOf(*pred.kids[2], out, preds);
    out.push_back(&pred);
    return true;
  }

  // A name of a concept inside `n`, or null.
  const Node *conceptIn(const Node &n) const {
    if (n.kind == NodeKind::Name && concepts_.count(n.text)) return &n;
    for (const syntax::NodePtr &k : n.kids)
      if (const Node *c = conceptIn(*k)) return c;
    return nullptr;
  }

  // Whether a conjunct of a `where` is a predicate over types rather than
  // a concept: a comparison or a connective other than `&&`, a bool, or a
  // call of a type-level metaprogram that returns a bool.
  bool isPredicate(const Node &n) const {
    if (n.kind == NodeKind::BoolLit) return true;
    if (n.kind != NodeKind::Apply || n.kids.empty() ||
        n.kids[0]->kind != NodeKind::Name)
      return false;
    static const std::set<std::string> ops = {
        "eq", "ne", "lt", "gt", "le", "ge", "or", "implies", "iff",
    };
    const std::string &head = n.kids[0]->text;
    return ops.count(head) || typePredicates_.count(head);
  }

  static std::string spellTypes(const std::vector<Type> &ts) {
    std::string out;
    for (size_t i = 0; i < ts.size(); ++i)
      out += (i ? ", " : "") + sema::typeName(ts[i]);
    return out;
  }

  // Why the type arguments `bound` do not meet the constraints of
  // `generic`, or nothing when they do (the use check).
  std::optional<std::string> constraintsUnmet(
      const sema::FuncSig &generic, const std::map<std::string, Type> &bound,
      const std::map<std::string, std::string> &named = {},
      Choice *choice = nullptr) {
    for (auto &[cname, adapter] : named) {
      bool constrains = false;
      for (const syntax::NodePtr &p : generic.item->kids[0]->kids)
        if (const Node *pred = wherePredicate(*p)) {
          std::vector<const Node *> cs;
          constraintsOf(*pred, cs);
          for (const Node *c : cs) constrains |= c->kids[0]->text == cname;
        }
      if (!constrains)
        return "'" + generic.name + "' has no constraint '" + cname +
               "' for '" + adapter + "' to adapt";
    }
    for (const syntax::NodePtr &p : generic.item->kids[0]->kids) {
      const Node *pred = wherePredicate(*p);
      if (!pred) continue;
      std::vector<const Node *> cs, preds;
      constraintsOf(*pred, cs, &preds);
      for (const Node *q : preds)
        if (std::optional<std::string> why = predicateUnmet(*q, bound))
          return why;
      for (const Node *c : cs) {
        std::vector<Type> args;
        for (size_t i = 1; i < c->kids.size(); ++i) {
          auto t = bound.find(c->kids[i]->text);
          Type ty;
          if (t != bound.end()) {
            ty = t->second;
          } else {
            Node asType;
            asType.kind = NodeKind::TypeName;
            asType.text = c->kids[i]->text;
            asType.loc = c->kids[i]->loc;
            ty = types_.resolve(asType);
          }
          if (!ty) return "a type in its constraints cannot be formed";
          args.push_back(ty);
        }
        const std::string &cname = c->kids[0]->text;
        if (std::optional<std::string> why =
                meetOrAdapt(generic, cname, args, named, choice))
          return why;
      }
    }
    return std::nullopt;
  }

  // Meets `cname` for `args` directly, or through an adapter: the one the
  // call names, the one the function being generated chose, or else the
  // only adapter for them in scope (ADR 0034, "Adapters"). Records the
  // adapter in `choice`. The reason when neither works.
  std::optional<std::string> meetOrAdapt(
      const sema::FuncSig &generic, const std::string &cname,
      const std::vector<Type> &args,
      const std::map<std::string, std::string> &named, Choice *choice) {
    std::string key = cname + "<" + spellTypes(args) + ">";
    std::string types = spellTypes(args);
    std::string meet = types + (args.size() > 1 ? " do" : " does") +
                       " not meet " + cname;
    std::string chosen;
    if (auto n = named.find(cname); n != named.end()) {
      auto a = adapters_.find(n->second);
      if (a == adapters_.end()) return "'" + n->second + "' is not an adapter";
      if (a->second.key != key)
        return "'" + n->second + "' adapts " + a->second.spelled + ", not " +
               cname + " " + types;
      chosen = n->second;
    } else if (auto f = adapterFor_.find(key); f != adapterFor_.end()) {
      chosen = f->second;
    } else {
      std::optional<std::string> why = unmet(cname, args);
      if (!why) return std::nullopt;
      std::vector<std::string> found;
      for (auto &[name, a] : adapters_)
        if (a.key == key) found.push_back(name);
      if (found.empty()) return meet + ": " + *why;
      if (found.size() > 1)
        return types + " meets " + cname + " through both '" + found[0] +
               "' and '" + found[1] + "'; name one, as in '" + generic.name +
               "<" + cname + " = " + found[0] + ">'";
      chosen = found[0];
    }
    const AdapterInfo &a = adapters_.at(chosen);
    if (std::optional<std::string> why = unmet(cname, args, &a))
      return meet + " through '" + chosen + "': " + *why;
    if (choice) {
      choice->adapterFor[key] = chosen;
      for (auto &[name, symbols] : a.fns)
        for (const std::string &sym : symbols)
          if (!llvm::is_contained(choice->adapted[name], sym))
            choice->adapted[name].push_back(sym);
    }
    return std::nullopt;
  }

  // Why `args` do not meet the concept `cname`, or nothing when they do. Decided
  // once per concept and arguments; laws and requirement contracts become
  // lemmas, proved for those arguments.
  std::optional<std::string> unmet(const std::string &cname,
                                   const std::vector<Type> &args,
                                   const AdapterInfo *via = nullptr) {
    std::string key = cname + "<" + spellTypes(args) + ">";
    if (via) key += " by " + via->name;
    for (Type t : args)
      if (archetypes_.count(t)) {
        if (promised_.count(key)) return std::nullopt;
        return "it is not promised by " + constraintsText(t);
      }
    if (auto it = met_.find(key); it != met_.end()) return it->second;
    // An `include` that comes back to this concept adds nothing new.
    met_[key] = std::nullopt;
    const Node &item = *concepts_.at(cname);
    std::map<std::string, Type> scope;
    size_t i = 0;
    for (const syntax::NodePtr &p : item.kids[0]->kids)
      if (sema::isTypeParam(*p) && i < args.size()) scope[p->text] = args[i++];
    std::vector<std::map<std::string, Type>> saved =
        types_.replaceTypeScopes({scope});
    std::optional<std::string> why = requirementsUnmet(item, key, scope, via);
    types_.replaceTypeScopes(std::move(saved));
    met_[key] = why;
    return why;
  }

  std::optional<std::string> requirementsUnmet(
      const Node &item, const std::string &key,
      const std::map<std::string, Type> &scope, const AdapterInfo *via) {
    for (const syntax::NodePtr &r : item.kids[3]->kids) {
      if (r->kind == NodeKind::SigInclude) {
        std::vector<Type> args;
        for (const syntax::NodePtr &a : r->kids) {
          Type t = types_.resolve(*a);
          if (!t) return "a type it includes cannot be formed";
          args.push_back(t);
        }
        if (std::optional<std::string> why = unmet(r->text, args, via))
          return *why + " (from 'include " + r->text + "')";
      } else if (r->kind == NodeKind::SigVal) {
        std::vector<std::string> names, mods;
        std::vector<Type> ptypes;
        const Node *cur = r->kids[0]->kids[1].get();
        for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
          const Node &d = *cur->kids[0];
          names.push_back(d.text);
          mods.push_back(d.kids[0]->text);
          Type t = types_.resolve(*d.kids[1]);
          if (!t) return "the type of '" + r->text + "' cannot be formed";
          ptypes.push_back(t);
        }
        Type result = types_.resolve(*cur);
        if (!result) return "the type of '" + r->text + "' cannot be formed";
        std::string spelled = r->text + " : ";
        for (Type t : ptypes) spelled += typeName(t) + " -> ";
        spelled += typeName(result);
        const sema::FuncSig *found = nullptr;
        // An adapter's own functions come first.
        std::vector<sema::FuncSig *> cands;
        if (via)
          if (auto f = via->fns.find(r->text); f != via->fns.end())
            for (const std::string &sym : f->second)
              cands.push_back(&sigs_.at(sym));
        for (sema::FuncSig *cand : overloadSet(r->text))
          cands.push_back(cand);
        for (sema::FuncSig *cand : cands) {
          if (found) break;
          if (cand->isGeneric() || cand->params.size() != ptypes.size() ||
              cand->result != result)
            continue;
          bool same = true;
          for (size_t i = 0; i < ptypes.size(); ++i)
            same = same && cand->params[i].type == ptypes[i] &&
                   cand->params[i].modifiers == mods[i];
          if (same) found = cand;
        }
        if (!found) return "no function '" + spelled + "'";
        if (!r->kids[2]->kids.empty())
          queueContractLemma(*r, key, names, *found, scope, via);
      } else if (r->kind == NodeKind::SigLemma) {
        queueLemma(key + "." + r->text, syntax::clone(*r->kids[0]),
                   syntax::clone(*r->kids[1]),
                   syntax::makeNode(NodeKind::Unit, r->loc), scope, r->loc,
                   via);
      }
    }
    return std::nullopt;
  }

  // A requirement's contract is honoured by the function that meets it
  // when the requirement's precondition implies the function's, and the
  // function's postcondition implies the requirement's. Both are proved by
  // a lemma over the function's parameters: it asserts the function's
  // preconditions under the requirement's, and ensures the requirement's
  // postcondition of a call.
  void queueContractLemma(const Node &req, const std::string &key,
                          const std::vector<std::string> &names,
                          const sema::FuncSig &found,
                          const std::map<std::string, Type> &scope,
                          const AdapterInfo *via) {
    syntax::SourceLoc at = req.loc;
    std::map<std::string, std::string> rename;
    auto params = syntax::makeNode(NodeKind::Params, at);
    auto call = syntax::makeNode(NodeKind::Apply, at);
    call->add(syntax::makeNode(NodeKind::Name, at, req.text));
    const Node *cur = req.kids[0]->kids[1].get();
    for (size_t i = 0; i < names.size(); ++i, cur = cur->kids[1].get()) {
      const std::string &mine = found.params[i].name;
      rename[names[i]] = mine;
      Node *p = params->add(syntax::makeNode(NodeKind::Param, at, mine));
      Node *annot = p->add(syntax::makeNode(NodeKind::Annot, at));
      annot->add(syntax::makeNode(NodeKind::Modifiers, at));
      annot->add(syntax::clone(*cur->kids[0]->kids[1]));
      annot->add(syntax::makeNode(NodeKind::None, at));
      call->add(syntax::makeNode(NodeKind::Name, at, mine));
    }
    auto contracts = syntax::makeNode(NodeKind::Contracts, at);
    for (const syntax::NodePtr &c : req.kids[2]->kids) {
      NodePtr copy = syntax::clone(*c);
      renameNames(*copy, rename, c->kind == NodeKind::Ensures ? call.get()
                                                              : nullptr);
      contracts->add(std::move(copy));
    }
    // The body asserts the function's own preconditions, in its own names.
    NodePtr body = syntax::makeNode(NodeKind::Unit, at);
    const Node &own = *found.item->kids[2];
    for (size_t i = own.kids.size(); i-- > 0;) {
      if (own.kids[i]->kind != NodeKind::Requires) continue;
      auto seq = syntax::makeNode(NodeKind::Sequence, at);
      Node *a = seq->add(syntax::makeNode(NodeKind::Assert, own.kids[i]->loc));
      a->add(syntax::clone(*own.kids[i]->kids[0]));
      seq->add(std::move(body));
      body = std::move(seq);
    }
    queueLemma(key + "." + req.text + ".contract", std::move(params),
               std::move(contracts), std::move(body), scope, at, via);
  }

  // Renames free names in a contract; `result` becomes `call` when given.
  static void renameNames(Node &n, const std::map<std::string, std::string> &to,
                          const Node *call) {
    for (syntax::NodePtr &k : n.kids) {
      if (k->kind == NodeKind::Name && call && k->text == "result") {
        k = syntax::clone(*call);
        continue;
      }
      if (k->kind == NodeKind::Name)
        if (auto it = to.find(k->text); it != to.end()) k->text = it->second;
      renameNames(*k, to, call);
    }
  }

  // Makes a lemma for a concept's arguments and queues it to be generated
  // and proved like any other function.
  void queueLemma(const std::string &symbol, NodePtr params, NodePtr contracts,
                  NodePtr body, const std::map<std::string, Type> &scope,
                  syntax::SourceLoc at, const AdapterInfo *via) {
    if (sigs_.count(symbol)) return;
    auto item = syntax::makeNode(NodeKind::LetItem, at, symbol);
    item->flags = "lemma";
    item->add(std::move(params));
    Node *ret = item->add(syntax::makeNode(NodeKind::RetAnnot, at));
    Node *annot = ret->add(syntax::makeNode(NodeKind::Annot, at));
    annot->add(syntax::makeNode(NodeKind::Modifiers, at));
    annot->add(syntax::makeNode(NodeKind::TypeName, at, "unit"));
    annot->add(syntax::makeNode(NodeKind::None, at));
    ret->add(syntax::makeNode(NodeKind::Attrs, at));
    item->add(std::move(contracts));
    item->add(std::move(body));
    sema::FuncSig sig;
    sig.name = symbol;
    sig.item = item.get();
    sig.typeArgs = scope;
    for (auto &[name, type] : scope) sig.typeParams.push_back(name);
    // A law of a concept met through an adapter is about its functions.
    if (via) sig.adapted = via->fns;
    synthesized_.push_back(std::move(item));
    if (!sema::resolveSignature(sig, types_, diags_)) return;
    sigs_.emplace(symbol, std::move(sig));
    pendingInstances_.push_back(symbol);
  }

  // --- the definition check (ADR 0034) --------------------------------

  // Generates the body of `symbol`, a generic, once with each type
  // parameter standing for an unknown type: a record named after it with
  // no fields. A call with an argument of such a type resolves against the
  // requirements of the concepts its constraints promise, and nothing else
  // it can do with a value of that type than pass it on. The generated
  // function, and every instance it made, is thrown away.
  void checkDefinition(const std::string &symbol) {
    const sema::FuncSig &generic = sigs_.at(symbol);
    std::map<std::string, Type> bound;
    for (const std::string &t : generic.typeParams) {
      Type a = RecordType::get(&ctx_, t, {}, {});
      bound[t] = a;
      archetypes_[a] = {t, {}, {}};
      standIns_.insert(a);
    }
    if (!promiseConstraints(generic, bound)) {
      archetypes_.clear();
      promised_.clear();
      promisedFns_.clear();
      return;
    }
    std::string key = "definition of " + generic.name;
    sema::FuncSig check = generic;
    check.name = key;
    check.typeArgs = bound;
    check.result = Type();
    std::map<std::string, std::optional<std::string>> savedMet = met_;
    size_t pending = pendingInstances_.size();
    std::set<std::string> before;
    for (auto &[k, v] : sigs_) before.insert(k);
    checking_ = true;
    opaqueStandIn_ = false;
    // A signature that applies a type-level metaprogram to a type
    // parameter, as in `: widen t`, has a type that is only known for
    // each instance, so its body is checked in each instance instead
    // (ADR 0035).
    if (sema::resolveSignature(check, types_, diags_) && !opaqueStandIn_) {
      sigs_.emplace(key, std::move(check));
      genFunction(key);
    }
    checking_ = false;
    // Nothing the check made survives it.
    if (auto f = module_.lookupSymbol<mlir::func::FuncOp>(key)) f.erase();
    for (auto it = sigs_.begin(); it != sigs_.end();)
      it = before.count(it->first) ? std::next(it) : sigs_.erase(it);
    pendingInstances_.resize(pending);
    met_ = std::move(savedMet);
    promised_.clear();
    promisedFns_.clear();
    archetypes_.clear();
  }

  // Records what the constraints of `generic` promise when its type
  // parameters are the stand-in types `bound`. False when a type in them
  // cannot be formed.
  bool promiseConstraints(const sema::FuncSig &generic,
                          const std::map<std::string, Type> &bound) {
    for (const syntax::NodePtr &p : generic.item->kids[0]->kids) {
      const Node *pred = wherePredicate(*p);
      if (!pred) continue;
      std::vector<const Node *> cs, preds;
      constraintsOf(*pred, cs, &preds);
      archetypes_[bound.at(p->text)].constraints = cs;
      archetypes_[bound.at(p->text)].predicates = preds;
      for (const Node *c : cs) {
        std::vector<Type> args;
        if (!constraintArgs(*c, bound, args)) return false;
        promise(c->kids[0]->text, args);
      }
    }
    return true;
  }

  // The types a constraint `C t u8` names, with `bound` for the type
  // parameters. False when one cannot be formed.
  bool constraintArgs(const Node &c, const std::map<std::string, Type> &bound,
                      std::vector<Type> &args) {
    for (size_t i = 1; i < c.kids.size(); ++i) {
      auto b = bound.find(c.kids[i]->text);
      Type ty;
      if (b != bound.end()) {
        ty = b->second;
      } else {
        Node asType;
        asType.kind = NodeKind::TypeName;
        asType.text = c.kids[i]->text;
        asType.loc = c.kids[i]->loc;
        ty = types_.resolve(asType);
      }
      if (!ty) return false;
      args.push_back(ty);
    }
    return true;
  }

  // --- ranking generic overloads (ADR 0034, step 5) --------------------

  // Stand-in types for the type parameters of `sig`.
  std::map<std::string, Type> standIns(const sema::FuncSig &sig) {
    std::map<std::string, Type> bound;
    for (const std::string &t : sig.typeParams) {
      bound[t] = RecordType::get(&ctx_, t, {}, {});
      standIns_.insert(bound[t]);
    }
    return bound;
  }

  // Whether the parameter types of the generic `a` are an instance of
  // those of `b`: `[u8]` of `[t]`, `pair t t` of `pair a b`. `mapB` binds
  // b's type parameters to a's stand-ins.
  bool instanceOf(const sema::FuncSig &a, const sema::FuncSig &b,
                  std::map<std::string, Type> &mapB) {
    sema::FuncSig ai = a;
    ai.typeArgs = standIns(a);
    ai.result = Type();
    if (!sema::resolveSignature(ai, types_, diags_)) return false;
    std::vector<const Node *> vb = valueParamsOf(b);
    if (vb.size() != ai.params.size()) return false;
    for (size_t i = 0; i < vb.size(); ++i)
      if (vb[i]->kids.empty() || vb[i]->kids[0]->kind != NodeKind::Annot ||
          !types_.unify(*vb[i]->kids[0], ai.params[i].type, b.typeParams,
                        mapB))
        return false;
    // Deduction only binds b's type parameters; the types must also be
    // the same once they are bound.
    for (const std::string &t : b.typeParams)
      if (!mapB.count(t)) return false;
    sema::FuncSig bi = b;
    bi.typeArgs = mapB;
    bi.result = Type();
    if (!sema::resolveSignature(bi, types_, diags_)) return false;
    for (size_t i = 0; i < bi.params.size(); ++i)
      if (bi.params[i].type != ai.params[i].type) return false;
    return true;
  }

  // Whether the constraints of `a` entail those of `b`, with `mapB`
  // binding b's type parameters to a's stand-ins: each concept b names is
  // promised by a's constraints, through `include`, or else a's promised
  // requirements have every one of its requirements, and it states no law
  // or contract, which would need a proof.
  bool entails(const sema::FuncSig &a, const sema::FuncSig &b,
               const std::map<std::string, Type> &mapB) {
    auto savedArch = std::move(archetypes_);
    auto savedPromised = std::move(promised_);
    auto savedFns = std::move(promisedFns_);
    archetypes_.clear();
    promised_.clear();
    promisedFns_.clear();
    std::map<std::string, Type> boundA = standIns(a);
    for (auto &[t, ty] : boundA) archetypes_[ty] = {t, {}, {}};
    bool ok = promiseConstraints(a, boundA);
    for (const syntax::NodePtr &p : b.item->kids[0]->kids) {
      const Node *pred = wherePredicate(*p);
      if (!pred || !ok) continue;
      std::vector<const Node *> cs, preds;
      constraintsOf(*pred, cs, &preds);
      for (const Node *c : cs) {
        std::vector<Type> args;
        ok = ok && constraintArgs(*c, mapB, args) &&
             entailed(c->kids[0]->text, args, 0);
      }
      // A predicate is entailed when a states it too (ADR 0035).
      for (const Node *q : preds) ok = ok && !predicateUnmet(*q, mapB);
    }
    archetypes_ = std::move(savedArch);
    promised_ = std::move(savedPromised);
    promisedFns_ = std::move(savedFns);
    return ok;
  }

  bool entailed(const std::string &cname, const std::vector<Type> &args,
                int depth) {
    std::string key = cname + "<" + spellTypes(args) + ">";
    if (promised_.count(key)) return true;
    auto c = concepts_.find(cname);
    if (c == concepts_.end() || depth > 16) return false;
    const Node &item = *c->second;
    std::map<std::string, Type> scope;
    size_t i = 0;
    for (const syntax::NodePtr &p : item.kids[0]->kids)
      if (sema::isTypeParam(*p) && i < args.size()) scope[p->text] = args[i++];
    std::vector<std::map<std::string, Type>> saved =
        types_.replaceTypeScopes({scope});
    bool ok = true;
    for (const syntax::NodePtr &r : item.kids[3]->kids) {
      if (!ok) break;
      if (r->kind == NodeKind::SigLemma) {
        ok = false;
      } else if (r->kind == NodeKind::SigInclude) {
        std::vector<Type> inner;
        for (const syntax::NodePtr &a : r->kids)
          if (Type t = types_.resolve(*a)) inner.push_back(t);
        types_.replaceTypeScopes(std::move(saved));
        ok = inner.size() == r->kids.size() &&
             entailed(r->text, inner, depth + 1);
        saved = types_.replaceTypeScopes({scope});
      } else if (r->kind == NodeKind::SigVal) {
        if (!r->kids[2]->kids.empty()) {
          ok = false;
          continue;
        }
        std::vector<Type> ptypes;
        const Node *cur = r->kids[0]->kids[1].get();
        for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get())
          ptypes.push_back(types_.resolve(*cur->kids[0]->kids[1]));
        Type result = types_.resolve(*cur);
        bool found = false;
        for (const sema::FuncSig *f : promisedFns_[r->text]) {
          bool same = f->params.size() == ptypes.size() && f->result == result;
          for (size_t k = 0; same && k < ptypes.size(); ++k)
            same = f->params[k].type == ptypes[k];
          found = found || same;
        }
        ok = found;
      }
    }
    types_.replaceTypeScopes(std::move(saved));
    return ok;
  }

  // 1 when the generic `a` is more specific than `b`, -1 when `b` is, and
  // 0 when neither is: first by parameter patterns, then by constraints.
  int moreSpecific(const sema::FuncSig &a, const sema::FuncSig &b) {
    std::string key = a.name + "|" + b.name;
    if (auto it = specificity_.find(key); it != specificity_.end())
      return it->second;
    std::map<std::string, Type> mapB, mapA;
    bool aInB = instanceOf(a, b, mapB), bInA = instanceOf(b, a, mapA);
    int result = 0;
    if (aInB && !bInA) {
      result = 1;
    } else if (bInA && !aInB) {
      result = -1;
    } else if (aInB && bInA) {
      bool ab = entails(a, b, mapB), ba = entails(b, a, mapA);
      result = ab && !ba ? 1 : ba && !ab ? -1 : 0;
    }
    specificity_[key] = result;
    specificity_[b.name + "|" + a.name] = -result;
    return result;
  }

  // Two generic overloads with the same parameter patterns and constraints
  // that entail each other could never be told apart: an error at the
  // second.
  void checkGenericOverloads() {
    for (auto &[name, symbols] : overloads_) {
      std::vector<const sema::FuncSig *> gs;
      for (const std::string &sym : symbols)
        if (const sema::FuncSig &f = sigs_.at(sym); f.isGeneric())
          gs.push_back(&f);
      std::sort(gs.begin(), gs.end(), [](auto *x, auto *y) {
        return std::make_pair(x->item->loc.line, x->item->loc.column) <
               std::make_pair(y->item->loc.line, y->item->loc.column);
      });
      for (size_t i = 0; i < gs.size(); ++i)
        for (size_t j = 0; j < i; ++j) {
          std::map<std::string, Type> m1, m2;
          if (instanceOf(*gs[i], *gs[j], m1) &&
              instanceOf(*gs[j], *gs[i], m2) && entails(*gs[i], *gs[j], m1) &&
              entails(*gs[j], *gs[i], m2)) {
            diags_.error(gs[i]->item->loc,
                         "'" + name + "' already has a generic overload "
                         "with these parameter types and constraints that "
                         "say the same, at line " +
                             std::to_string(gs[j]->item->loc.line) +
                             ", so no call could choose between them");
            break;
          }
        }
    }
  }

  // --- overloads told apart by preconditions (ADR 0034, step 6) --------

  // The `requires` clauses of `sig`, with its parameters renamed by
  // position, as text: two overloads' clauses compare equal when they say
  // the same of the same arguments.
  std::set<std::string> requiresOf(const sema::FuncSig &sig) {
    std::map<std::string, std::string> rename;
    for (size_t i = 0; i < sig.params.size(); ++i)
      rename[sig.params[i].name] = "#" + std::to_string(i);
    std::set<std::string> out;
    for (const syntax::NodePtr &c : sig.item->kids[2]->kids) {
      if (c->kind != NodeKind::Requires) continue;
      NodePtr copy = syntax::clone(*c->kids[0]);
      renameNames(*copy, rename, nullptr);
      if (copy->kind == NodeKind::Name)
        if (auto it = rename.find(copy->text); it != rename.end())
          copy->text = it->second;
      std::ostringstream os;
      syntax::dump(os, *copy);
      out.insert(os.str());
    }
    return out;
  }

  // Overloads with the same parameter types must be ordered by their
  // preconditions: each one's `requires` clauses include every clause of
  // the next. That is a proof that each precondition implies the next,
  // so the most specific proved at a call is well defined. They must also
  // return the same type.
  void checkPreconditionOverloads() {
    for (auto &[name, symbols] : overloads_) {
      // Grouped in the order the overloads are visited: mlir::Type has no
      // ordering, and pointer order would make the diagnostics' order vary.
      std::vector<std::pair<std::vector<Type>,
                            std::vector<const sema::FuncSig *>>>
          byTypes;
      for (const std::string &sym : symbols) {
        const sema::FuncSig &f = sigs_.at(sym);
        if (f.isGeneric()) continue;
        std::vector<Type> ts;
        for (const sema::Param &p : f.params) ts.push_back(p.type);
        auto it = std::find_if(byTypes.begin(), byTypes.end(),
                               [&](const auto &e) { return e.first == ts; });
        if (it == byTypes.end()) {
          byTypes.emplace_back(ts, std::vector<const sema::FuncSig *>{});
          it = std::prev(byTypes.end());
        }
        it->second.push_back(&f);
      }
      for (auto &[ts, group] : byTypes) {
        if (group.size() < 2) continue;
        std::sort(group.begin(), group.end(), [](auto *x, auto *y) {
          return std::make_pair(x->item->loc.line, x->item->loc.column) <
                 std::make_pair(y->item->loc.line, y->item->loc.column);
        });
        std::vector<std::pair<std::set<std::string>, const sema::FuncSig *>>
            ranked;
        bool ok = true;
        for (const sema::FuncSig *f : group) {
          std::set<std::string> req = requiresOf(*f);
          for (auto &[other, g] : ranked) {
            std::string at = " at line " + std::to_string(g->item->loc.line);
            if (f->result != g->result) {
              diags_.error(f->item->loc,
                           "'" + name + "' has an overload with these "
                           "parameter types" + at + " that returns " +
                           typeName(g->result) + "; overloads told apart by "
                           "their preconditions return the same type");
              ok = false;
            } else if (req == other) {
              diags_.error(f->item->loc,
                           "'" + name + "' already has an overload with "
                           "these parameter types and the same "
                           "preconditions" + at + ", so no call could "
                           "choose between them");
              ok = false;
            } else if (!std::includes(req.begin(), req.end(), other.begin(),
                                      other.end()) &&
                       !std::includes(other.begin(), other.end(),
                                      req.begin(), req.end())) {
              diags_.error(f->item->loc,
                           "the preconditions of this overload of '" + name +
                           "' and the one" + at + " are not ordered: the "
                           "'requires' of one must include each 'requires' "
                           "of the other");
              ok = false;
            }
            if (!ok) break;
          }
          if (!ok) break;
          ranked.emplace_back(std::move(req), f);
        }
        if (!ok) continue;
        // Most specific first: the most clauses.
        std::stable_sort(ranked.begin(), ranked.end(), [](auto &x, auto &y) {
          return x.first.size() > y.first.size();
        });
        std::vector<std::string> order;
        for (auto &[req, f] : ranked) order.push_back(f->name);
        for (const std::string &sym : order) preconditionOrder_[sym] = order;
      }
    }
  }

  // Records that the constraints promise `cname` for `args`, with what it
  // includes, and the requirement functions they promise.
  void promise(const std::string &cname, const std::vector<Type> &args) {
    auto c = concepts_.find(cname);
    if (c == concepts_.end()) return;
    std::string key = cname + "<" + spellTypes(args) + ">";
    if (!promised_.insert(key).second) return;
    const Node &item = *c->second;
    std::map<std::string, Type> scope;
    size_t i = 0;
    for (const syntax::NodePtr &p : item.kids[0]->kids)
      if (sema::isTypeParam(*p) && i < args.size()) scope[p->text] = args[i++];
    std::vector<std::map<std::string, Type>> saved =
        types_.replaceTypeScopes({scope});
    for (const syntax::NodePtr &r : item.kids[3]->kids) {
      if (r->kind == NodeKind::SigInclude) {
        std::vector<Type> inner;
        for (const syntax::NodePtr &a : r->kids)
          if (Type t = types_.resolve(*a)) inner.push_back(t);
        if (inner.size() == r->kids.size()) {
          types_.replaceTypeScopes(std::move(saved));
          promise(r->text, inner);
          saved = types_.replaceTypeScopes({scope});
        }
        continue;
      }
      if (r->kind != NodeKind::SigVal) continue;
      sema::FuncSig sig;
      sig.name = key + "." + r->text;
      sig.item = r.get();
      bool ok = true;
      const Node *cur = r->kids[0]->kids[1].get();
      for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
        const Node &d = *cur->kids[0];
        sema::Param param;
        param.name = d.text.empty() ? "_" : d.text;
        param.modifiers = d.kids[0]->text;
        param.loc = d.loc;
        param.type = types_.resolve(*d.kids[1]);
        ok = ok && param.type;
        sig.params.push_back(std::move(param));
      }
      sig.result = types_.resolve(*cur);
      if (!ok || !sig.result) continue;
      // Two concepts may promise the same function.
      bool dup = false;
      for (const sema::FuncSig *other : promisedFns_[r->text]) {
        bool same = other->params.size() == sig.params.size() &&
                    other->result == sig.result;
        for (size_t k = 0; same && k < sig.params.size(); ++k)
          same = other->params[k].type == sig.params[k].type;
        dup = dup || same;
      }
      if (dup) continue;
      promisedSigs_.push_back(std::move(sig));
      promisedFns_[r->text].push_back(&promisedSigs_.back());
    }
    types_.replaceTypeScopes(std::move(saved));
  }

  // `Ord t`, as written, for each constraint of the type parameter `t`.
  std::string constraintsText(Type archetype) {
    const Archetype &a = archetypes_.at(archetype);
    if (a.constraints.empty()) return "'" + a.name + "', which has no constraints";
    std::string out;
    for (size_t i = 0; i < a.constraints.size(); ++i) {
      const Node &c = *a.constraints[i];
      std::string one = c.kids[0]->text;
      for (size_t k = 1; k < c.kids.size(); ++k) one += " " + c.kids[k]->text;
      out += (i ? " && " : "") + one;
    }
    return "'" + out + "'";
  }

  // Why a generic body cannot call `name` with arguments of the type
  // parameters' types `abstract`, with a concept that would promise it.
  // Empty when no argument has such a type and no concept requires `name`.
  std::string notPromised(const std::string &name,
                          const std::vector<Type> &abstract) {
    std::string suggestion;
    for (auto &[cname, item] : concepts_) {
      for (const syntax::NodePtr &r : item->kids[3]->kids)
        if (r->kind == NodeKind::SigVal && r->text == name) {
          suggestion = cname;
          break;
        }
      if (!suggestion.empty()) break;
    }
    if (abstract.empty() && suggestion.empty()) return "";
    std::string what = abstract.empty()
                           ? std::string("the constraints of this generic")
                           : constraintsText(abstract[0]);
    std::string out = "'" + name + "' is not promised by " + what;
    if (!suggestion.empty()) {
      std::string t = abstract.empty() ? "t" : archetypes_.at(abstract[0]).name;
      out += "; constrain '" + t + "' by a concept that requires it, such "
             "as '" + suggestion + " " + t + "'";
    }
    return out;
  }

  // The instance of a generic function for `bound`, made and queued on
  // first use. Null after an error.
  sema::FuncSig *genericInstance(const sema::FuncSig &generic,
                                 std::map<std::string, Type> bound,
                                 const Choice &choice = {}) {
    const std::vector<std::string> &params = generic.typeParams;
    std::string key = generic.name + "<";
    for (size_t i = 0; i < params.size(); ++i)
      key += (i ? ", " : "") + typeName(bound[params[i]]);
    // An instance made through adapters is its own instance.
    for (auto &[concept_key, adapter] : choice.adapterFor)
      key += ", " + concept_key.substr(0, concept_key.find('<')) + " = " +
             adapter;
    key += ">";
    auto it = sigs_.find(key);
    if (it == sigs_.end()) {
      sema::FuncSig inst = generic;
      inst.name = key;
      inst.typeArgs = bound;
      inst.result = Type();
      inst.adapted = choice.adapted;
      inst.adapterFor = choice.adapterFor;
      if (!sema::resolveSignature(inst, types_, diags_)) return nullptr;
      if (!inst.result && !retAnnotOf(generic)) {
        fail(*generic.item, "a generic function needs its return type for "
                            "now, as in 'let " + generic.name + " ... : T = "
                            "...'");
        return nullptr;
      }
      it = sigs_.emplace(key, std::move(inst)).first;
      pendingInstances_.push_back(key);
    }
    return &it->second;
  }

  // Binds the type arguments `f<u8, t = u16>` gives. False after an error.
  bool bindTypeArgs(const sema::FuncSig &generic, const Node *targs,
                    std::map<std::string, Type> &bound,
                    std::map<std::string, std::string> *named = nullptr) {
    const std::vector<std::string> &params = generic.typeParams;
    if (targs) {
      size_t next = 0;
      for (size_t i = 1; i < targs->kids.size(); ++i) {
        const Node &t = *targs->kids[i];
        std::string name;
        const Node *typeNode = &t;
        if (t.kind == NodeKind::NamedArg) {
          name = t.text;
          typeNode = t.kids[0].get();
          // `f<Eq = bitwise_eq>` names the adapter for a constraint.
          if (named && concepts_.count(name) &&
              typeNode->kind == NodeKind::Name) {
            (*named)[name] = typeNode->text;
            continue;
          }
          if (!llvm::is_contained(params, name)) {
            fail(t, "'" + generic.name + "' has no type parameter '" + name +
                        "'");
            return false;
          }
        } else {
          if (next >= params.size()) {
            fail(t, "'" + generic.name + "' takes " +
                        plural(params.size(), "type argument") +
                        ", given more");
            return false;
          }
          name = params[next++];
        }
        // `t = u8` parses its value as an expression: a bare name is a
        // type name there.
        Node asType;
        if (typeNode->kind == NodeKind::Name) {
          asType.kind = NodeKind::TypeName;
          asType.text = typeNode->text;
          asType.loc = typeNode->loc;
          typeNode = &asType;
        }
        Type ty = types_.resolve(*typeNode);
        if (!ty) return false;
        if (!bound.emplace(name, ty).second) {
          fail(t, "the type parameter '" + name + "' is given twice");
          return false;
        }
      }
    }
    return true;
  }

  // Whether a written type mentions a type parameter that is not bound.
  static bool mentionsUnbound(const Node &type,
                              const std::vector<std::string> &params,
                              const std::map<std::string, Type> &bound) {
    if (type.kind == NodeKind::TypeName && llvm::is_contained(params, type.text))
      return !bound.count(type.text);
    for (const syntax::NodePtr &k : type.kids)
      if (k && mentionsUnbound(*k, params, bound)) return true;
    return false;
  }

  // Why an argument's type does not match its parameter's written type.
  std::string clashMessage(const Node &annot, Type actual,
                           const std::map<std::string, Type> &bound) {
    std::map<std::string, Type> alone;
    std::vector<std::string> names;
    for (auto &[name, t] : bound) names.push_back(name);
    if (types_.unify(annot, actual, names, alone))
      for (auto &[name, t] : alone)
        if (bound.count(name) && bound.at(name) != t)
          return "'" + name + "' is already " + typeName(bound.at(name)) +
                 ", but this makes it " + typeName(t);
    return "it does not match its parameter's type";
  }

  static bool writes(const sema::Param &p) {
    return sema::hasModifier(p.modifiers, "out") ||
           sema::hasModifier(p.modifiers, "inout");
  }

  // Whether a buffer is, or views, read-only constant data.
  static bool isConstantData(Value v) {
    while (auto s = v.getDefiningOp<SliceOp>()) v = s.getBuffer();
    return v.getDefiningOp<ConstArrayOp>() != nullptr;
  }

  R emitCall(const Node &n, const sema::FuncSig &sig,
             llvm::ArrayRef<Value> operands) {
    llvm::SmallVector<Type> results;
    if (!isUnit(sig.result)) results.push_back(sig.result);
    auto call = create<mlir::func::CallOp>(loc(n), sig.name, results,
                                              operands);
    // A call left open between overloads told apart by their
    // preconditions: the verifier chooses (verify::resolveOverloads).
    if (openCandidates_ && sig.name == openFor_) {
      call->setAttr("pia.overload_candidates", openCandidates_);
      openCandidates_ = {};
    }
    if (results.empty()) return unit();
    return TV{call.getResult(0), sig.result};
  }

  // `=` and `<>` on records call `eq_<name>`, which `@derive(eq)` makes.
  R genRecordEq(const Node &n, const std::string &op, TV a,
                const Node &lhsNode, TV c, const Node &rhsNode) {
    if (op != "=" && op != "<>")
      return fail(n, "records cannot be compared with '" + op + "'");
    auto rt = mlir::dyn_cast<RecordType>(a.type);
    if (!rt || a.type != c.type)
      return fail(n, "'" + op + "' compares two values of one record type, "
                     "found " + typeName(a.type) + " and " + typeName(c.type));
    std::string name = rt.getName().str();
    auto it = sigs_.find("eq_" + name);
    // In a contract, `=` without an `eq_` is equality of the values
    // themselves, which every type has: a generic contract that compares
    // values of a type parameter means the same in each instance as at the
    // definition, where it was accepted.
    if (it == sigs_.end() && contract_) {
      Location l = loc(n);
      Value eq = sameValue(l, a.value, c.value, a.type);
      if (!eq)
        return fail(n, "comparing values of type " + name + " with '" + op +
                           "' in a contract is not supported yet: a field's "
                           "type has no equality there");
      if (op == "<>")
        eq = create<mlir::arith::XOrIOp>(l, eq, boolConst(l, true));
      return TV{eq, boolType()};
    }
    if (it == sigs_.end())
      return fail(n, "comparing records of type " + name + " with '" + op +
                         "' needs 'eq_" + name + "'; add @derive(eq) to '" +
                         name + "'");
    const sema::FuncSig &sig = it->second;
    if (sig.params.size() != 2 || sig.params[0].type != a.type ||
        sig.params[1].type != a.type || sig.result != boolType())
      return fail(n, "'eq_" + name + "' must take two " + name +
                         " values and return bool");
    (void)lhsNode;
    (void)rhsNode;
    R eq = emitCall(n, sig, {a.value, c.value});
    if (!eq || op == "=") return eq;
    Location l = loc(n);
    Value v = create<mlir::arith::XOrIOp>(l, eq->value, boolConst(l, true));
    return TV{v, boolType()};
  }

  // `=` on two arrays or slices in a contract: the same length and the
  // same element at every index, as
  // `len a = len b && forall (k in 0..len a). a.[k] = b.[k]`.
  R genBufferEq(const Node &n, const std::string &op, TV a, TV c) {
    syntax::SourceLoc at = n.loc;
    unsigned k = matchCounter_++;
    std::string an = "#eqa" + std::to_string(k), cn = "#eqb" + std::to_string(k),
                kn = "#eqk" + std::to_string(k);
    auto name = [&](const std::string &s) {
      return syntax::makeNode(NodeKind::Name, at, s);
    };
    auto len = [&](const std::string &s) {
      auto app = syntax::makeNode(NodeKind::Apply, at);
      app->add(name("len"));
      app->add(name(s));
      return app;
    };
    auto index = [&](const std::string &s) {
      auto ix = syntax::makeNode(NodeKind::Index, at);
      ix->add(name(s));
      ix->add(name(kn));
      return ix;
    };
    auto range = syntax::makeNode(NodeKind::Range, at);
    range->add(syntax::makeNode(NodeKind::IntLit, at, "0"));
    range->add(len(an));
    auto binder = syntax::makeNode(NodeKind::RangeBinder, at, kn);
    binder->add(std::move(range));
    auto same = syntax::makeNode(NodeKind::Binary, at, "=");
    same->add(index(an));
    same->add(index(cn));
    auto all = syntax::makeNode(NodeKind::Quantifier, at, "forall");
    all->add(std::move(binder));
    all->add(std::move(same));
    syntax::NodePtr pred = std::move(all);
    if (mlir::isa<SliceType>(a.type)) {
      auto lens = syntax::makeNode(NodeKind::Binary, at, "=");
      lens->add(len(an));
      lens->add(len(cn));
      auto both = syntax::makeNode(NodeKind::Binary, at, "&&");
      both->add(std::move(lens));
      both->add(std::move(pred));
      pred = std::move(both);
    }
    const Node &ref = *pred;
    matchTrees_.push_back(std::move(pred));
    pushScope();
    bind(an, a.value, a.type, false);
    bind(cn, c.value, c.type, false);
    R r = genExpr(ref, boolType());
    popScope();
    if (!r || op == "=") return r;
    Location l = loc(n);
    return TV{create<mlir::arith::XOrIOp>(l, r->value, boolConst(l, true)),
              boolType()};
  }

  // Whether `a` and `b`, of type `t`, are the same value: integers and
  // bools compare, records field by field, and variants by tag and then by
  // the payload of the constructor they hold. Null when some part of `t`
  // has no such equality (a buffer).
  Value sameValue(Location l, Value a, Value b, Type t) {
    if (mlir::isa<IntType>(t)) return cmp(l, CmpPredicate::eq, a, b);
    if (isBool(t))
      return create<mlir::arith::CmpIOp>(l, mlir::arith::CmpIPredicate::eq,
                                         a, b);
    auto rt = mlir::dyn_cast<RecordType>(t);
    if (!rt) return Value();
    auto field = [&](Value v, llvm::StringRef name, Type ft) -> Value {
      return create<FieldOp>(l, ft, v, b_.getStringAttr(name));
    };
    if (types_.isVariant(t)) {
      Type tt = rt.getFieldTypes()[*rt.fieldIndex("tag")];
      Value ta = field(a, "tag", tt), tb = field(b, "tag", tt);
      Value all = cmp(l, CmpPredicate::eq, ta, tb);
      for (const sema::Ctor *c : types_.ctorsOf(t)) {
        if (!c->payload) continue;
        Value same = sameValue(l, field(a, c->name, c->payload),
                               field(b, c->name, c->payload), c->payload);
        if (!same) return Value();
        Value k = create<ConstantOp>(
            l, tt,
            b_.getIntegerAttr(b_.getIntegerType(kWidth),
                              llvm::APInt(kWidth, c->tag)));
        Value holds = cmp(l, CmpPredicate::eq, ta, k);
        all = create<mlir::arith::AndIOp>(l, all, implies(l, holds, same));
      }
      return all;
    }
    Value all = boolConst(l, true);
    for (auto [name, ft] : llvm::zip(rt.getFieldNames(), rt.getFieldTypes())) {
      Value same = sameValue(l, field(a, name.getValue(), ft),
                             field(b, name.getValue(), ft), ft);
      if (!same) return Value();
      all = create<mlir::arith::AndIOp>(l, all, same);
    }
    return all;
  }

  Type elementType(Type buffer) {
    if (auto a = mlir::dyn_cast<ArrayType>(buffer)) return a.getElementType();
    if (auto s = mlir::dyn_cast<SliceType>(buffer)) return s.getElementType();
    return {};
  }

  // The index of `xs.[i]`, as an `index` value.
  std::optional<Value> genIndexValue(const Node &index) {
    if (index.kind == NodeKind::Range) {
      fail(index, "a slice 'xs.[a .. b]' is a view to read or pass on; "
                  "write through one inside a function that takes it 'out'");
      return std::nullopt;
    }
    R i = genExpr(index, types_.usize());
    if (!i) return std::nullopt;
    if (!mlir::isa<IntType>(i->type)) {
      fail(index, "an index must be an integer, found " + typeName(i->type));
      return std::nullopt;
    }
    return toIndex(loc(index), i->value);
  }

  R genIndex(const Node &n) {
    R buf = genExpr(*n.kids[0], Type());
    if (!buf) return buf;
    Type elem = elementType(buf->type);
    if (!elem)
      return fail(*n.kids[0], "only arrays and slices can be indexed, found " +
                                  typeName(buf->type));
    if (n.kids[1]->kind == NodeKind::Range) {
      // `xs.[a .. b]`: a view of elements [a, b).
      const Node &range = *n.kids[1];
      auto lo = genIndexValue(*range.kids[0]);
      if (!lo) return std::nullopt;
      auto hi = genIndexValue(*range.kids[1]);
      if (!hi) return std::nullopt;
      Type t = SliceType::get(&ctx_, elem);
      Value v = create<SliceOp>(loc(n), t, buf->value, *lo, *hi);
      return TV{v, t};
    }
    auto idx = genIndexValue(*n.kids[1]);
    if (!idx) return std::nullopt;
    Value v = create<LoadOp>(loc(n), elem, buf->value, *idx);
    return TV{v, elem};
  }

  // `{ r = x; g = 0 }`: the record type comes from the context or, failing
  // that, from the one record whose fields are exactly these.
  R genRecordLit(const Node &n, Type expected) {
    auto rt = mlir::dyn_cast_or_null<RecordType>(expected);
    if (rt && types_.isVariant(rt))
      return fail(n, typeName(rt) + " is a variant; build it with one of its "
                     "constructors");
    if (!rt) {
      std::set<std::string> written;
      for (const syntax::NodePtr &f : n.kids) written.insert(f->text);
      std::vector<RecordType> matches;
      for (const auto &[name, t] : types_.namedTypes()) {
        auto r = mlir::dyn_cast<RecordType>(t);
        if (!r || r.getName() != name || types_.isVariant(r)) continue;
        std::set<std::string> fields;
        for (mlir::StringAttr f : r.getFieldNames()) fields.insert(f.str());
        if (fields == written) matches.push_back(r);
      }
      if (matches.size() != 1)
        return fail(n, matches.empty()
                           ? "no record type has exactly these fields"
                           : "more than one record type has these fields; "
                             "annotate the type, as in 'let p : T = { ... }'");
      rt = matches[0];
    }
    for (const syntax::NodePtr &f : n.kids)
      if (!rt.fieldIndex(f->text))
        return fail(*f, typeName(rt) + " has no field '" + f->text + "'");
    llvm::SmallVector<Value> fields;
    for (auto [name, ft] : llvm::zip(rt.getFieldNames(), rt.getFieldTypes())) {
      const Node *init = nullptr;
      for (const syntax::NodePtr &f : n.kids) {
        if (f->text != name.getValue()) continue;
        if (init)
          return fail(*f, "the field '" + f->text + "' is given twice");
        init = f.get();
      }
      if (!init)
        return fail(n, "the field '" + name.str() + "' of " + typeName(rt) +
                           " is missing");
      R v = genExpr(*init->kids[0], ft);
      if (!v) return v;
      R c = coerce(*v, ft, *init->kids[0]);
      if (!c) return c;
      fields.push_back(c->value);
    }
    return TV{create<RecordOp>(loc(n), rt, fields), rt};
  }

  R genField(const Node &n) {
    R obj = genExpr(*n.kids[0], Type());
    if (!obj) return obj;
    auto rt = mlir::dyn_cast<RecordType>(obj->type);
    if (!rt || types_.isVariant(rt))
      return fail(n, "'." + n.text + "' needs a record, found " +
                         typeName(obj->type) +
                         (rt ? "; use 'match' to read a variant" : ""));
    std::optional<unsigned> i = rt.fieldIndex(n.text);
    if (!i) return fail(n, typeName(rt) + " has no field '" + n.text + "'");
    Type ft = rt.getFieldTypes()[*i];
    Value v = create<FieldOp>(loc(n), ft, obj->value, b_.getStringAttr(n.text));
    return TV{v, ft};
  }

  // `xs.[i].r <- v` reads element i, replaces its field and writes it back.
  // Once records are scalarized, only the field's own buffer is written.
  R genElementFieldAssign(const Node &n) {
    const Node &place = *n.kids[0];
    const Node &index = *place.kids[0];
    const Node &obj = *index.kids[0];
    if (obj.kind != NodeKind::Name)
      return fail(obj, "only a named array or slice can be written");
    BindingPtr b = lookup(obj.text);
    if (!b) return fail(obj, "unknown name '" + obj.text + "'");
    Type elem = elementType(b->type);
    if (!elem)
      return fail(obj, "only arrays and slices can be indexed, found " +
                           typeName(b->type));
    auto rt = mlir::dyn_cast<RecordType>(elem);
    if (!rt || types_.isVariant(rt))
      return fail(place, "'." + place.text + "' needs a record, found " +
                             typeName(elem));
    if (!b->isParam || !(sema::hasModifier(b->modifiers, "out") ||
                         sema::hasModifier(b->modifiers, "inout")))
      return fail(obj, "cannot write to '" + obj.text +
                           "': declare the parameter 'out' or 'inout'");
    std::optional<unsigned> i = rt.fieldIndex(place.text);
    if (!i)
      return fail(place, typeName(rt) + " has no field '" + place.text + "'");
    auto idx = genIndexValue(*index.kids[1]);
    if (!idx) return std::nullopt;
    Type ft = rt.getFieldTypes()[*i];
    R v = genExpr(*n.kids[1], ft);
    if (!v) return v;
    R c = coerce(*v, ft, *n.kids[1]);
    if (!c) return c;
    Location l = loc(n);
    Value old = create<LoadOp>(l, rt, b->value, *idx);
    llvm::SmallVector<Value> fields;
    for (auto [j, name] : llvm::enumerate(rt.getFieldNames()))
      fields.push_back(j == *i ? c->value
                               : create<FieldOp>(l, rt.getFieldTypes()[j], old,
                                                 name)
                                     .getResult());
    create<StoreOp>(l, create<RecordOp>(l, rt, fields).getResult(), b->value,
                    *idx);
    return unit();
  }

  R genAssign(const Node &n) {
    const Node &place = *n.kids[0];
    const Node &valueNode = *n.kids[1];
    if (place.kind == NodeKind::Field) {
      // `p.r <- v` rebuilds the record `p` with one field replaced.
      const Node &obj = *place.kids[0];
      if (obj.kind == NodeKind::Index) return genElementFieldAssign(n);
      if (obj.kind != NodeKind::Name)
        return fail(obj, "only a field of a named record can be assigned");
      BindingPtr b = lookup(obj.text);
      if (!b) return fail(obj, "unknown name '" + obj.text + "'");
      auto rt = mlir::dyn_cast<RecordType>(b->type);
      if (!rt)
        return fail(place, "'." + place.text + "' needs a record, found " +
                               typeName(b->type));
      if (!b->isMutable)
        return fail(obj, "'" + obj.text + "' is not mutable; declare it "
                         "as 'let " + obj.text + " : mutable T = ...'");
      std::optional<unsigned> i = rt.fieldIndex(place.text);
      if (!i)
        return fail(place, typeName(rt) + " has no field '" + place.text + "'");
      Type ft = rt.getFieldTypes()[*i];
      R v = genExpr(valueNode, ft);
      if (!v) return v;
      R c = coerce(*v, ft, valueNode);
      if (!c) return c;
      Location l = loc(n);
      llvm::SmallVector<Value> fields;
      for (auto [j, name] : llvm::enumerate(rt.getFieldNames()))
        fields.push_back(j == *i ? c->value
                                 : create<FieldOp>(l, rt.getFieldTypes()[j],
                                                   b->value, name)
                                       .getResult());
      b->value = create<RecordOp>(l, rt, fields);
      return unit();
    }
    if (place.kind == NodeKind::Name) {
      BindingPtr b = lookup(place.text);
      if (!b) return fail(place, "unknown name '" + place.text + "'");
      if (!b->isMutable)
        return fail(place, "'" + place.text + "' is not mutable; declare it "
                           "as 'let " + place.text + " : mutable T = ...'");
      if (mlir::isa<ArrayType, SliceType>(b->type))
        return fail(place, "assigning a whole array is not supported yet");
      R v = genExpr(valueNode, b->type);
      if (!v) return v;
      R c = coerce(*v, b->type, valueNode);
      if (!c) return c;
      b->value = c->value;
      return unit();
    }
    if (place.kind == NodeKind::Index) {
      const Node &obj = *place.kids[0];
      if (obj.kind != NodeKind::Name)
        return fail(obj, "only a named array or slice can be written");
      BindingPtr b = lookup(obj.text);
      if (!b) return fail(obj, "unknown name '" + obj.text + "'");
      Type elem = elementType(b->type);
      if (!elem)
        return fail(obj, "only arrays and slices can be indexed, found " +
                             typeName(b->type));
      if (!b->isParam || !(sema::hasModifier(b->modifiers, "out") ||
                           sema::hasModifier(b->modifiers, "inout")))
        return fail(obj, "cannot write to '" + obj.text +
                             "': declare the parameter 'out' or 'inout'");
      auto idx = genIndexValue(*place.kids[1]);
      if (!idx) return std::nullopt;
      R v = genExpr(valueNode, elem);
      if (!v) return v;
      R c = coerce(*v, elem, valueNode);
      if (!c) return c;
      create<StoreOp>(loc(n), c->value, b->value, *idx);
      return unit();
    }
    return fail(place, "only a name or an element can be assigned");
  }

  R genIf(const Node &n, Type expected) {
    Location l = loc(n);
    R c = genExpr(*n.kids[0], boolType());
    if (!c) return c;
    if (!isBool(c->type))
      return fail(*n.kids[0], "an 'if' condition must be a bool, found " +
                                  typeName(c->type));
    const Node &thenNode = *n.kids[1];
    const Node *elseNode = n.kids.size() > 2 &&
                                   n.kids[2]->kind != NodeKind::None
                               ? n.kids[2].get()
                               : nullptr;
    std::vector<BindingPtr> vars = carried({&thenNode, elseNode});
    llvm::SmallVector<Value> before = values(vars);

    auto thenBlock = std::make_unique<Block>();
    auto elseBlock = std::make_unique<Block>();
    TV tv, ev = unit();
    llvm::SmallVector<Value> thenVars, elseVars;
    {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(thenBlock.get());
      pushScope();
      R t = genExpr(thenNode, expected);
      popScope();
      if (!t) return t;
      tv = *t;
      thenVars = values(vars);
      setValues(vars, before);
      if (elseNode) {
        b_.setInsertionPointToEnd(elseBlock.get());
        pushScope();
        R e = genExpr(*elseNode, expected ? expected : tv.type);
        popScope();
        if (!e) return e;
        ev = *e;
      }
      elseVars = values(vars);
      setValues(vars, before);
    }

    Type rt;
    if (!elseNode) {
      if (!isUnit(tv.type))
        return fail(thenNode, "an 'if' without 'else' must have type unit, "
                              "found " + typeName(tv.type));
      rt = unitType();
    } else if (tv.type == ev.type) {
      rt = tv.type;
    } else if (mlir::isa<IntType>(tv.type) && mlir::isa<IntType>(ev.type)) {
      rt = join(mlir::cast<IntType>(tv.type), mlir::cast<IntType>(ev.type));
    } else {
      return fail(n, "the branches of 'if' have different types: " +
                         typeName(tv.type) + " and " + typeName(ev.type));
    }

    auto finish = [&](Block *block, TV v, const Node &at,
                      llvm::SmallVector<Value> &vs) -> bool {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(block);
      llvm::SmallVector<Value> yields;
      if (!isUnit(rt)) {
        R cv = coerce(v, rt, at);
        if (!cv) return false;
        yields.push_back(cv->value);
      }
      yields.append(vs.begin(), vs.end());
      create<mlir::scf::YieldOp>(l, yields);
      return true;
    };
    if (!finish(thenBlock.get(), tv, thenNode, thenVars)) return std::nullopt;
    if (!finish(elseBlock.get(), ev, elseNode ? *elseNode : n, elseVars))
      return std::nullopt;

    llvm::SmallVector<Type> types;
    if (!isUnit(rt)) types.push_back(rt);
    for (const BindingPtr &b : vars) types.push_back(b->type);
    auto ifOp = makeIf(l, types, c->value, std::move(thenBlock),
                       std::move(elseBlock));
    size_t first = isUnit(rt) ? 0 : 1;
    setValues(vars, ifOp.getResults().drop_front(first));
    if (isUnit(rt)) return unit();
    return TV{ifOp.getResult(0), rt};
  }

  // The bounds of `lo..hi`, joined to one range type. Two literals count
  // as usize, the type loops and quantifiers most often range over.
  std::optional<std::pair<TV, TV>> genRange(const Node &range) {
    const Node &lo = *range.kids[0], &hi = *range.kids[1];
    Type expected = isLiteral(lo) && isLiteral(hi) ? types_.usize() : Type();
    auto ops = genOperands(lo, hi, expected);
    if (!ops) return std::nullopt;
    auto at = mlir::dyn_cast<IntType>(ops->first.type);
    auto ct = mlir::dyn_cast<IntType>(ops->second.type);
    if (!at || !ct) {
      fail(range, "a range needs integer bounds, found " +
                      typeName(ops->first.type) + " and " +
                      typeName(ops->second.type));
      return std::nullopt;
    }
    IntType j = join(at, ct);
    R a = coerce(ops->first, j, lo);
    R c = coerce(ops->second, j, hi);
    if (!a || !c) return std::nullopt;
    return std::make_pair(*a, *c);
  }

  bool genLoopAnnots(const Node &annots) {
    for (const syntax::NodePtr &a : annots.kids) {
      if (a->kind == NodeKind::Invariant) {
        R p = genPredicate(*a->kids[0]);
        if (!p) return false;
        create<contract::InvariantOp>(loc(*a), p->value);
      } else if (a->kind == NodeKind::Decreases) {
        R m = genContractExpr(*a->kids[0], Type());
        if (!m) return false;
        create<contract::DecreasesOp>(loc(*a), m->value);
      }
    }
    return true;
  }

  R genFor(const Node &n) {
    Location l = loc(n);
    const Node &pattern = *n.kids[0];
    const Node &iterable = *n.kids[1];
    const Node &stepNode = *n.kids[2];
    const Node &annots = *n.kids[3];
    const Node &body = *n.kids[4];
    if (pattern.kind != NodeKind::PVar)
      return fail(pattern, "a for loop binds a single name for now");
    if (iterable.kind != NodeKind::Range)
      return fail(iterable, "a for loop iterates over a range 'lo..hi' for now");
    auto bounds = genRange(iterable);
    if (!bounds) return std::nullopt;
    Type t = bounds->first.type;
    Value lb = toIndex(l, bounds->first.value);
    Value ub = toIndex(l, bounds->second.value);
    Value step;
    if (stepNode.kind != NodeKind::None) {
      R s = genExpr(stepNode, t);
      if (!s) return s;
      if (!mlir::isa<IntType>(s->type))
        return fail(stepNode, "a step must be an integer, found " +
                                  typeName(s->type));
      step = toIndex(loc(stepNode), s->value);
    } else {
      step = create<mlir::arith::ConstantIndexOp>(l, 1);
    }

    std::vector<BindingPtr> vars = carried({&annots, &body});
    auto forOp = create<mlir::scf::ForOp>(l, lb, ub, step, values(vars));
    Block *block = forOp.getBody();
    {
      OpBuilder::InsertionGuard guard(b_);
      // Without iteration arguments the builder adds an empty yield; it is
      // rebuilt below with the loop-carried values.
      if (!block->empty() && block->back().hasTrait<mlir::OpTrait::IsTerminator>())
        block->back().erase();
      b_.setInsertionPointToEnd(block);
      pushScope();
      setValues(vars, forOp.getRegionIterArgs());
      Value i = create<FromIndexOp>(loc(pattern), t, forOp.getInductionVar());
      if (!checkFresh(pattern.text, pattern.loc)) {
        popScope();
        return std::nullopt;
      }
      bind(pattern.text, i, t, false);
      bool ok = genLoopAnnots(annots);
      LoopScope inLoop(frames_);
      R r = ok ? genExpr(body, Type()) : std::nullopt;
      if (r && !mustUse(*r, body)) r = std::nullopt;
      if (r) create<mlir::scf::YieldOp>(l, values(vars));
      popScope();
      if (!r) return r;
    }
    setValues(vars, forOp.getResults());
    return unit();
  }

  R genWhile(const Node &n) {
    Location l = loc(n);
    const Node &cond = *n.kids[0];
    const Node &annots = *n.kids[1];
    const Node &body = *n.kids[2];
    std::vector<BindingPtr> vars = carried({&cond, &annots, &body});
    llvm::SmallVector<Type> types;
    for (const BindingPtr &b : vars) types.push_back(b->type);
    bool ok = true;
    auto whileOp = create<mlir::scf::WhileOp>(
        l, types, values(vars),
        [&](OpBuilder &ob, Location, mlir::ValueRange args) {
          OpBuilder::InsertionGuard guard(b_);
          b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
          pushScope();
          setValues(vars, args);
          R c;
          if (genLoopAnnots(annots)) c = genExpr(cond, boolType());
          if (c && !isBool(c->type)) {
            fail(cond, "a 'while' condition must be a bool, found " +
                           typeName(c->type));
            c = std::nullopt;
          }
          if (c)
            create<mlir::scf::ConditionOp>(l, c->value, values(vars));
          else
            ok = false;
          popScope();
        },
        [&](OpBuilder &ob, Location, mlir::ValueRange args) {
          if (!ok) return;
          OpBuilder::InsertionGuard guard(b_);
          b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
          pushScope();
          setValues(vars, args);
          LoopScope inLoop(frames_);
          R r = genExpr(body, Type());
          if (r && !mustUse(*r, body)) r = std::nullopt;
          if (r)
            create<mlir::scf::YieldOp>(l, values(vars));
          else
            ok = false;
          popScope();
        });
    if (!ok) return std::nullopt;
    setValues(vars, whileOp.getResults());
    return unit();
  }

  // --- `?` and `handle` (ADR 0028) -----------------------------------

  // The scopes a `?` can leave (ADR 0028): the function body, and each
  // `handle` inside it. A deque, so a frame stays put while inner ones come
  // and go.
  struct Frame {
    const Node *handle = nullptr;  // null for the function body
    Type result;                   // the function's result type, if written
    std::string function;
    // The nodes whose value is the scope's value: a `?` there can end the
    // scope, since nothing after it in the scope still needs a value.
    std::set<const Node *> tails;
    unsigned loops = 0;            // loops open inside the scope
    unsigned sites = 0;            // the `?`s that reach the handler
    std::set<const Node *> armsUsed;
    std::set<std::string> binds;   // the names the handled scope binds
    // The `defer`s registered so far in the scope, outermost first: a `?`
    // that leaves the scope runs them, innermost first, before its error
    // reaches the handler or the caller.
    std::vector<const Node *> defers;
  };

  static bool definesResult(const Node &n) {
    if ((n.kind == NodeKind::LetItem && n.text == "result") ||
        (n.kind == NodeKind::Ctor && (n.text == "Ok" || n.text == "Err")))
      return true;
    for (const syntax::NodePtr &k : n.kids)
      if (definesResult(*k)) return true;
    return false;
  }
  //
  // A `?` ends its scope early, so it must sit where the rest of the scope
  // is all that follows it: in a tail of the scope, unconditionally
  // evaluated. There it becomes an `if` on the result's tag: `Ok` goes on
  // with the rest of the scope, holding the payload where the `?` was, and
  // `Err` becomes the scope's value, either `Err e` returned to the caller
  // or the handler's arms for that error, generated at this `?`. So each
  // arm is checked and proved once per `?` that can reach it, knowing only
  // what holds there.

  // Counts the loops open in the innermost scope, whose bodies a `?` cannot
  // leave without a handler of their own.
  struct LoopScope {
    std::deque<Frame> &frames;
    explicit LoopScope(std::deque<Frame> &f) : frames(f) {
      if (!frames.empty()) ++frames.back().loops;
    }
    ~LoopScope() {
      if (!frames.empty()) --frames.back().loops;
    }
  };

  // Marks `n` and the nodes whose value is its value as tails of the
  // innermost scope.
  void addTails(const Node &n) {
    frames_.back().tails.insert(&n);
    switch (n.kind) {
      case NodeKind::LetIn:
        addTails(*n.kids[4]);
        break;
      case NodeKind::Sequence:
        addTails(*n.kids[1]);
        break;
      case NodeKind::If:
        addTails(*n.kids[1]);
        if (n.kids.size() > 2 && n.kids[2]->kind != NodeKind::None)
          addTails(*n.kids[2]);
        break;
      case NodeKind::Match:
        for (size_t i = 1; i < n.kids.size(); ++i) addTails(*n.kids[i]->kids[1]);
        break;
      default:
        break;
    }
  }

  // The first `?` that `n` always evaluates before its tails, in
  // evaluation order, or null.
  static const Node *hoistable(const Node &n) {
    switch (n.kind) {
      case NodeKind::Try:
        if (const Node *inner = hoistable(*n.kids[0])) return inner;
        return &n;
      case NodeKind::LetIn:
        return n.kids[0]->kids.empty() ? hoistable(*n.kids[3]) : nullptr;
      case NodeKind::Sequence:
      case NodeKind::If:
      case NodeKind::Match:
        return hoistable(*n.kids[0]);
      case NodeKind::For:
        if (const Node *t = hoistable(*n.kids[1])) return t;
        return hoistable(*n.kids[2]);
      case NodeKind::Binary:
        if (n.text == "&&" || n.text == "||" || n.text == "==>")
          return hoistable(*n.kids[0]);
        break;
      case NodeKind::While:
      case NodeKind::Handle:
      case NodeKind::Lambda:
      case NodeKind::Quantifier:
      case NodeKind::Assert:
      case NodeKind::Assume:
        return nullptr;
      default:
        break;
    }
    for (const syntax::NodePtr &k : n.kids)
      if (const Node *t = hoistable(*k)) return t;
    return nullptr;
  }

  static bool hasTry(const Node &n) {
    if (n.kind == NodeKind::Try) return true;
    for (const syntax::NodePtr &k : n.kids)
      if (hasTry(*k)) return true;
    return false;
  }

  // A copy of `n` with `target` replaced by `replacement`.
  static syntax::NodePtr cloneWith(const Node &n, const Node *target,
                                   syntax::NodePtr &replacement) {
    if (&n == target) return std::move(replacement);
    auto c = std::make_unique<Node>();
    c->kind = n.kind;
    c->text = n.text;
    c->flags = n.flags;
    c->loc = n.loc;
    for (const syntax::NodePtr &k : n.kids)
      c->kids.push_back(cloneWith(*k, target, replacement));
    for (const syntax::NodePtr &k : n.comments)
      c->comments.push_back(syntax::clone(*k));
    return c;
  }

  static const Node &corePattern(const Node &p) {
    return p.kind == NodeKind::PAs ? *p.kids[0] : p;
  }

  bool isResultType(Type t) const {
    const sema::Instance *i = t ? types_.instanceOf(t) : nullptr;
    return i && i->generic == "result" && i->args.size() == 2;
  }

  // A result may not be dropped unexamined (ADR 0028).
  bool mustUse(const TV &v, const Node &at) {
    if (!isResultType(v.type)) return true;
    fail(at, "this result is never used; pass its error on with '?', or "
             "'match' it");
    return false;
  }

  std::string tryMisplaced() const {
    if (!frames_.empty() && frames_.back().loops)
      return "a '?' in a loop body needs a 'handle' on that body for now, "
             "as in 'do step i? handle | e -> () done': its error cannot "
             "leave the loop yet";
    return "this '?' cannot end its scope from here: the scope still needs "
           "a value from the branch, arm or expression it is in; bind it "
           "with 'let' first, or give that part its own 'handle'";
  }

  static std::string where(const Node &n) {
    return std::to_string(n.loc.line) + ":" + std::to_string(n.loc.column);
  }

  // The names that `n` binds: what a handler's arms may not use unless it
  // is bound where the error is raised.
  void collectBinds(const Node &n, std::set<std::string> &out) const {
    if ((n.kind == NodeKind::LetIn || n.kind == NodeKind::PAs ||
         (n.kind == NodeKind::PVar && !types_.isCtorName(n.text))) &&
        n.text != "_")
      out.insert(n.text);
    for (const syntax::NodePtr &k : n.kids) collectBinds(*k, out);
  }

  // A name in `n` that the handled scope binds but that is not bound here,
  // where the error is raised. `own` holds the names the arm binds itself.
  const Node *unboundHere(const Node &n, const Frame &f,
                          const std::set<std::string> &own) {
    if (n.kind == NodeKind::Name && f.binds.count(n.text) &&
        !own.count(n.text) && !lookup(n.text))
      return &n;
    for (const syntax::NodePtr &k : n.kids)
      if (const Node *u = unboundHere(*k, f, own)) return u;
    return nullptr;
  }

  // The arms of `f`'s handler that take the errors of the `?` at `t`, in
  // order, ending at the first catch-all.
  std::optional<std::vector<const Node *>> armsFor(const Node &t, Type err,
                                                   Frame &f) {
    const Node &h = *f.handle;
    std::vector<const sema::Ctor *> ctors = types_.ctorsOf(err);
    std::vector<const Node *> take;
    std::set<std::string> covered;
    bool all = false;
    for (size_t i = 1; i < h.kids.size() && covered.size() < ctors.size();
         ++i) {
      const Node &arm = *h.kids[i];
      const Node &pat = corePattern(*arm.kids[0]);
      if (pat.kind == NodeKind::PVar && !types_.isCtorName(pat.text)) {
        take.push_back(&arm);
        all = true;
        break;
      }
      if ((pat.kind == NodeKind::PVar || pat.kind == NodeKind::PCtor) &&
          types_.ctorIn(pat.text, err)) {
        take.push_back(&arm);
        covered.insert(pat.text);
      }
    }
    if (!all && covered.size() < ctors.size()) {
      std::string missing;
      for (const sema::Ctor *c : ctors)
        if (!covered.count(c->name))
          missing += (missing.empty() ? "" : ", ") + c->name;
      fail(t, "this '?' can raise " + missing + ", which no arm of the "
              "handler at " + where(h) + " takes; add an arm for each, or "
              "a catch-all '| e -> ...'");
      return std::nullopt;
    }
    for (const Node *arm : take) {
      std::set<std::string> own;
      collectBinds(*arm, own);
      if (const Node *late = unboundHere(*arm->kids[1], f, own)) {
        fail(*late, "this arm is reached from the '?' at " + where(t) +
                        ", where '" + late->text + "' is not bound yet; an "
                        "arm may use only what is bound at every '?' that "
                        "reaches it (ADR 0028)");
        return std::nullopt;
      }
      f.armsUsed.insert(arm);
    }
    return take;
  }

  // `n`, a tail of the innermost scope, with `t` the first `?` it
  // evaluates.
  R genTry(const Node &n, const Node &t, Type expected) {
    R r = genExpr(*t.kids[0], Type());
    if (!r) return r;
    if (!isResultType(r->type))
      return fail(t, "'?' passes on the error of a result, but this is " +
                         typeName(r->type));
    const sema::Instance *inst = types_.instanceOf(r->type);
    Type ok = inst->args[0], err = inst->args[1];
    if (!types_.isVariant(err))
      return fail(t, "'?' needs an error type that is a variant, so a "
                     "handler can match it; this result's errors are " +
                         typeName(err));
    Frame &f = frames_.back();
    ++f.sites;
    std::string hidden = "#try" + std::to_string(tryCounter_++);
    syntax::SourceLoc at = t.loc;
    auto name = [&](const std::string &text, const char *flags) {
      auto x = syntax::makeNode(NodeKind::Name, at, text);
      x->flags = flags;
      return x;
    };
    auto builtin = [&](const char *which, const char *ctor) {
      auto a = syntax::makeNode(NodeKind::Apply, at);
      a->add(name(which, "prelude"));
      a->add(name(hidden, ""));
      a->add(name(ctor, ""));
      return a;
    };

    syntax::NodePtr onErr;
    if (!f.handle) {
      Type fr = f.result;
      if (!fr)
        return fail(t, "'?' passes the error on to the caller, so '" +
                           f.function + "' needs its return type written, "
                           "as in ': result u8 " + typeName(err) + "'");
      if (!isResultType(fr))
        return fail(t, "'?' passes the error on to the caller, but '" +
                           f.function + "' returns " + typeName(fr) +
                           "; return a result, or give the scope a 'handle'");
      Type ferr = types_.instanceOf(fr)->args[1];
      if (ferr != err && !inErrorSet(err, ferr))
        return fail(t, "this '?' passes on errors of type " +
                           typeName(err) + ", but '" + f.function +
                           "' returns errors of type " + typeName(ferr) +
                           "; add them to its error set, as in '" +
                           typeName(ferr) + " | " + typeName(err) +
                           "', or give the scope a 'handle' that converts "
                           "them");
      onErr = syntax::makeNode(NodeKind::Apply, at);
      onErr->add(name("Err", ""));
      onErr->add(builtin("#payload", "Err"));
    } else {
      auto arms = armsFor(t, err, f);
      if (!arms) return std::nullopt;
      onErr = syntax::makeNode(NodeKind::Match, at);
      onErr->add(builtin("#payload", "Err"));
      for (const Node *arm : *arms) onErr->add(syntax::clone(*arm));
    }

    // Cleanup runs first, innermost first, on the way out (ADR 0028). The
    // error is the `?`'s own immutable payload, read after the cleanup, so
    // no cleanup can change or replace it.
    for (const Node *d : f.defers) {
      auto seq = syntax::makeNode(NodeKind::Sequence, at);
      seq->add(syntax::clone(*d));
      seq->add(std::move(onErr));
      onErr = std::move(seq);
    }

    syntax::NodePtr okValue = isUnit(ok)
                                  ? syntax::makeNode(NodeKind::Unit, at)
                                  : builtin("#payload", "Ok");
    auto ifNode = syntax::makeNode(NodeKind::If, at);
    ifNode->add(builtin("#is", "Ok"));
    ifNode->add(cloneWith(n, &t, okValue));
    ifNode->add(std::move(onErr));
    const Node &chain = *ifNode;
    matchTrees_.push_back(std::move(ifNode));  // diagnostics may point into it
    // What follows the `?` is still a tail: it may raise again.
    addTails(*chain.kids[1]);
    pushScope();
    bind(hidden, r->value, r->type, false);
    R out = genExpr(chain, expected);
    popScope();
    return out;
  }

  // `defer d; rest`: `d` runs at every exit from `rest` (ADR 0028). Each
  // normal exit, the nodes whose value is `rest`'s value, gets a copy of
  // `d` after it, and each `?` that leaves the scope runs it before its
  // error goes on, so every exit's cleanup is ordinary code there, which
  // the verifier walks like the rest.
  R genDefer(const Node &n, Type expected) {
    const Node &d = *n.kids[0]->kids[0];
    if (const Node *t = firstTry(d))
      return fail(*t, "cleanup cannot fail, so a 'defer' cannot pass an "
                      "error on with '?'; 'match' the result there");
    syntax::NodePtr rest = withCleanup(*n.kids[1], d);
    const Node &r = *rest;
    matchTrees_.push_back(std::move(rest));  // diagnostics may point into it
    if (frames_.empty()) return genExpr(r, expected);
    if (frames_.back().tails.count(&n)) addTails(r);
    frames_.back().defers.push_back(&d);
    R out = genExpr(r, expected);
    frames_.back().defers.pop_back();
    return out;
  }

  static const Node *firstTry(const Node &n) {
    if (n.kind == NodeKind::Try) return &n;
    for (const syntax::NodePtr &k : n.kids)
      if (const Node *t = firstTry(*k)) return t;
    return nullptr;
  }

  // A copy of `n` with `d` run after each node whose value is `n`'s value.
  // An inner `defer`'s cleanup goes inside an outer one's, so they run in
  // reverse order of registration.
  static syntax::NodePtr withCleanup(const Node &n, const Node &d) {
    auto copy = [&](std::initializer_list<size_t> exits) {
      auto c = std::make_unique<Node>();
      c->kind = n.kind;
      c->text = n.text;
      c->flags = n.flags;
      c->loc = n.loc;
      for (size_t i = 0; i < n.kids.size(); ++i) {
        bool exit = false;
        for (size_t e : exits) exit |= e == i;
        c->kids.push_back(exit ? withCleanup(*n.kids[i], d)
                               : syntax::clone(*n.kids[i]));
      }
      for (const syntax::NodePtr &k : n.comments)
        c->comments.push_back(syntax::clone(*k));
      return c;
    };
    switch (n.kind) {
      case NodeKind::LetIn:
        return copy({4});
      case NodeKind::Sequence:
      case NodeKind::Arm:
        return copy({1});
      case NodeKind::Cleanup:
        return copy({0});
      case NodeKind::If:
        if (n.kids.size() > 2 && n.kids[2]->kind != NodeKind::None)
          return copy({1, 2});
        break;
      case NodeKind::Match: {
        auto c = copy({});
        for (size_t i = 1; i < n.kids.size(); ++i)
          c->kids[i] = withCleanup(*n.kids[i], d);
        return c;
      }
      default:
        break;
    }
    auto c = syntax::makeNode(NodeKind::Cleanup, n.loc);
    c->add(syntax::clone(n));
    c->add(syntax::clone(d));
    return c;
  }

  // An exit from a `defer`'s scope: its value, then the cleanup.
  R genCleanup(const Node &n, Type expected) {
    R v = genExpr(*n.kids[0], expected);
    if (!v) return v;
    for (size_t i = 1; i < n.kids.size(); ++i) {
      R c = genExpr(*n.kids[i], Type());
      if (!c) return c;
      if (!isUnit(c->type))
        return fail(*n.kids[i],
                    "a 'defer' runs only for its effect, so its expression "
                    "must have type unit, but this has type " +
                        typeName(c->type));
    }
    return v;
  }

  // `body handle | p -> e ...`: the body with its `?`s handled here.
  R genHandle(const Node &n, Type expected) {
    if (frames_.empty())
      return fail(n, "'handle' is only supported in a function body for now");
    for (size_t i = 1; i < n.kids.size(); ++i)
      if (hasTry(*n.kids[i]->kids[1]))
        return fail(*n.kids[i]->kids[1],
                    "a '?' inside a handler arm is not supported yet; "
                    "'match' the result there instead");
    Frame f;
    f.handle = &n;
    f.result = frames_.back().result;
    f.function = frames_.back().function;
    collectBinds(*n.kids[0], f.binds);
    frames_.push_back(std::move(f));
    addTails(*n.kids[0]);
    R r = genExpr(*n.kids[0], expected);
    Frame done = std::move(frames_.back());
    frames_.pop_back();
    if (!r) return r;
    if (!done.sites)
      return fail(n, "nothing in this scope passes an error on with '?', so "
                     "its handler is never used");
    for (size_t i = 1; i < n.kids.size(); ++i) {
      const Node &arm = *n.kids[i];
      if (done.armsUsed.count(&arm)) continue;
      const Node &pat = corePattern(*arm.kids[0]);
      if (pat.kind == NodeKind::PVar && !types_.isCtorName(pat.text))
        return fail(pat, "this arm is never reached: earlier arms take every "
                         "error the '?'s in its scope can raise");
      return fail(pat, "this arm is never reached: no '?' in its scope can "
                       "raise '" + pat.text + "' before an earlier arm "
                       "takes it");
    }
    return r;
  }

  R genLetIn(const Node &n, Type expected) {
    const Node &params = *n.kids[0];
    const Node &ret = *n.kids[1];
    const Node &contracts = *n.kids[2];
    if (!params.kids.empty())
      return fail(n, "local functions are not supported yet; define '" +
                         n.text + "' at the top level");
    if (!contracts.kids.empty())
      return fail(*contracts.kids[0],
                  "contracts on a local 'let' are not supported yet");
    Type declared;
    std::string modifiers;
    if (ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
        ret.kids[0]->kind == NodeKind::Annot) {
      modifiers = ret.kids[0]->kids[0]->text;
      declared = types_.resolveAnnot(*ret.kids[0]);
      if (!declared) return std::nullopt;
      if (!contract_ && !ghost_)
        if (sema::specOnlyPart(declared))
          return fail(*ret.kids[0], "'" + n.text + "' has " +
                                        specOnlyMessage(declared));
      if (ret.kids.size() > 1 && !ret.kids[1]->kids.empty())
        return fail(*ret.kids[1]->kids[0],
                    "attributes on a local 'let' are not supported yet");
    }
    const Node &valueNode = *n.kids[3];
    R v = genExpr(valueNode, declared);
    if (!v) return v;
    if (declared) {
      v = coerce(*v, declared, valueNode);
      if (!v) return v;
    }
    if (isUnit(v->type))
      return fail(valueNode, "'" + n.text + "' would have type unit");
    if (!checkFresh(n.text, n.loc)) return std::nullopt;
    pushScope();
    bind(n.text, v->value, v->type, sema::hasModifier(modifiers, "mutable"));
    R body = genExpr(*n.kids[4], expected);
    popScope();
    return body;
  }

  // One quantifier op per bound name, nested, so a later range can mention
  // an earlier name: `forall (i in 0..n) (j in 0..i). p`.
  R genQuantifier(const Node &n, size_t index) {
    const Node &binder = *n.kids[index];
    bool innermost = index + 2 == n.kids.size();
    bool isForall = n.text == "forall";
    Location l = loc(binder);

    Type t;
    std::optional<std::pair<TV, TV>> bounds;
    if (binder.kind == NodeKind::RangeBinder) {
      bounds = genRange(*binder.kids[0]);
      if (!bounds) return std::nullopt;
      t = bounds->first.type;
    } else if (binder.kind == NodeKind::Binder && !binder.kids.empty() &&
               binder.kids[0]->kind != NodeKind::None) {
      t = types_.resolve(*binder.kids[0]);
      if (!t) return std::nullopt;
    } else {
      return fail(binder, "'" + binder.text +
                              "' needs a type or a range, as in (" +
                              binder.text + " in 0..n)");
    }

    mlir::Operation *q =
        isForall
            ? create<contract::ForallOp>(l, b_.getI1Type()).getOperation()
            : create<contract::ExistsOp>(l, b_.getI1Type()).getOperation();
    OpBuilder::InsertionGuard guard(b_);
    Block *block = b_.createBlock(&q->getRegion(0), {}, {t}, {l});
    if (!checkFresh(binder.text, binder.loc)) return std::nullopt;
    pushScope();
    Value x = block->getArgument(0);
    bind(binder.text, x, t, false);
    R inner = innermost ? genPredicate(*n.kids.back())
                        : genQuantifier(n, index + 1);
    popScope();
    if (!inner) return inner;
    Value body = inner->value;
    if (bounds) {
      Value inRange = create<mlir::arith::AndIOp>(
          l, cmp(l, CmpPredicate::le, bounds->first.value, x),
          cmp(l, CmpPredicate::lt, x, bounds->second.value));
      body = isForall ? implies(l, inRange, body)
                      : create<mlir::arith::AndIOp>(l, inRange, body)
                            .getResult();
    }
    create<contract::YieldOp>(l, body);
    return TV{q->getResult(0), boolType()};
  }

  Options options_;
  mlir::MLIRContext &ctx_;
  OpBuilder b_;
  mlir::StringAttr file_;
  syntax::Diagnostics &diags_;
  sema::TypeResolver types_;
  mlir::ModuleOp module_;
  std::map<std::string, sema::FuncSig> sigs_;
  std::map<std::string, Constant> consts_;
  unsigned matchCounter_ = 0;
  std::vector<syntax::NodePtr> matchTrees_;
  std::deque<Frame> frames_;
  unsigned tryCounter_ = 0;
  // The prelude's types (`result`), when the program does not define them.
  syntax::NodePtr prelude_;
  std::vector<std::map<std::string, BindingPtr>> scopes_;
  bool contract_ = false;
  OverflowMode overflow_ = OverflowMode::proof;
  unsigned fuel_ = 0;  // @fuel(n) on the function being generated
  bool ghost_ = false;  // generating a spec function or a lemma
  std::deque<std::string> pendingInstances_;  // generic instances to generate
  // Concepts by name, and whether each (concept, arguments) is met: the
  // reason when it is not (ADR 0034).
  std::map<std::string, const Node *> concepts_;
  std::map<std::string, std::optional<std::string>> met_;
  // Lemmas made for concepts' laws and requirement contracts.
  std::deque<syntax::NodePtr> synthesized_;
  // Those of the function being generated.
  std::map<std::string, std::vector<std::string>> adapted_;
  std::map<std::string, std::string> adapterFor_;
  // While a generic's definition is checked: its type parameters' stand-in
  // types, the concepts its constraints promise, and their requirements.
  struct Archetype {
    std::string name;
    std::vector<const Node *> constraints;
    std::vector<const Node *> predicates;  // the `where` that are not concepts
  };
  bool checking_ = false;
  // Overloads with the same parameter types, most specific precondition
  // first, by each one's symbol; and the call being made open between them.
  std::map<std::string, std::vector<std::string>> preconditionOrder_;
  mlir::ArrayAttr openCandidates_;
  std::string openFor_;
  std::map<std::string, int> specificity_;  // "a|b": moreSpecific(a, b)
  llvm::DenseMap<Type, Archetype> archetypes_;
  std::set<std::string> promised_;
  std::map<std::string, std::vector<sema::FuncSig *>> promisedFns_;
  std::deque<sema::FuncSig> promisedSigs_;
  // Each written function name and the symbols it may call (ADR 0034).
  std::map<std::string, std::vector<std::string>> overloads_;
  // Type-level metaprograms (ADR 0035): those that return a type, and
  // those that return a bool, by name; the interpreter that runs them; and
  // each type a metaprogram has seen, by its spelling.
  std::map<std::string, const Node *> typeFns_;
  std::map<std::string, const Node *> typePredicates_;
  meta::Interpreter interp_;
  std::map<std::string, Type> typeValues_;
  // Stand-in types, which stand for every type: a generic's type
  // parameters while its definition is checked or it is ranked, and what
  // a type-level metaprogram makes of them.
  llvm::DenseSet<Type> standIns_;
  // Why a type-level metaprogram may not terminate, by name.
  std::map<std::string, std::string> notTotal_;
  std::set<std::string> reportedNotTotal_;
  // While a candidate's signature is substituted (ADR 0035), a type that
  // cannot be formed is recorded here as its reason, not reported.
  std::optional<std::string> *softFailure_ = nullptr;
  // Set when a type-level metaprogram is applied to a stand-in while a
  // definition is checked.
  bool opaqueStandIn_ = false;
};

}  // namespace

mlir::OwningOpRef<mlir::ModuleOp> generate(const syntax::Node &program,
                                           std::string_view filename,
                                           mlir::MLIRContext &ctx,
                                           syntax::Diagnostics &diags,
                                           const Options &options) {
  loadDialects(ctx);
  return Gen(ctx, filename, diags, options).run(program);
}

}  // namespace pia::irgen
