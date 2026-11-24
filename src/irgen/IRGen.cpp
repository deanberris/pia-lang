#include "irgen/IRGen.h"
#include "irgen/Boxes.h"
#include "irgen/Memory.h"
#include "irgen/Regions.h"
#include "irgen/Target.h"
#include "irgen/Theories.h"
#include "verify/Strategy.h"
#include "verify/Triggers.h"

#include <algorithm>
#include <cstdlib>
#include <cstring>
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
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/Path.h"
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
  // A parameter's value on entry, which `old` reads: a mutable scalar or
  // record parameter is threaded as SSA values, so its current value is
  // the one after the body's assignments.
  Value entry;
  unsigned loopDepth = 0;  // the loops open where it was bound
  // The locals and parameters its value is borrowed from (#70): it holds
  // the result of a call whose result type is `borrowed(m) ...`, or a part
  // of one.
  std::vector<std::shared_ptr<Binding>> lenders;
  // A buffer borrowed with a result type that lets it be written,
  // `borrowed(m) out mutable [u8]`.
  bool writable = false;
  // A `with_arena`'s arena, which lends its own memory (#70).
  bool arena = false;
  // A lambda's closure, which borrows what it captures (ADR 0044).
  bool closure = false;
  // Its referenced captures: each field, and the variable that sees the
  // field's value after each call.
  std::vector<std::pair<std::string, std::shared_ptr<Binding>>> refs;
  // A region (ADR 0042, step 2): what a parameter whose type mentions it
  // borrows from, outside the function.
  bool region = false;
  // For a region with no name, the parameter whose type holds it, as `v`
  // in `(v : borrowed vec u8)`.
  std::string regionOf;
  // A local's scope, the body of its `let`: a loan it holds ends at its
  // last use there (ADR 0042).
  const syntax::Node *scope = nullptr;
  // A `let spec` local or a spec parameter (ADR 0058): code may write it,
  // and only contracts, invariants, asserts and lemma calls may read it.
  bool spec = false;
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
    if (syntax::isDigitSeparator(c))
      continue;
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

  void setTheoryInfo(TheoryInfo info) { theoryInfo_ = std::move(info); }

  // Whether `sig` is a constant of the built-in theory `Target`, such as
  // `Target.page_size`, which code may use as a value (ADR 0049). Proofs
  // see only the axioms about it, outside `@target`.
  bool isTargetValue(const sema::FuncSig &sig) const {
    return sig.item && sig.params.empty() &&
           llvm::StringRef(sig.name).starts_with("Target.") &&
           hasFlag(*sig.item, "abstract") &&
           theoryInfo_.modelled.count("Target");
  }
  void setRegionInfo(RegionInfo info) { regionInfo_ = std::move(info); }
  // Whether the file is marked `@trusted` (ADR 0023): only then may it use
  // `assume`.
  void setTrusted(bool trusted) { trusted_ = trusted; }

  mlir::OwningOpRef<mlir::ModuleOp> run(const Node &program) {
    mlir::OwningOpRef<mlir::ModuleOp> module =
        mlir::ModuleOp::create(mlir::FileLineColLoc::get(file_, 1, 1));
    module_ = *module;
    collectTypeFunctions(program);
    // `result t e` comes with the language (ADR 0028), unless the program
    // brings its own `result`, `Ok` or `Err`.
    // So does `arena`, the type of a `with_arena`'s region (#70), for a
    // program that makes one.
    usesArenas_ = mentions(program, "with_arena");
    std::string prelude;
    if (!definesResult(program))
      prelude += "let result = let (t : type) (e : type) => type | Ok of t | "
                 "Err of e\n";
    if (usesArenas_ && !definesItem(program, "arena"))
      prelude += "let arena = type { mem : [u8]; used : usize }\n";
    if (!prelude.empty()) {
      syntax::Diagnostics ignored;
      prelude_ = syntax::parseProgram(prelude, ignored);
      if (prelude_) sema::defineTypeItems(*prelude_, types_, diags_);
    }
    sigs_ = sema::collectSignatures(program, types_, diags_);
    if (diags_.hasErrors()) return nullptr;
    collectLinear(program);
    collectConstants();
    if (diags_.hasErrors()) return nullptr;
    // Higher-order functions are called only through specialisations.
    for (auto it = sigs_.begin(); it != sigs_.end();) {
      if (!it->second.isHigherOrder()) {
        ++it;
        continue;
      }
      if (!it->second.adapter.empty())
        diags_.error(it->second.item->loc,
                     "'" + it->second.source() + "' takes a function, and "
                     "an adapter's function cannot yet (ADR 0044)");
      hofs_[it->second.source()].push_back(std::move(it->second));
      it = sigs_.erase(it);
    }
    if (diags_.hasErrors()) return nullptr;
    std::map<const Node *, std::string> symbolOf;
    for (auto &[symbol, sig] : sigs_) {
      symbolOf[sig.item] = symbol;
      if (sig.adapter.empty()) overloads_[sig.source()].push_back(symbol);
    }
    // `Function`, the concept of function values (ADR 0044, section 4),
    // comes with the language, unless the program brings its own.
    if (mentions(program, "Function") && !definesItem(program, "Function")) {
      syntax::Diagnostics ignored;
      functionConcept_ = syntax::parseProgram(
          "let meta Function (f : type) (a : type) (r : type) : concept = sig\n"
          "  let apply : (g : f) -> (x : a) -> r\n"
          "end\n",
          ignored);
    }
    collectConcepts(program);
    if (diags_.hasErrors()) return nullptr;
    for (const syntax::NodePtr &item : program.kids)
      if ((item->kind == NodeKind::LetItem && item->kids.size() > 3 &&
           item->kids[3]->kind == NodeKind::TypeValue) ||
          sema::isGenericTypeItem(*item))
        typeItems_.emplace_back(item->text, item.get());
    checkModule(program);
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
    // Each higher-order function is proved once too, with its function
    // parameters abstract (ADR 0044, step 6). Callees first, so that the
    // specialisation of one another calls, made at the caller's stand-in,
    // is discharged by the callee's proof rather than proved again. Not by
    // position: the functions of an imported module all sit at its import.
    for (sema::FuncSig *h : hofsCalleesFirst()) proveOnce(*h);
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
      if (llvm::StringRef(key).starts_with(kDefinition))
        checkDefinition(key.substr(std::strlen(kDefinition)));
      else
        genFunction(key);
    }
    if (diags_.hasErrors()) return nullptr;
    checkGhosts();
    checkAxioms();
    checkModels();
    if (diags_.hasErrors()) return nullptr;
    // The generics proved only at their instances, for the report.
    if (!notParametric_.empty()) {
      llvm::SmallVector<mlir::Attribute> notes;
      for (const NotParametric &n : notParametric_)
        notes.push_back(b_.getStringAttr(n.where + "\t" + n.generic + "\t" + n.why));
      (*module)->setAttr("pia.not_parametric", b_.getArrayAttr(notes));
    }
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

  // Spec-only state in code (ADR 0041): a value whose type is spec-only
  // (`int`, `real` or a theory's sort), or a record holding one. The
  // verifier sees it and codegen erases it. A buffer of records is one
  // buffer per field, so a spec-only field of its elements is a buffer
  // codegen erases, as `box`'s state is in a `vec (box t)`. A buffer whose
  // elements are wholly spec-only cannot be, since its length is in code,
  // and neither can a buffer nested in an element.
  static bool isSpecScalar(Type t) {
    return mlir::isa_and_nonnull<UnboundedIntType, RealType, SortType>(t);
  }
  static bool hasCodeLeaf(Type t) {
    if (isSpecScalar(t)) return false;
    if (auto r = mlir::dyn_cast<RecordType>(t))
      return llvm::any_of(r.getFieldTypes(), hasCodeLeaf);
    return true;
  }
  static Type specInElement(Type e) {
    if (!hasCodeLeaf(e)) return sema::specOnlyPart(e);
    if (auto r = mlir::dyn_cast<RecordType>(e))
      for (Type f : r.getFieldTypes()) {
        if (mlir::isa<ArrayType, SliceType>(f))
          if (Type x = sema::specOnlyPart(f)) return x;
        if (mlir::isa<RecordType>(f))
          if (Type x = specInElement(f)) return x;
      }
    return {};
  }
  static Type specInBuffer(Type t) {
    if (!t) return {};
    if (auto a = mlir::dyn_cast<ArrayType>(t))
      return specInElement(a.getElementType());
    if (auto sl = mlir::dyn_cast<SliceType>(t))
      return specInElement(sl.getElementType());
    if (auto r = mlir::dyn_cast<RecordType>(t))
      for (Type f : r.getFieldTypes())
        if (Type x = specInBuffer(f)) return x;
    return {};
  }
  std::string specInBufferMessage(Type t) {
    return "type " + typeName(t) + ", whose buffer elements hold the "
           "spec-only type " + typeName(specInBuffer(t)) + "; spec-only state "
           "can be a parameter, a local, a record field or a field of a "
           "buffer's records, but not a whole element of a buffer or part "
           "of a buffer inside one (ADR 0041)";
  }

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
    std::string who = mlir::isa<SortType>(part)
                          ? "a theory's sorts"
                          : "int and real";
    return what + "; " + who + " can be used only in spec functions, "
           "lemmas, contracts and quantifiers, not in code (ADR 0036)";
  }

  // Why code cannot read the spec binding `b` (ADR 0058).
  static std::string specReadMessage(const Binding &b) {
    return "'" + b.name + "' is spec state, which code may write but not "
           "read: only contracts, loop invariants, asserts, lemma calls and "
           "spec parameters may read it, so that codegen can erase it "
           "(ADR 0058)";
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
    b->loopDepth = loopDepth_;
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
      if (n) {
        collectAssigned(*n, names);
        collectThreaded(*n, names);
      }
    std::vector<BindingPtr> out;
    for (const std::string &name : names) {
      BindingPtr b = lookup(name);
      if (b && b->isMutable && !mlir::isa<ArrayType, SliceType>(b->type))
        out.push_back(b);
    }
    return out;
  }

  // The variables passed to a threaded parameter of a call in `n`, which
  // the call rebinds (`threaded`).
  void collectThreaded(const Node &n, std::set<std::string> &out) {
    if (n.kind == NodeKind::Apply && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::Name)
      for (sema::FuncSig *sig : overloadSet(n.kids[0]->text)) {
        std::vector<size_t> through;
        if (sig->isGeneric() && sig->item) {
          // A generic's parameters are resolved per instance, so read the
          // modifiers from its syntax. Type parameters are deduced, so a
          // call passes no argument for them; `carried` drops buffers by
          // the caller's types.
          size_t arg = 0;
          for (const syntax::NodePtr &p : sig->item->kids[0]->kids) {
            if (p->kind != NodeKind::Param) continue;
            if (llvm::is_contained(sig->typeParams, p->text)) continue;
            const Node *annot = p->kids.empty() ? nullptr : p->kids[0].get();
            const Node *mods =
                annot && !annot->kids.empty() ? annot->kids[0].get() : nullptr;
            if (mods && (sema::hasModifier(mods->text, "inout") ||
                         sema::hasModifier(mods->text, "out")))
              through.push_back(arg);
            ++arg;
          }
        } else {
          through = threaded(*sig);
        }
        for (size_t i : through) {
          if (i + 1 >= n.kids.size()) continue;
          // `f g.small` rebinds `g`.
          const Node *a = n.kids[i + 1].get();
          while (a->kind == NodeKind::Field && !a->kids.empty())
            a = a->kids[0].get();
          if (a->kind == NodeKind::Name) out.insert(a->text);
        }
      }
    // A closure that writes a capture is threaded through each use, and
    // so is what it writes (ADR 0044, section 6).
    if (n.kind == NodeKind::Apply)
      for (const syntax::NodePtr &k : n.kids) {
        if (k->kind == NodeKind::Name && k->flags.empty())
          if (BindingPtr b = lookup(k->text); b && !b->refs.empty()) {
            out.insert(k->text);
            for (auto &[field, target] : b->refs) out.insert(target->name);
          }
        if (k->kind == NodeKind::Lambda)
          for (const syntax::NodePtr &c : k->kids)
            if (c->kind == NodeKind::Captures)
              for (const syntax::NodePtr &cap : c->kids)
                if (cap->flags == "inout") out.insert(cap->text);
      }
    for (const syntax::NodePtr &k : n.kids) collectThreaded(*k, out);
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

  // Whether every element of an array literal is an integer literal, so
  // it can be constant data.
  static bool constantElements(const Node &lit) {
    for (const syntax::NodePtr &k : lit.kids) {
      const Node *e = k.get();
      if (e->kind == NodeKind::Neg && e->kids.size() == 1) e = e->kids[0].get();
      if (e->kind != NodeKind::IntLit) return false;
    }
    return true;
  }

  // Fresh storage for a local array (`pia.region`), with the literal's
  // elements stored into it one by one, or another array copied in.
  R genLocalArray(const Node &value, ArrayType arr) {
    Location l = loc(value);
    Value storage = create<RegionOp>(l, arr);
    // A region's elements start as zero.
    if (isZeros(value)) return TV{storage, arr};
    Type elem = arr.getElementType();
    if (value.kind == NodeKind::ListLit) {
      if (value.kids.size() != arr.getLength())
        return fail(value, "an array literal for " + typeName(arr) +
                               " needs " + plural(arr.getLength(), "element") +
                               ", found " + std::to_string(value.kids.size()));
      for (size_t i = 0; i < value.kids.size(); ++i) {
        const Node &k = *value.kids[i];
        R e = genExpr(k, elem);
        if (!e) return e;
        R c = coerce(*e, elem, k);
        if (!c) return c;
        Value at = create<mlir::arith::ConstantIndexOp>(loc(k),
                                                        static_cast<int64_t>(i));
        create<StoreOp>(loc(k), c->value, storage, at);
      }
      return TV{storage, arr};
    }
    R src = genExpr(value, arr);
    if (!src) return src;
    R c = coerce(*src, arr, value);
    if (!c) return c;
    create<CopyOp>(l, c->value, storage);
    return TV{storage, arr};
  }

  // `zeros`, an array of zero elements of the type it is bound at, unless
  // the program defines the name itself (ADR 0058).
  bool isZeros(const Node &n) {
    return n.kind == NodeKind::Name && n.flags.empty() && n.text == "zeros" &&
           !lookup("zeros") && overloadSet("zeros").empty();
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
        fail(*k, "an array literal with computed elements needs storage of "
                 "its own: bind it to a local first, as in "
                 "'let a : [u8; 2] = [x; y] in ...'");
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
    // A generic function from another module's interface sees that
    // module's functions, as its own body did there (ADR 0039).
    AdlScope adl(adlModule_, fromModule(item));
    // A box's call through its union (ADR 0046) assumes that the object's
    // requirement is the erased one: the use check at widen proved it meets
    // the contract, which is all a caller is told.
    struct TrustScope {
      bool &t;
      bool saved;
      ~TrustScope() { t = saved; }
    } trustScope{trusted_, trusted_};
    if (hasFlag(item, "box_trusted")) trusted_ = true;
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
    // The result, then the final value of each threaded parameter.
    auto resultTypes = [&](Type t) {
      llvm::SmallVector<Type> out;
      if (t && !isUnit(t)) out.push_back(t);
      for (size_t i : threaded(sig)) out.push_back(sig.params[i].type);
      return out;
    };

    b_.setInsertionPointToEnd(module_.getBody());
    auto fn = create<mlir::func::FuncOp>(
        l, sig.name, b_.getFunctionType(argTypes, resultTypes(sig.result)));
    // An instance is internal: C calls the generic's instances only through
    // Pia functions, which name concrete types.
    if (!sig.typeArgs.empty()) fn.setPrivate();
    // An instance at concrete types, which the verifier counts against its
    // generic's proof (ADR 0043).
    if (!sig.typeArgs.empty() && !hasFlag(item, "lemma") && !checking_) {
      bool concrete = true;
      for (auto &[n, t] : sig.typeArgs) concrete &= !standIns_.contains(t);
      if (concrete)
        fn->setAttr("pia.instance_of",
                    b_.getStringAttr(llvm::StringRef(sig.name).split('<').first));
    }
    // A specialisation of a higher-order function proved once is an
    // instance of that proof (ADR 0044, step 6).
    if (auto p = provedBy_.find(llvm::StringRef(sig.name).split('<').first.str());
        p != provedBy_.end()) {
      bool concrete = true;
      for (auto &[n, t] : sig.typeArgs) concrete &= !standIns_.contains(t);
      if (concrete && !checking_)
        fn->setAttr("pia.instance_of", b_.getStringAttr(p->second));
      // At another proof's stand-ins, it is part of that proof, which then
      // holds only if this one's does (the verifier checks both).
      else if (!concrete)
        fn->setAttr("pia.proved_by", b_.getStringAttr(p->second));
    }
    // A spec function copied from another module's interface is proved by
    // that module; here it is only unfolded (ADR 0039).
    if (sig.typeArgs.empty() && hasFlag(item, "spec"))
      if (std::string from = fromModule(item); !from.empty())
        fn->setAttr("pia.spec_from", b_.getStringAttr(from));
    // A law or requirement contract that the concept's module proved.
    if (auto a = assertClaims_.find(sig.name); a != assertClaims_.end())
      fn->setAttr("pia.assert_claim", b_.getStringAttr(a->second));
    if (auto c = certified_.find(sig.name); c != certified_.end())
      fn->setAttr("pia.certified", b_.getStringAttr(c->second));
    if (auto e = exports_.find(sig.name); e != exports_.end()) {
      fn->setAttr(PiaDialect::getExportAttrName(),
                  b_.getStringAttr(e->second));
      if (abiC_.count(sig.name))
        fn->setAttr(PiaDialect::getAbiCAttrName(), b_.getUnitAttr());
      if (auto n = linkNames_.find(sig.name); n != linkNames_.end())
        fn->setAttr("pia.link_name", b_.getStringAttr(n->second));
    }
    for (size_t i = 0; i < sig.params.size(); ++i) {
      if (!sig.params[i].modifiers.empty())
        fn.setArgAttr(i, PiaDialect::getModifiersAttrName(),
                      b_.getStringAttr(sig.params[i].modifiers));
      // Codegen erases a spec parameter, and the arguments calls pass for
      // it (ADR 0058).
      if (sig.params[i].spec)
        fn.setArgAttr(i, PiaDialect::getSpecStateAttrName(),
                      b_.getUnitAttr());
    }
    Block *entry = fn.addEntryBlock();
    b_.setInsertionPointToStart(entry);

    scopes_.clear();
    regionBindings_.clear();
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
      b->spec = p.spec;
      b->entry = entry->getArgument(i);
      for (const std::string &r : p.regions) b->lenders.push_back(regionBinding(r));
      // A parameter of a type with regions, which names none, has one of
      // its own.
      if (p.regions.empty() && holdsRegionField(p.type))
        b->lenders.push_back(regionBinding("'" + p.name + "'", p.name));
    }

    overflow_ = OverflowMode::proof;
    fuel_ = 0;
    owns_.clear();
    variadic_.reset();
    solver_.clear();
    ghost_ = false;
    triggers_.clear();
    const Node &ret = *item.kids[1];
    if (ret.kind == NodeKind::RetAnnot && ret.kids.size() > 1 &&
        !genAttributes(*ret.kids[1]))
      return;
    // `@solver(...)`: how Z3 solves this function's goals (ADR 0036).
    if (!solver_.empty()) fn->setAttr("pia.solver", b_.getStringAttr(solver_));
    bool isSpec = hasFlag(item, "spec"), isLemma = hasFlag(item, "lemma");
    bool isAxiom = hasFlag(item, "axiom");
    ghost_ = isSpec || isLemma || isAxiom;
    // A theory's members are named `T.x` (ADR 0036).
    if (hasFlag(item, "theory")) {
      std::string theory = llvm::StringRef(sig.name).split('.').first.str();
      fn->setAttr("pia.theory", b_.getStringAttr(theory));
      if (auto m = theoryInfo_.modelled.find(theory);
          m != theoryInfo_.modelled.end())
        fn->setAttr("pia.modelled", b_.getStringAttr(m->second));
    }
    // A model's items, and the lemmas that check it, see its definitions;
    // nothing else does (sealing).
    if (auto m = theoryInfo_.modelOf.find(sig.name);
        m != theoryInfo_.modelOf.end())
      fn->setAttr("pia.model", b_.getStringAttr(m->second));
    // An `@target(m)` function's proofs see m's values (ADR 0049).
    if (auto t = theoryInfo_.targetOf.find(sig.name);
        t != theoryInfo_.targetOf.end())
      fn->setAttr("pia.target", b_.getStringAttr(t->second));
    if (auto w = theoryInfo_.witnesses.find(sig.name);
        w != theoryInfo_.witnesses.end())
      fn->setAttr("pia.witness_of", b_.getStringAttr(w->second));
    if (auto o = theoryInfo_.obligations.find(sig.name);
        o != theoryInfo_.obligations.end())
      fn->setAttr("pia.obligation",
                  b_.getStringAttr("the model '" + o->second.first +
                                   "' meets the axiom '" + o->second.second +
                                   "'"));
    // A frame lemma that piac wrote for a `reads` clause (ADR 0060,
    // section 3) says what it checks.
    if (llvm::StringRef(sig.name).ends_with("'frame") &&
        hasFlag(item, "lemma")) {
      std::string f = llvm::StringRef(sig.name).drop_back(6).str();
      fn->setAttr("pia.obligation",
                  b_.getStringAttr("'" + f +
                                   "' gives the same result for "
                                   "buffers that agree on what it reads"));
      fn->setAttr("pia.assert_claim",
                  b_.getStringAttr("'" + f +
                                   "' reads only the cells its "
                                   "'reads' clause names"));
    }
    if (!triggers_.empty() && !isAxiom) {
      fail(*triggers_.front(), "@trigger applies only to an axiom");
      return;
    }
    // A theory's abstract spec function has no body: to the verifier it is
    // an uninterpreted function (ADR 0036).
    if (hasFlag(item, "abstract")) {
      fn.getBody().getBlocks().clear();
      fn.setPrivate();
      fn->setAttr(PiaDialect::getSpecAttrName(), b_.getUnitAttr());
      fn->setAttr(PiaDialect::getAbstractAttrName(), b_.getUnitAttr());
      // A constant of `Target` is a value in code too: codegen puts in the
      // value of the model compiled for (ADR 0049).
      if (isTargetValue(sig))
        fn->setAttr("pia.target_value",
                    b_.getStringAttr(theoryInfo_.modelled.at("Target") +
                                     sig.name.substr(6)));
      return;
    }
    // An imported function's body is in another module (ADR 0039).
    if (hasFlag(item, "import")) {
      genImport(item, sig, fn);
      return;
    }
    // Code may take and return spec-only state, which codegen erases, but
    // not in a buffer (ADR 0041).
    if (!ghost_) {
      for (const sema::Param &p : sig.params)
        if (!p.spec && specInBuffer(p.type)) {
          diags_.error(p.loc, "the parameter '" + p.name + "' has " +
                                  specInBufferMessage(p.type));
          return;
        }
      if (specInBuffer(sig.result)) {
        fail(ret, "'" + name + "' returns a value of " +
                      specInBufferMessage(sig.result));
        return;
      }
    }
    if (fuel_ && !isSpec && !isLemma) {
      fail(item, "@fuel applies only to a spec function or a lemma");
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

    // A parameter whose record type refines its fields holds them: the
    // caller proves them, and the body assumes them (ADR 0036).
    for (size_t i = 0; i < sig.params.size(); ++i)
      if (!refine(entry->getArgument(i), sig.params[i].type, false)) return;

    if (isAxiom) {
      fn->setAttr(PiaDialect::getAxiomAttrName(), b_.getUnitAttr());
      genAxiom(item, sig);
      return;
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
      } else if (c->kind == NodeKind::Reads) {
        // `reads xs.[lo .. hi]`: the spec function's footprint (ADR 0060,
        // section 3).
        const Node &e = *c->kids[0];
        if (!hasFlag(item, "spec")) {
          fail(*c, "only a spec function says what it reads");
          return;
        }
        bool byOwner = c->kids.size() == 2;
        // `reads xs.[c] where owner.[c] = v`: the cells an owner array
        // gives to v.
        const Node *ownerAt = nullptr, *value = nullptr;
        if (byOwner) {
          // `owner.[c] = v`, as written or as the operator expands it,
          // `eq (owner.[c]) v`.
          const Node &w = *c->kids[1];
          const Node *lhs = nullptr, *rhs = nullptr;
          if (w.kind == NodeKind::Binary && w.text == "=")
            lhs = w.kids[0].get(), rhs = w.kids[1].get();
          else if (w.kind == NodeKind::Apply && w.kids.size() == 3 &&
                   w.kids[0]->kind == NodeKind::Name && w.kids[0]->text == "eq")
            lhs = w.kids[1].get(), rhs = w.kids[2].get();
          if (lhs && e.kind == NodeKind::Index &&
              e.kids[1]->kind == NodeKind::Name &&
              lhs->kind == NodeKind::Index &&
              lhs->kids[0]->kind == NodeKind::Name &&
              lhs->kids[1]->kind == NodeKind::Name &&
              lhs->kids[1]->text == e.kids[1]->text) {
            ownerAt = lhs->kids[0].get();
            value = rhs;
          }
        }
        if (e.kind != NodeKind::Index || e.kids[0]->kind != NodeKind::Name ||
            (!byOwner && e.kids[1]->kind != NodeKind::Range) ||
            (byOwner && !ownerAt)) {
          fail(e, "a footprint is a range of a buffer parameter, as in "
                  "'reads xs.[lo .. hi]', or the cells an owner array gives "
                  "to a value, as in 'reads xs.[c] where owner.[c] = v'");
          return;
        }
        BindingPtr buf = lookup(e.kids[0]->text);
        if (!buf || !buf->isParam || !elementType(buf->type)) {
          fail(*e.kids[0], "a footprint names a buffer parameter");
          return;
        }
        if (byOwner) {
          BindingPtr owner = lookup(ownerAt->text);
          if (!owner || !owner->isParam || !elementType(owner->type) ||
              !mlir::isa<IntType>(elementType(owner->type))) {
            fail(*ownerAt,
                 "a footprint's owner is an array parameter of integers");
            return;
          }
          R v = genContractExpr(*value, Type());
          if (!v)
            return;
          create<contract::ReadsOp>(loc(*c), buf->value, v->value, v->value,
                                    owner->value);
        } else {
          R lo = genContractExpr(*e.kids[1]->kids[0], types_.usize());
          R hi = lo ? genContractExpr(*e.kids[1]->kids[1], types_.usize())
                    : std::nullopt;
          if (!lo || !hi)
            return;
          create<contract::ReadsOp>(loc(*c), buf->value, lo->value, hi->value,
                                    Value());
        }
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
    struct MovedScope {
      std::map<BindingPtr, Move> &moved;
      std::map<BindingPtr, Move> saved;
      unsigned &depth, savedDepth;
      ~MovedScope() {
        moved = std::move(saved);
        depth = savedDepth;
      }
    } movedScope{moved_, std::move(moved_), loopDepth_, loopDepth_};
    moved_.clear();
    // Moves out of buffer elements are this function's own.
    struct ElementScope {
      std::map<const Node *, mlir::Operation *> &moved;
      std::map<const Node *, syntax::SourceLoc> &copied;
      std::map<const Node *, mlir::Operation *> savedMoved;
      std::map<const Node *, syntax::SourceLoc> savedCopied;
      ~ElementScope() {
        moved = std::move(savedMoved);
        copied = std::move(savedCopied);
      }
    } elementScope{movedOut_, copiedOut_, std::move(movedOut_),
                   std::move(copiedOut_)};
    movedOut_.clear();
    copiedOut_.clear();
    loopDepth_ = 0;
    frames_.clear();
    frames_.emplace_back();
    frames_.back().result = sig.result;
    frames_.back().function = sig.source();
    // `drop` itself takes its argument apart rather than dropping it.
    struct DropScope {
      Type &t;
      Type saved;
      ~DropScope() { t = saved; }
    } dropScope{dropping_, dropping_};
    dropping_ = sig.name == "drop" && sig.params.size() == 1
                    ? sig.params[0].type
                    : Type();
    // `= extern "symbol"`: a C function (#55).
    std::string foreign;
    bool isExtern = externSymbol(bodyNode, foreign);
    if (isExtern) {
      fn.setPrivate();
      fn->setAttr("pia.extern", b_.getStringAttr(foreign));
    }
    // The buffer it lends is `out`, unwritten: a caller finds every
    // element of it empty (ADR 0048, section 6).
    if (sema::hasModifier(sig.lentModifiers, "out"))
      fn->setAttr("pia.out_result", b_.getUnitAttr());
    // A `moved` parameter with a `drop` is dropped at the end of the body
    // unless it is consumed first.
    const Node *bodyPtr = &bodyNode;
    // `with_arena n (let (a) => body)` is a `let` of a fresh arena (#70).
    if (usesArenas_ && !isSpec && !ghost_ && !isExtern &&
        mentions(bodyNode, "with_arena") && overloadSet("with_arena").empty()) {
      syntax::NodePtr copy = syntax::clone(bodyNode);
      desugarArenas(copy);
      bodyPtr = keep(std::move(copy));
    }
    if (!isSpec && !ghost_ && !isExtern)
      for (const sema::Param &p : sig.params)
        if (sema::hasModifier(p.modifiers, "moved"))
          if (BindingPtr b = lookup(p.name); b && needsDrop(b)) {
            const Node &d = dropNode(p.name, p.loc);
            bodyPtr = keep(withCleanup(*bodyPtr, d));
            frames_.back().defers.push_back(&d);
          }
    if (!isSpec) addTails(*bodyPtr);
    if (variadic_ && !isExtern) {
      fail(*variadicNode_, "@variadic is only for a foreign declaration, "
                           "'= extern \"symbol\"'");
      return;
    }
    // A function with `@owns(buf, owner, b)` checks every access to `buf`
    // as a spread iteration `b` would (ADR 0060).
    if (!owns_.empty() && !footprintScope(item))
      return;
    R body = isExtern ? genForeign(bodyNode, foreign, sig, entry)
             : isSpec ? genContractExpr(bodyNode, sig.result)
                      : genExpr(*bodyPtr, sig.result);
    spread_.reset();
    if (!body) return;
    if (!isSpec && !ghost_)
      for (size_t i : threaded(sig))
        if (BindingPtr b = lookup(sig.params[i].name))
          for (const BindingPtr &l : b->lenders)
            if (l->region && !l->regionOf.empty() &&
                l->regionOf != sig.params[i].name) {
              fail(bodyNode, "'" + name + "' stores in '" + b->name +
                                 "' a value borrowed from what '" +
                                 l->regionOf + "' borrows from; give both "
                                 "one region, as in '(r : region)', with " +
                                 "the region in both their types");
              return;
            } else if (l->region && l->regionOf.empty() &&
                       !llvm::is_contained(sig.params[i].regions, l->name)) {
              fail(bodyNode, "'" + name + "' stores in '" + b->name +
                                 "' a value borrowed from the region '" +
                                 l->name + "', which its type does not "
                                 "mention");
              return;
            } else if (!l->region && sig.params[i].lender.empty() &&
                       !sig.params[i].regions.empty()) {
              fail(bodyNode, "'" + name + "' stores in '" + b->name +
                                 "' a value borrowed from '" + l->name +
                                 "', which ends with '" + name + "'; '" +
                                 b->name + "' may hold only loans from its "
                                 "region '" + sig.params[i].regions[0] + "'");
              return;
            } else if (!l->region && l->name != sig.params[i].lender) {
              fail(bodyNode, "'" + name + "' stores a value borrowed from '" +
                                 l->name + "' in '" + b->name + "'; say so "
                                 "in its parameter, as in '(" + b->name +
                                 " : borrowed(" + l->name + ")" +
                                 withoutBorrowed(sig.params[i].modifiers) +
                                 " " + typeName(b->type) + ")'");
              return;
            }
    if (!isSpec && !ghost_)
      for (const BindingPtr &l : lendersOf(*bodyPtr))
        if (l->region && !l->regionOf.empty()) {
          fail(bodyNode, "'" + name + "' returns a value borrowed from what '" +
                             l->regionOf + "' borrows from; give '" +
                             l->regionOf + "' a region, as in '(r : region)' "
                             "and a type that mentions it, and say so in the "
                             "result type, as in ': borrowed(r) " +
                             typeName(body->type) + "'");
          return;
        } else if (l->region && !llvm::is_contained(sig.resultRegions, l->name)) {
          fail(bodyNode, "'" + name + "' returns a value borrowed from the "
                             "region '" + l->name + "'; say so in its result "
                             "type, as in ': borrowed(" + l->name + ") " +
                             typeName(body->type) + "'");
          return;
        } else if (!l->region && l->name != sig.resultLender) {
          fail(bodyNode, "'" + name + "' returns a value borrowed from '" +
                             l->name + "'; say so in its result type, as in "
                             "': borrowed(" + l->name + ") " +
                             typeName(body->type) + "'");
          return;
        }
    if (!isSpec && !ghost_) {
      bool owned = true;
      for (const sema::Param &p : sig.params) {
        BindingPtr b = lookup(p.name);
        if (!b) continue;
        if (sema::hasModifier(p.modifiers, "moved")) {
          owned &= consumed(b, p.loc);
        } else if (auto m = moved_.find(b); m != moved_.end()) {
          diags_.error(m->second.at,
                       "'" + p.name + "' is borrowed by this function, so it "
                       "cannot be consumed here; take it as 'moved'");
          owned = false;
        }
      }
      // An owning element read as a value out of a buffer this function
      // cannot write would leave the box in both places.
      for (const auto &[node, at] : copiedOut_) {
        diags_.error(at, "this moves an element that owns its slices out "
                         "of a buffer that cannot be written, which would "
                         "leave it in both; borrow it, as in a field read, "
                         "or take the buffer as 'inout'");
        owned = false;
      }
      if (!owned) return;
    }
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

    bool hasResult = !rets.empty();
    // A threaded parameter's final value goes back to the caller.
    for (size_t i : threaded(sig))
      rets.push_back(lookup(sig.params[i].name)->value);
    pushScope();
    if (hasResult) bind("result", rets[0], result, false);
    // So does a result: the function proves its fields' refinements.
    if (hasResult && !refine(rets[0], result, true)) return;
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind != NodeKind::Ensures) continue;
      R p = genPredicate(*c->kids[0]);
      if (!p) return;
      create<contract::EnsuresOp>(loc(*c), p->value);
    }
    popScope();
    create<mlir::func::ReturnOp>(l, rets);
  }

  // A function imported from another module's interface (ADR 0039): the
  // interface's `requires`, a result the verifier knows nothing more about,
  // and the interface's `ensures` about it. Callers are checked against
  // that contract, as against any callee's; the function itself is not
  // verified here, since its module proves it meets the interface.
  void genImport(const Node &item, const sema::FuncSig &sig,
                 mlir::func::FuncOp fn) {
    std::string from;
    llvm::SmallVector<llvm::StringRef> words;
    llvm::StringRef(item.flags).split(words, ' ', -1, false);
    for (llvm::StringRef w : words)
      if (w.consume_front("from:")) from = w.str();
    fn->setAttr(PiaDialect::getImportAttrName(), b_.getStringAttr(from));
    fn.setPrivate();
    const Node &contracts = *item.kids[2];
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind != NodeKind::Requires) continue;
      R p = genPredicate(*c->kids[0]);
      if (!p) return;
      create<contract::RequiresOp>(loc(*c), p->value);
    }
    llvm::SmallVector<Value> rets;
    pushScope();
    if (sig.result && !isUnit(sig.result)) {
      Value r = create<ArbitraryOp>(loc(item), sig.result).getResult();
      rets.push_back(r);
      bind("result", r, sig.result, false);
    }
    // A threaded parameter's final value is unknown but for the `ensures`.
    for (size_t i : threaded(sig)) {
      Value v = create<ArbitraryOp>(loc(item), sig.params[i].type).getResult();
      rets.push_back(v);
      if (BindingPtr b = lookup(sig.params[i].name)) b->value = v;
    }
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind != NodeKind::Ensures) continue;
      R p = genPredicate(*c->kids[0]);
      if (!p) return;
      create<contract::EnsuresOp>(loc(*c), p->value);
    }
    popScope();
    create<mlir::func::ReturnOp>(loc(item), rets);
  }

  // `{ p : real where 0.0 <= p }`: a `requires` (or, for a result, an
  // `ensures`) per refined field of `v`'s record type, and of the records
  // in its fields, with the field's name standing for the field.
  bool refined(Type t) {
    auto rec = mlir::dyn_cast<RecordType>(t);
    if (!rec) return false;
    if (types_.refinements(rec.getName().str())) return true;
    for (Type ft : rec.getFieldTypes())
      if (refined(ft)) return true;
    return false;
  }

  bool refine(Value v, Type t, bool ensures) {
    if (!refined(t)) return true;
    auto rec = mlir::cast<RecordType>(t);
    for (auto [name, ft] : llvm::zip(rec.getFieldNames(), rec.getFieldTypes()))
      if (mlir::isa<RecordType>(ft)) {
        Value f = create<FieldOp>(b_.getUnknownLoc(), ft, v, name);
        if (!refine(f, ft, ensures)) return false;
      }
    const auto *refs = types_.refinements(rec.getName().str());
    if (!refs) return true;
    for (const auto &[field, pred] : *refs) {
      auto index = rec.fieldIndex(field);
      if (!index) continue;
      Type ft = rec.getFieldTypes()[*index];
      Location l = loc(*pred);
      Value f = create<FieldOp>(l, ft, v, b_.getStringAttr(field));
      scopes_.emplace_back();
      scopes_.back()[field] = std::make_shared<Binding>();
      scopes_.back()[field]->name = field;
      scopes_.back()[field]->value = f;
      scopes_.back()[field]->type = ft;
      R p = genPredicate(*pred);
      scopes_.pop_back();
      if (!p) return false;
      if (ensures)
        create<contract::EnsuresOp>(l, p->value);
      else
        create<contract::RequiresOp>(l, p->value);
    }
    return true;
  }

  // An axiom (ADR 0036): its preconditions and postconditions, and its
  // triggers, with no body. The verifier quantifies them over the
  // parameters; nothing proves them, since without a model they are
  // trusted.
  void genAxiom(const Node &item, const sema::FuncSig &sig) {
    const Node &contracts = *item.kids[2];
    bool ensures = false;
    for (const syntax::NodePtr &c : contracts.kids) {
      if (c->kind == NodeKind::Requires || c->kind == NodeKind::Ensures) {
        R p = genPredicate(*c->kids[0]);
        if (!p) return;
        if (c->kind == NodeKind::Requires)
          create<contract::RequiresOp>(loc(*c), p->value);
        else
          create<contract::EnsuresOp>(loc(*c), p->value);
        ensures |= c->kind == NodeKind::Ensures;
      } else {
        fail(*c, "an axiom has only 'requires' and 'ensures'");
        return;
      }
    }
    if (!ensures) {
      fail(item, "the axiom '" + sig.name + "' states nothing: give it an "
                 "'ensures'");
      return;
    }
    if (sig.result && !isUnit(sig.result)) {
      fail(item, "an axiom has no result: what it states goes in 'ensures'");
      return;
    }
    for (const Node *t : triggers_) {
      llvm::SmallVector<Value> terms;
      for (const syntax::NodePtr &k : t->kids) {
        R v = genContractExpr(*k, Type());
        if (!v) return;
        terms.push_back(v->value);
      }
      create<contract::TriggerOp>(loc(*t), terms);
    }
    create<mlir::func::ReturnOp>(loc(item), mlir::ValueRange{});
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
  // An ordinary function whose body is a definition, as a spec function's
  // is: scalar parameters and result, and no loop, call, buffer, write or
  // `abort`, so it always returns exactly what its body computes. A spec
  // function may call one, such as a concept's `less` for u8, and the
  // verifier unfolds it there (docs/verifier.md).
  // A record of scalars counts as scalars: the verifier splits it into
  // its fields, as for a lambda's closure (ADR 0044). A call is allowed
  // to a spec function or another such function, without recursion.
  static bool scalarish(mlir::Type t) {
    if (mlir::isa<IntType>(t) || t.isInteger(1)) return true;
    if (auto r = mlir::dyn_cast<RecordType>(t)) {
      for (mlir::Type f : r.getFieldTypes())
        if (!scalarish(f)) return false;
      return true;
    }
    return false;
  }
  static bool definesValue(mlir::func::FuncOp f) {
    std::set<mlir::Operation *> visiting;
    return definesValue(f, visiting);
  }
  static bool definesValue(mlir::func::FuncOp f,
                           std::set<mlir::Operation *> &visiting) {
    if (!f || f.isExternal() || f.getNumResults() != 1) return false;
    // An imported function means what its interface's contract says.
    if (f->hasAttr(PiaDialect::getImportAttrName())) return true;
    if (!scalarish(f.getFunctionType().getResult(0))) return false;
    for (mlir::Type t : f.getFunctionType().getInputs())
      if (!scalarish(t)) return false;
    if (!visiting.insert(f.getOperation()).second) return false;
    auto module = f->getParentOfType<mlir::ModuleOp>();
    bool ok = true;
    f.walk([&](mlir::Operation *op) {
      if (auto c = mlir::dyn_cast<mlir::func::CallOp>(op)) {
        auto callee =
            module ? module.lookupSymbol<mlir::func::FuncOp>(c.getCallee())
                   : mlir::func::FuncOp();
        if (!callee ||
            !(callee->hasAttr(PiaDialect::getSpecAttrName()) ||
              definesValue(callee, visiting)))
          ok = false;
      } else if (mlir::isa<mlir::scf::ForOp, mlir::scf::WhileOp, AbortOp,
                           LoadOp, StoreOp>(op)) {
        ok = false;
      }
    });
    visiting.erase(f.getOperation());
    return ok;
  }

  void checkGhosts() {
    auto isSpec = [](mlir::func::FuncOp f) {
      return f && f->hasAttr(PiaDialect::getSpecAttrName());
    };
    std::map<std::string, std::vector<std::string>> calls;
    for (auto f : module_.getOps<mlir::func::FuncOp>()) {
      if (!isSpec(f) || f.isExternal()) continue;  // abstract: no body
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
          if (isSpec(callee))
            calls[name].push_back(call.getCallee().str());
          else if (!definesValue(callee))
            diags_.error(sourceLoc(op->getLoc()),
                         "a spec function can call only spec functions and "
                         "pure functions of scalars (no loop, call, buffer "
                         "or 'abort'), and '" + call.getCallee().str() +
                             "' is neither");
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

  // A model defines each abstract function with the theory's type, its
  // sorts replaced by the model's (ADR 0036).
  void checkModels() {
    for (const auto &[item, model] : theoryInfo_.modelOf) {
      if (theoryInfo_.obligations.count(item) ||
          theoryInfo_.witnesses.count(item))
        continue;
      auto f = module_.lookupSymbol<mlir::func::FuncOp>(item);
      if (!f) continue;
      std::string member = item.substr(model.size());  // ".x"
      mlir::func::FuncOp abstract;
      std::string theory;
      for (const auto &[t, m] : theoryInfo_.modelled)
        if (m == model) theory = t;
      abstract = module_.lookupSymbol<mlir::func::FuncOp>(theory + member);
      if (!abstract) continue;
      auto as = [&](Type t) -> Type {
        if (auto so = mlir::dyn_cast<SortType>(t)) {
          std::string name = so.getName().str();
          if (Type m = types_.named(model + name.substr(theory.size())))
            return m;
        }
        return t;
      };
      mlir::FunctionType want = abstract.getFunctionType();
      mlir::FunctionType have = f.getFunctionType();
      bool same = want.getNumInputs() == have.getNumInputs() &&
                  want.getNumResults() == have.getNumResults();
      for (unsigned i = 0; same && i < want.getNumInputs(); ++i)
        same = as(want.getInput(i)) == have.getInput(i);
      for (unsigned i = 0; same && i < want.getNumResults(); ++i)
        same = as(want.getResult(i)) == have.getResult(i);
      if (!same) {
        std::string w;
        for (unsigned i = 0; i < want.getNumInputs(); ++i)
          w += typeName(as(want.getInput(i))) + " -> ";
        w += want.getNumResults() ? typeName(as(want.getResult(0))) : "unit";
        diags_.error(sourceLoc(f.getLoc()),
                     "the model '" + model + "' defines '" + theory + member +
                         "' with the wrong type: in this model it is " + w);
      }
    }
  }

  // Every axiom needs a trigger, or the solver would never use it, or use
  // it without limit (ADR 0036).
  void checkAxioms() {
    for (auto f : module_.getOps<mlir::func::FuncOp>()) {
      if (!f->hasAttr(PiaDialect::getAxiomAttrName())) continue;
      for (mlir::Type t : f.getFunctionType().getInputs())
        if (mlir::isa<ArrayType, SliceType>(t)) {
          diags_.error(sourceLoc(f.getLoc()),
                       "an axiom's parameters are values, not buffers");
          return;
        }
      verify::AxiomTriggers t = verify::axiomTriggers(module_, f);
      if (t.triggers.empty() && !t.error.empty())
        diags_.error(sourceLoc(f.getLoc()), "the axiom '" +
                                                f.getSymName().str() +
                                                "' has no trigger: " + t.error);
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
      // `@solver(nlsat)` or `@solver(tactic = "(then simplify smt)")`
      // chooses the Z3 strategy for the function's goals (ADR 0036).
      if (a->text == "solver") {
        std::string strategy;
        // `nlsat` names Z3's nonlinear real arithmetic strategy,
        // `qfnra-nlsat`, which prepares the goal for the nlsat tactic.
        if (a->kids.size() == 1 && a->kids[0]->kind == NodeKind::Name)
          strategy = a->kids[0]->text == "nlsat" ? "qfnra-nlsat"
                                                  : a->kids[0]->text;
        else if (a->kids.size() == 1 && a->kids[0]->kind == NodeKind::NamedArg &&
                 a->kids[0]->text == "tactic" &&
                 a->kids[0]->kids[0]->kind == NodeKind::StringLit)
        {
          strategy = a->kids[0]->kids[0]->text;
          if (strategy.size() >= 2 && strategy.front() == '"' &&
              strategy.back() == '"')
            strategy = strategy.substr(1, strategy.size() - 2);
        }
        if (strategy.empty()) {
          fail(*a, "@solver takes a Z3 tactic's name, as in @solver(nlsat), "
                   "or a strategy, as in @solver(tactic = \"(then simplify "
                   "smt)\")");
          return false;
        }
        if (std::optional<std::string> why = verify::checkStrategy(strategy)) {
          fail(*a, "@solver: " + *why);
          return false;
        }
        solver_ = strategy;
        continue;
      }
      // `@variadic(n)` on a foreign declaration: the C function has n
      // named parameters, and the rest are its variadic ones (ADR 0051).
      if (a->text == "variadic" && a->kids.size() == 1 &&
          a->kids[0]->kind == NodeKind::IntLit) {
        auto lit = sema::parseIntLiteral(a->kids[0]->text);
        if (!lit || !lit->suffix.empty() || lit->value.ugt(64)) {
          fail(*a, "@variadic takes the number of the C function's named "
                   "parameters");
          return false;
        }
        variadic_ = static_cast<unsigned>(lit->value.getZExtValue());
        variadicNode_ = a.get();
        continue;
      }
      // `@allow(range_requires)` silences a lint (ADR 0037); lints run on
      // the syntax tree, so there is nothing to generate.
      // `@trigger(t1, t2)` on an axiom: one pattern (ADR 0036).
      if (a->text == "trigger" && !a->kids.empty()) {
        triggers_.push_back(a.get());
        continue;
      }
      // `@owns(buf, owner, b)`: the function touches only the cells c of
      // `buf` with `owner.[c] = b` (ADR 0060); checked with the body.
      if (a->text == "owns" && a->kids.size() == 3 &&
          llvm::all_of(a->kids, [](const syntax::NodePtr &k) {
            return k->kind == NodeKind::Name;
          })) {
        owns_.push_back(a.get());
        continue;
      }
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
    lent_.erase(&n);
    writable_.erase(&n);
    // A spec-only place in code, such as `p.heap <- Alloc.take p.heap s`
    // or a spec-only argument: its value is specification, as in a
    // contract, and codegen erases it (ADR 0041).
    if (!contract_ && !ghost_ && isSpecScalar(expected)) {
      contract_ = true;
      R r = genExprOf(n, expected);
      contract_ = false;
      return r;
    }
    R r = genExprOf(n, expected);
    if (r && !contract_ && !ghost_ && isSpecScalar(r->type))
      return fail(n, "this expression has " + specOnlyMessage(r->type) +
                     "; code can only store it in a spec-only place, such as "
                     "a field, local or parameter of that type (ADR 0041)");
    if (r) noteLenders(n, *r);
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
            if (!syntax::isDigitSeparator(c))
              digits.push_back(c);
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
      case NodeKind::Spread:
        return genSpread(n);
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
        // An assumption is never checked, so it is a trusted item, and
        // only a file marked @trusted may make one (ADR 0023).
        if (n.kind == NodeKind::Assume && !trusted_)
          return fail(n, "'assume' is only allowed in a file marked "
                         "'@trusted' (ADR 0023), since nothing checks it: "
                         "prove the fact with 'assert' or a lemma, make it "
                         "a 'requires' if callers can promise it, or mark "
                         "the file '@trusted' on a line of its own");
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
      case NodeKind::Lambda: {
        // A lambda as a value is its closure (ADR 0044, section 6).
        if (contract_ || ghost_)
          return fail(n, "a lambda cannot be a value in a contract yet");
        std::optional<Captures> caps = capturesOf(n);
        if (!caps) return std::nullopt;
        std::optional<Closure> c = closureOf(n, nullptr, {}, "", *caps);
        if (!c) return std::nullopt;
        R v = genExpr(*c->value, c->type);
        if (v && !c->lenders.empty()) lent_[&n] = c->lenders;
        if (v) closureRefs_[&n] = c->refs;
        return v;
      }
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
      if (BindingPtr b = lookup(n.text)) {
        if (!usable(b, n)) return std::nullopt;
        if (b->spec && !contract_ && !ghost_)
          return fail(n, specReadMessage(*b));
        // A referenced capture is the lambda's alone while it is live.
        if (!contract_ && !ghost_)
          if (auto [x, use] = writerOf(b, n); x)
            return fail(n, "'" + b->name + "' is captured by '" + x->name +
                               "' as 'inout', so it cannot be read here; " +
                               stillUsed(x, n, use) + ", and its writes are "
                               "seen after its last use");
        consumeValue(b, n);
        return TV{b->value, b->type};
      }
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
    if (hofs_.count(n.text))
      return fail(n, "'" + n.text + "' takes a function; passing it as a "
                     "value comes later (ADR 0044)");
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
        if (contract_ && a.type == c.type && (op == "=" || op == "<>")) {
          // At the definition, equality of the values themselves, which a
          // generic proof encodes as equality in its sort (ADR 0043).
          Value eq = standInEq(l, a.value, c.value, a.type);
          if (op == "<>")
            eq = create<mlir::arith::XOrIOp>(l, eq, boolConst(l, true));
          return TV{eq, boolType()};
        }
        Type t = archetypes_.count(a.type) ? a.type : c.type;
        return fail(n, "'" + op + "' is not defined for every '" +
                           typeName(t) + "'; a generic body can use only "
                           "what its constraints promise");
      }
      if (contract_ && a.type == c.type && (op == "=" || op == "<>") &&
          (mlir::isa<ArrayType>(a.type) || mlir::isa<SliceType>(a.type)))
        return genBufferEq(n, op, a, c);
      if (mlir::isa<SortType>(a.type) || mlir::isa<SortType>(c.type)) {
        // A theory's sort has equality and nothing else (ADR 0036).
        if (a.type != c.type)
          return fail(n, "'" + op + "' needs operands of one type, found " +
                             typeName(a.type) + " and " + typeName(c.type));
        if (op != "=" && op != "<>")
          return fail(n, "'" + op + "' is not defined on the sort " +
                             typeName(a.type) + ", which has only = and <>");
        return TV{create<ExactCmpOp>(l, b_.getI1Type(),
                                     CmpPredicateAttr::get(
                                         &ctx_, op == "=" ? CmpPredicate::eq
                                                          : CmpPredicate::ne),
                                     a.value, c.value),
                  boolType()};
      }
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
      // A spec function's `int` result, or another exact context, takes
      // the exact value: `b * 16` with a range-typed `b` cannot overflow.
      if (isExact(expected) &&
          (op == "+" || op == "-" || op == "*" || op == "/" || op == "%") &&
          mlir::isa<IntType>(ops->first.type) &&
          mlir::isa<IntType>(ops->second.type)) {
        R l2 = coerce(ops->first, expected, lhsNode);
        if (!l2) return std::nullopt;
        return genExactArith(n, op, *l2, ops->second, lhsNode, rhsNode);
      }
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

  // Some value of `t`: its lowest integer, false, an empty slice, or a
  // record of those.
  Value defaultValue(Location l, Type t) {
    if (auto it = mlir::dyn_cast<IntType>(t)) {
      llvm::APInt v = it.contains(llvm::APInt(kWidth, 0))
                          ? llvm::APInt(kWidth, 0)
                          : it.getLo().sextOrTrunc(kWidth);
      return create<ConstantOp>(
          l, it, b_.getIntegerAttr(b_.getIntegerType(kWidth), v));
    }
    if (isBool(t)) return boolConst(l, false);
    // A spec-only `int`, such as a block's owner (ADR 0041): 0, exactly.
    if (mlir::isa<UnboundedIntType>(t)) {
      llvm::APInt zero(kWidth, 0);
      Type z = IntType::get(&ctx_, zero, zero);
      Value c = create<ConstantOp>(
          l, z, b_.getIntegerAttr(b_.getIntegerType(kWidth), zero));
      return create<ExactConvertOp>(l, t, c);
    }
    if (auto st = mlir::dyn_cast<SliceType>(t))
      return create<EmptyOp>(l, st).getResult();
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
    if (auto rt = mlir::dyn_cast<RecordType>(s->type);
        rt && !types_.isVariant(rt))
      return genRecordMatch(n, *s, rt, expected);
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
        else if (a.as.empty())
          for (const sema::Ctor *c : ctors)
            if (!covered.count(c->name) && c->payload && isLinear(c->payload))
              return fail(pat, "this arm drops the @linear payload of '" +
                                   c->name + "'; match '" + c->name +
                                   "' with a name and consume it");
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
          if (!only && sub.text == "_" && a.as.empty() && isLinear(c->payload))
            return fail(sub, "'_' drops this @linear payload; bind it with a "
                             "name and consume it");
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
    {
      BindingPtr h = bind(hidden, s->value, s->type, false);
      h->lenders = lendersOf(*n.kids[0]);
      h->writable = writable(*n.kids[0]);
    }
    R r = genExpr(*chain, expected);
    popScope();
    passLenders(n, *chain);
    matchTrees_.push_back(std::move(chain));  // diagnostics may point into it
    return r;
  }

  // `match r with | { a; b = x } -> e` on a record: binds its fields, as
  // `let a = r.a in let x = r.b in e`. Matching consumes `r`, so this is
  // how a @linear record is finally taken apart (#56).
  R genRecordMatch(const Node &n, const TV &s, RecordType rt, Type expected) {
    if (n.kids.size() != 2)
      return fail(*n.kids[2]->kids[0], "a record has one shape, so a 'match' "
                                       "on it has one arm");
    const Node &arm = *n.kids[1];
    if (arm.kids.size() > 2 && !arm.kids[2]->kids.empty())
      return fail(*arm.kids[2], "arm contracts on a record 'match' are not "
                                "supported yet");
    const Node &pat = *arm.kids[0];
    std::string hidden = "#match" + std::to_string(matchCounter_++);
    syntax::SourceLoc at = n.loc;
    std::vector<std::pair<std::string, std::string>> binds;  // name, field
    if (pat.kind == NodeKind::PVar && !types_.isCtorName(pat.text)) {
      if (pat.text == "_" && isLinear(rt))
        return fail(pat, "'_' drops this @linear value; bind its fields "
                         "and consume the @linear ones");
    } else if (pat.kind == NodeKind::PRecord) {
      std::set<std::string> seen;
      for (const syntax::NodePtr &f : pat.kids) {
        std::optional<unsigned> i = rt.fieldIndex(f->text);
        if (!i)
          return fail(*f, typeName(rt) + " has no field '" + f->text + "'");
        if (!seen.insert(f->text).second)
          return fail(*f, "'" + f->text + "' is already matched");
        std::string name = f->text;
        if (!f->kids.empty() && f->kids[0]->kind != NodeKind::None) {
          const Node &sub = *f->kids[0];
          if (sub.kind != NodeKind::PVar || types_.isCtorName(sub.text))
            return fail(sub, "only a name or '_' can match a field for now");
          name = sub.text;
        }
        if (name == "_") {
          if (isLinear(rt.getFieldTypes()[*i]))
            return fail(*f, "'_' drops the @linear field '" + f->text +
                            "'; bind it and consume it");
          continue;
        }
        binds.emplace_back(name, f->text);
      }
      for (auto [j, field] : llvm::enumerate(rt.getFieldNames()))
        if (!seen.count(field.getValue().str()) &&
            isLinear(rt.getFieldTypes()[j]))
          return fail(pat, "this pattern drops the @linear field '" +
                               field.getValue().str() +
                               "'; bind it and consume it");
    } else {
      return fail(pat, "a record is matched by '{ a; b = x }', a name or '_'");
    }
    syntax::NodePtr body = syntax::clone(*arm.kids[1]);
    if (pat.kind == NodeKind::PVar && pat.text != "_") {
      auto let = syntax::makeNode(NodeKind::LetIn, pat.loc, pat.text);
      let->add(syntax::makeNode(NodeKind::Params, pat.loc));
      let->add(syntax::makeNode(NodeKind::None, pat.loc));
      let->add(syntax::makeNode(NodeKind::Contracts, pat.loc));
      let->add(syntax::makeNode(NodeKind::Name, pat.loc, hidden));
      let->add(std::move(body));
      body = std::move(let);
    }
    for (auto it = binds.rbegin(); it != binds.rend(); ++it) {
      auto field = syntax::makeNode(NodeKind::Field, at, it->second);
      field->add(syntax::makeNode(NodeKind::Name, at, hidden));
      auto let = syntax::makeNode(NodeKind::LetIn, at, it->first);
      let->add(syntax::makeNode(NodeKind::Params, at));
      let->add(syntax::makeNode(NodeKind::None, at));
      let->add(syntax::makeNode(NodeKind::Contracts, at));
      let->add(std::move(field));
      let->add(std::move(body));
      body = std::move(let);
    }
    if (!frames_.empty() && frames_.back().tails.count(&n)) addTails(*body);
    const Node &chain = *body;
    matchTrees_.push_back(std::move(body));  // diagnostics may point into it
    pushScope();
    {
      BindingPtr h = bind(hidden, s.value, s.type, false);
      h->lenders = lendersOf(*n.kids[0]);
      h->writable = writable(*n.kids[0]);
    }
    R r = genExpr(chain, expected);
    popScope();
    passLenders(n, chain);
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

  // `clz x`, `ctz x`, `popcount x`, `bswap x`, `rotl x n` and `rotr x n`
  // work on the storage bits of an unsigned operand (docs/stdlib.md, group
  // 2). Their result types are exact: [0, w] for the counts, and the whole
  // w-bit unsigned type for the others.
  R genBitBuiltin(const Node &n, const std::string &name) {
    bool rotate = name == "rotl" || name == "rotr";
    size_t argc = n.kids.size() - 1;
    if (argc != (rotate ? 2u : 1u))
      return fail(n, "'" + name + "' takes " +
                         (rotate ? "two arguments" : "one argument"));
    R v = genExpr(*n.kids[1], Type());
    if (!v) return v;
    auto t = mlir::dyn_cast<IntType>(v->type);
    if (!t || t.getLo().isNegative())
      return fail(*n.kids[1], "'" + name + "' needs an unsigned integer, "
                                  "found " + typeName(v->type));
    unsigned w = t.getStorageWidth();
    Location l = loc(n);
    llvm::APInt zero(kWidth, 0);
    if (name == "clz" || name == "ctz" || name == "popcount") {
      auto rt = IntType::get(&ctx_, zero, llvm::APInt(kWidth, w));
      Value r;
      if (name == "clz") r = create<ClzOp>(l, rt, v->value);
      else if (name == "ctz") r = create<CtzOp>(l, rt, v->value);
      else r = create<PopcountOp>(l, rt, v->value);
      return TV{r, rt};
    }
    auto full = IntType::get(&ctx_, zero,
                             llvm::APInt::getMaxValue(w).zext(kWidth));
    if (name == "bswap") return TV{create<BSwapOp>(l, full, v->value), full};
    R amount = genExpr(*n.kids[2], Type());
    if (!amount) return amount;
    if (!mlir::isa<IntType>(amount->type))
      return fail(*n.kids[2], "'" + name + "' needs an integer amount, found " +
                                  typeName(amount->type));
    Value r = name == "rotl"
                  ? Value(create<RotlOp>(l, full, v->value, amount->value))
                  : Value(create<RotrOp>(l, full, v->value, amount->value));
    return TV{r, full};
  }

  // --- atomics (ADR 0052) ----------------------------------------------

  static bool isAtomicBuiltin(const std::string &name) {
    static const std::set<std::string> names = {
        "atomic_new", "atomic_load", "atomic_store", "atomic_swap",
        "atomic_cas", "atomic_add",  "atomic_sub",   "atomic_and",
        "atomic_or",  "atomic_xor",  "atomic_min",   "atomic_max",
        "fence",
    };
    return names.count(name) != 0;
  }

  static const char *orderName(MemoryOrder o) {
    switch (o) {
    case MemoryOrder::relaxed:
      return "relaxed";
    case MemoryOrder::acquire:
      return "acquire";
    case MemoryOrder::release:
      return "release";
    case MemoryOrder::acq_rel:
      return "acq_rel";
    case MemoryOrder::seq_cst:
      return "seq_cst";
    }
    return "?";
  }

  // "relaxed, acquire or seq_cst".
  static std::string orderList(llvm::ArrayRef<MemoryOrder> orders) {
    std::string out;
    for (size_t i = 0; i < orders.size(); ++i) {
      if (i)
        out += i + 1 == orders.size() ? " or " : ", ";
      out += orderName(orders[i]);
    }
    return out;
  }

  // The order written at `n`, which must be one of the five constants by
  // name: an order is fixed when the program is compiled, so it can never
  // be a run-time value that a compiler would have to treat as `seq_cst`.
  // The name is read here alone, so it means the order even where a
  // function of the same name exists (ADR 0052, section 2).
  std::optional<MemoryOrder> orderOf(const Node &n, const std::string &op,
                                     llvm::ArrayRef<MemoryOrder> allowed,
                                     const char *which = "") {
    std::optional<MemoryOrder> o;
    if (n.kind == NodeKind::Name)
      o = symbolizeMemoryOrder(n.text);
    if (!o) {
      fail(n, "the " + std::string(which) + "order of '" + op +
                  "' must be one of the constants " + orderList(allowed) +
                  ", written in place: an order is fixed when the program "
                  "is compiled");
      return std::nullopt;
    }
    if (!llvm::is_contained(allowed, *o)) {
      fail(n, "'" + op + "' takes the " + std::string(which) + "order " +
                  orderList(allowed) + ", not " + orderName(*o) +
                  " (ADR 0052, section 2)");
      return std::nullopt;
    }
    return o;
  }

  // A cell of a range type narrower than its machine integer, such as
  // `atomic int{0..64}`, is refined: the range is an invariant of the cell
  // across every task, proved one store at a time (ADR 0052, section 3).
  static bool refinedCell(AtomicType cell) {
    auto t = mlir::dyn_cast<IntType>(cell.getElementType());
    if (!t)
      return false;
    unsigned w = t.getStorageWidth();
    llvm::APInt lo = t.getLo().sextOrTrunc(kWidth);
    llvm::APInt hi = t.getHi().sextOrTrunc(kWidth);
    if (lo.isZero() && hi == llvm::APInt::getMaxValue(w).zext(kWidth))
      return false;
    return !(lo == llvm::APInt::getSignedMinValue(w).sext(kWidth) &&
             hi == llvm::APInt::getSignedMaxValue(w).sext(kWidth));
  }

  // The cell an atomic op names. Naming it only borrows it.
  std::optional<std::pair<Value, AtomicType>> genCell(const Node &n,
                                                      const std::string &op) {
    R c = genExpr(n, Type());
    if (!c)
      return std::nullopt;
    unconsume(n);
    auto cell = mlir::dyn_cast<AtomicType>(c->type);
    if (!cell) {
      fail(n, "'" + op + "' needs an atomic cell, found " + typeName(c->type));
      return std::nullopt;
    }
    return std::make_pair(c->value, cell);
  }

  // A value to store in `cell`, or to combine with what it holds: it must
  // be of the cell's type, so a refined cell's range is a goal here.
  std::optional<Value> genCellValue(const Node &n, AtomicType cell) {
    Type elem = cell.getElementType();
    R v = genExpr(n, elem);
    if (!v)
      return std::nullopt;
    R cv = coerce(*v, elem, n);
    if (!cv)
      return std::nullopt;
    return cv->value;
  }

  // `atomic_new v`, `atomic_load o c`, `atomic_store o c v`, `atomic_swap o
  // c v`, `atomic_cas ok fail c expected desired`, the read-modify-writes
  // and `fence o` (ADR 0052, section 2). `mode` is the overflow mode stated
  // on this very expression, as in `@wrap (atomic_add o c v)`.
  R genAtomic(const Node &n, const std::string &name, Type expected,
              std::optional<OverflowMode> mode) {
    if (contract_ || ghost_)
      return fail(n, "'" + name +
                         "' is not allowed in a contract or ghost "
                         "code: what another task may write is not a value a "
                         "specification can name (ADR 0052, section 3)");
    using O = MemoryOrder;
    const O all[] = {O::relaxed, O::acquire, O::release, O::acq_rel,
                     O::seq_cst};
    size_t argc = n.kids.size() - 1;
    auto arity = [&](size_t k, const char *form) -> bool {
      if (argc == k)
        return true;
      fail(n, "'" + name + "' takes " + std::to_string(k) + " argument" +
                  (k == 1 ? "" : "s") + ", as in '" + form + "'");
      return false;
    };
    Location l = loc(n);
    if (name == "fence") {
      if (!arity(1, "fence seq_cst"))
        return std::nullopt;
      auto o = orderOf(*n.kids[1], name,
                       {O::acquire, O::release, O::acq_rel, O::seq_cst});
      if (!o)
        return std::nullopt;
      create<FenceOp>(l, *o);
      return unit();
    }
    if (name == "atomic_new") {
      if (!arity(1, "atomic_new 0"))
        return std::nullopt;
      auto want = mlir::dyn_cast_or_null<AtomicType>(expected);
      R v = genExpr(*n.kids[1], want ? want.getElementType() : Type());
      if (!v)
        return v;
      if (want) {
        v = coerce(*v, want.getElementType(), *n.kids[1]);
        if (!v)
          return v;
      }
      if (!mlir::isa<IntType>(v->type) && !isBool(v->type))
        return fail(*n.kids[1], "an atomic cell holds an integer or bool, "
                                "not " +
                                    typeName(v->type));
      auto cell = want ? want : AtomicType::get(&ctx_, v->type);
      return TV{create<AtomicNewOp>(l, cell, v->value).getResult(), cell};
    }
    if (name == "atomic_load") {
      if (!arity(2, "atomic_load acquire c"))
        return std::nullopt;
      auto o = orderOf(*n.kids[1], name, {O::relaxed, O::acquire, O::seq_cst});
      if (!o)
        return std::nullopt;
      auto c = genCell(*n.kids[2], name);
      if (!c)
        return std::nullopt;
      Type elem = c->second.getElementType();
      return TV{create<AtomicLoadOp>(l, elem, *o, c->first).getResult(), elem};
    }
    if (name == "atomic_store") {
      if (!arity(3, "atomic_store release c v"))
        return std::nullopt;
      auto o = orderOf(*n.kids[1], name, {O::relaxed, O::release, O::seq_cst});
      if (!o)
        return std::nullopt;
      auto c = genCell(*n.kids[2], name);
      if (!c)
        return std::nullopt;
      auto v = genCellValue(*n.kids[3], c->second);
      if (!v)
        return std::nullopt;
      create<AtomicStoreOp>(l, *o, *v, c->first);
      return unit();
    }
    if (name == "atomic_cas") {
      if (!arity(5, "atomic_cas acq_rel acquire c expected desired"))
        return std::nullopt;
      auto ok = orderOf(*n.kids[1], name, all, "success ");
      if (!ok)
        return std::nullopt;
      // The failure order only reads, and it may not be stronger than the
      // success order, so the cases C leaves undefined cannot be written.
      llvm::SmallVector<O> fails = {O::relaxed};
      if (*ok == O::acquire || *ok == O::acq_rel || *ok == O::seq_cst)
        fails.push_back(O::acquire);
      if (*ok == O::seq_cst)
        fails.push_back(O::seq_cst);
      auto bad = orderOf(*n.kids[2], name, fails, "failure ");
      if (!bad)
        return std::nullopt;
      auto c = genCell(*n.kids[3], name);
      if (!c)
        return std::nullopt;
      auto e = genCellValue(*n.kids[4], c->second);
      if (!e)
        return std::nullopt;
      auto d = genCellValue(*n.kids[5], c->second);
      if (!d)
        return std::nullopt;
      Type elem = c->second.getElementType();
      Value old = create<AtomicCasOp>(l, elem, *ok, *bad, c->first, *e, *d);
      return TV{old, elem};
    }
    return genAtomicRmw(n, name, mode);
  }

  R genAtomicRmw(const Node &n, const std::string &name,
                 std::optional<OverflowMode> mode) {
    static const std::map<std::string, RmwKind> kinds = {
        {"atomic_swap", RmwKind::swap}, {"atomic_add", RmwKind::add},
        {"atomic_sub", RmwKind::sub},   {"atomic_and", RmwKind::band},
        {"atomic_or", RmwKind::bor},    {"atomic_xor", RmwKind::bxor},
        {"atomic_min", RmwKind::min},   {"atomic_max", RmwKind::max},
    };
    RmwKind kind = kinds.at(name);
    if (n.kids.size() != 4)
      return fail(n, "'" + name + "' takes 3 arguments, as in '" + name +
                         " acq_rel c v'");
    using O = MemoryOrder;
    auto o =
        orderOf(*n.kids[1], name,
                {O::relaxed, O::acquire, O::release, O::acq_rel, O::seq_cst});
    if (!o)
      return std::nullopt;
    auto c = genCell(*n.kids[2], name);
    if (!c)
      return std::nullopt;
    AtomicType cell = c->second;
    Type elem = cell.getElementType();
    bool refined = refinedCell(cell);
    bool arith = kind == RmwKind::add || kind == RmwKind::sub;
    bool bitwise =
        kind == RmwKind::band || kind == RmwKind::bor || kind == RmwKind::bxor;
    if (isBool(elem) && (arith || kind == RmwKind::min || kind == RmwKind::max))
      return fail(n, "'" + name + "' needs a cell of an integer type, found " +
                         typeName(cell));
    // Nothing is known of the result of a bitwise op on a value that any
    // task may have left there, so none can be proved to meet a range.
    if (refined && bitwise)
      return fail(n, "'" + name + "' is not allowed on the refined cell " +
                         typeName(cell) +
                         ", since its result cannot be "
                         "proved to stay in the range; use a compare-and-"
                         "swap loop that checks the new value (ADR 0052, "
                         "section 3)");
    OverflowMode overflow = OverflowMode::proof;
    if (arith) {
      // An atomic add states its own overflow handling, never the
      // function's: nothing is assumed of what the hardware does.
      if (!mode)
        return fail(n, "'" + name +
                           "' must state its overflow mode on the "
                           "expression itself, as in '@wrap (" +
                           name +
                           " o c v)', or '@trap', '@saturate' or '@proof'; "
                           "an enclosing @overflow(...) does not apply "
                           "(ADR 0052, section 2)");
      overflow = *mode;
      if (refined && overflow != OverflowMode::proof)
        return fail(n, "'" + name + "' on the refined cell " + typeName(cell) +
                           " must be '@proof', with a goal "
                           "that the result stays in the range for every "
                           "value the cell may hold (ADR 0052, section 3)");
      if (!refined && overflow == OverflowMode::proof)
        return fail(n, "'@proof' on '" + name +
                           "' needs a refined cell, "
                           "such as 'atomic int{0..64}': another task may "
                           "have left any value of " +
                           typeName(elem) +
                           " in this one, so the result cannot be proved "
                           "to fit");
    }
    auto v = genCellValue(*n.kids[3], cell);
    if (!v)
      return std::nullopt;
    Location l = loc(n);
    Value old = create<AtomicRmwOp>(l, elem, kind, *o, c->first, *v, overflow);
    // The goal of `@proof`: from any value the range allows, the result
    // stays in it. `old` is such a value, and nothing else is known of it.
    // The sum itself is only checked; codegen drops it.
    if (arith && overflow == OverflowMode::proof) {
      auto pm = OverflowModeAttr::get(&ctx_, OverflowMode::proof);
      if (kind == RmwKind::add)
        create<AddOp>(l, elem, old, *v, pm);
      else
        create<SubOp>(l, elem, old, *v, pm);
    }
    return TV{old, elem};
  }

  // `@wrap e`, `@trap e`, `@saturate e`, `@proof e`: `e` under that
  // overflow mode (docs/design.md). The parser writes it `#overflow m e`.
  R genModeExpr(const Node &n, Type expected) {
    auto m = symbolizeOverflowMode(n.kids[1]->text);
    if (!m)
      return fail(*n.kids[1], "unknown overflow mode");
    OverflowMode saved = overflow_;
    const Node *savedNode = statedNode_;
    std::optional<OverflowMode> savedMode = statedMode_;
    overflow_ = *m;
    statedNode_ = n.kids[2].get();
    statedMode_ = *m;
    R r = genExpr(*n.kids[2], expected);
    overflow_ = saved;
    statedNode_ = savedNode;
    statedMode_ = savedMode;
    return r;
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

  // The integer type that `a`, the argument of `min a` or `max a`, names,
  // or null if it names no integer type: a value, a function or nothing.
  // A name as written, or one a quote made. A quote's names carry
  // "toplevel" or "prelude" and never resolve to a local at the expansion
  // site (docs/meta.md, "Hygiene"), so only a written name can be one.
  bool boundName(const Node &n) {
    if (n.kind != NodeKind::Name)
      return false;
    if (n.flags.empty())
      return !lookup(n.text);
    return n.flags == "toplevel" || n.flags == "prelude";
  }

  Type boundOperandType(const Node &a) {
    if (!boundName(a) || !overloadSet(a.text).empty())
      return {};
    auto name = syntax::makeNode(NodeKind::TypeName, a.loc, a.text);
    size_t errors = diags_.count();
    Type t = types_.resolve(*name);
    diags_.truncate(errors);
    return t;
  }

  // `min t` and `max t`: the bounds of the integer type `t` (ADR 0059).
  // They overload Pia.Core.Order's `min a b` and `max a b` by their one
  // argument being a type, so they are folded here, before overload
  // resolution sees a type where it expects a value. The result is the
  // bound as a literal, which takes its context's type like any literal,
  // so `ensures a * b > max u16 ==> ...` reads exactly as the number did.
  // Each bound comes from the type as Sema resolved it, so `max usize`
  // follows the pointer width that the target's model gives usize.
  std::optional<R> genTypeBound(const Node &n, Type expected) {
    if (n.kids.size() != 2)
      return std::nullopt;
    const Node &f = *n.kids[0];
    if (!boundName(f) || (f.text != "min" && f.text != "max"))
      return std::nullopt;
    const Node &a = *n.kids[1];
    Type t = boundOperandType(a);
    if (!t)
      return std::nullopt;
    auto it = mlir::dyn_cast<IntType>(t);
    if (!it)
      return fail(a, "'" + f.text + " " + a.text +
                         "' needs an integer type, "
                         "and '" +
                         a.text + "' is not one");
    llvm::APInt bound = f.text == "min" ? it.getLo() : it.getHi();
    bool negative = bound.isNegative();
    llvm::APInt magnitude = negative ? -bound : bound;
    auto lit = syntax::makeNode(NodeKind::IntLit, n.loc,
                                llvm::toString(magnitude, 10, false));
    if (!negative)
      return genExpr(*keep(std::move(lit)), expected);
    auto neg = syntax::makeNode(NodeKind::Neg, n.loc);
    neg->add(std::move(lit));
    return genExpr(*keep(std::move(neg)), expected);
  }

  R genApply(const Node &n, Type expected) {
    if (n.flags == "drop") return genDrop(n);
    if (n.flags == "region") return genRegion(n, expected);
    if (std::optional<R> b = genTypeBound(n, expected))
      return *b;
    if (const Node &f = *n.kids[0]; f.kind == NodeKind::Name &&
                                     f.flags.empty() && !lookup(f.text) &&
                                     overloadSet(f.text).empty()) {
      if (f.text == "unsafe") return genUnsafe(n, expected);
      if (f.text == "with_arena")
        return fail(n, "'with_arena' takes the arena's size in bytes, an "
                       "integer literal, and a function of the arena, as "
                       "in 'with_arena 256 (let (a) => use a)'");
      if (f.text == "extern")
        return fail(n, "'extern \"symbol\"' is only a function's whole body, "
                       "as in 'let f (x : i32) : i32 ensures true = extern "
                       "\"f\"'");
    }
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
    // `g x` for a function object `g` is `apply g x` (ADR 0044, section 4).
    if (local && !targs)
      if (BindingPtr g = lookup(fn.text);
          mlir::isa<RecordType>(g->type) && !overloadSet("apply").empty()) {
        auto call = syntax::makeNode(NodeKind::Apply, n.loc);
        call->add(syntax::makeNode(NodeKind::Name, fn.loc, "apply"));
        for (const NodePtr &k : n.kids) call->add(syntax::clone(*k));
        return genApply(*keep(std::move(call)), expected);
      }
    if (!local && fn.flags != "prelude")
      // In code from another module, its higher-order functions by their
      // own names, as its other functions are found (ADR 0039, section 6;
      // #257).
      if (auto h = findHof(fn.text); h != hofs_.end()) {
        std::vector<const Node *> args;
        for (size_t i = 1; i < n.kids.size(); ++i)
          args.push_back(n.kids[i].get());
        return genMixedCall(n, fn.text, h->second, targs, args, expected);
      }
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
        // `add 1`, with arguments left, is a function of the rest.
        if (args.size() < sig.params.size() && !args.empty() && !contract_ &&
            !ghost_)
          if (const Node *lam = partialLambda(n, sig))
            return genExpr(*lam, expected);
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
    if (fn.flags == "prelude" && fn.text == "#overflow" && argc == 2)
      return genModeExpr(n, expected);
    if (!local && isAtomicBuiltin(fn.text))
      return genAtomic(n, fn.text, expected,
                       statedNode_ == &n ? statedMode_ : std::nullopt);
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
      if (fn.text == "clz" || fn.text == "ctz" || fn.text == "popcount" ||
          fn.text == "bswap" || fn.text == "rotl" || fn.text == "rotr")
        return genBitBuiltin(n, fn.text);
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
        unconsume(*n.kids[1]);
        if (!mlir::isa<ArrayType, SliceType>(buf->type))
          return fail(*n.kids[1], "'len' needs an array or slice, found " +
                                      typeName(buf->type));
        Value i = create<LenOp>(l, b_.getIndexType(), buf->value);
        Type usize = types_.usize();
        return TV{create<FromIndexOp>(l, usize, i), usize};
      }
      if (fn.text == "old") {
        // A lemma's arguments are spec too: `occurrences_swapped (old xs)
        // xs i j` relates the state on entry to this one.
        if (!contract_ && !ghost_)
          return fail(n, "'old' is only allowed in contracts and in a "
                         "lemma's arguments");
        if (argc != 1) return fail(n, "'old' takes one argument");
        // `old` reads the parameters as they were on entry. A buffer is
        // the same value throughout; the verifier reads its entry memory.
        std::vector<std::pair<BindingPtr, Value>> saved;
        for (auto &scope : scopes_)
          for (auto &[name, b] : scope)
            if (b->isParam && b->entry && b->value != b->entry &&
                !mlir::isa<ArrayType, SliceType>(b->type)) {
              saved.push_back({b, b->value});
              b->value = b->entry;
            }
        R v = genExpr(*n.kids[1], Type());
        for (auto &[b, value] : saved) b->value = value;
        if (!v) return v;
        return TV{create<contract::OldOp>(l, v->type, v->value), v->type};
      }
    }
    return fail(fn, "'" + fn.text + "' is not a function");
  }

  R genCall(const Node &n, const sema::FuncSig &sig,
            const std::vector<const Node *> &args,
            const std::vector<std::optional<TV>> *early = nullptr) {
    // A requirement a box over a concept cannot forward (ADR 0046).
    if (sig.item)
      if (std::string why = boxUncallable(*sig.item); !why.empty())
        return fail(n, why);
    if (args.size() == sig.params.size() &&
        !(sig.item && hasFlag(*sig.item, "lemma")) &&
        !checkFootprintCall(n, sig, args))
      return std::nullopt;
    if (args.size() != sig.params.size())
      return fail(n, "'" + sig.name + "' takes " +
                         plural(sig.params.size(), "argument") + ", given " +
                         std::to_string(args.size()) +
                         "; partial application is not supported yet");
    // `: u8 -> u8`: the closure the body makes, inferred first.
    if (!sig.result && sig.arrowResult)
      if (auto it = sigs_.find(sig.name); it != sigs_.end() && &it->second == &sig)
        inferResult(it->second, *sig.item);
    if (!sig.result)
      return fail(n, "'" + sig.name + "' is used before its return type is "
                     "known; annotate it, as in 'let " + sig.name +
                     " ... : T = ...'");
    if (sig.item && hasFlag(*sig.item, "spec") && !contract_ && !ghost_ &&
        !isTargetValue(sig))
      return fail(n, "'" + sig.name + "' is a spec function, so it can be "
                     "used only in contracts, spec functions and lemmas");
    if (effectful_.count(sig.name) && (contract_ || ghost_))
      return fail(n, "this lambda writes a captured variable, so it cannot "
                     "be called in a contract (ADR 0044, section 6)");
    if (sig.item && hasFlag(*sig.item, "lemma") && contract_)
      return fail(n, "'" + sig.name + "' is a lemma: call it as a statement, "
                     "and its postcondition holds after the call");
    {
      std::string symbol;
      bool foreign = sig.item && sig.item->kids.size() > 3 &&
                     externSymbol(*sig.item->kids[3], symbol);
      bool contracted = false;
      if (foreign)
        for (const syntax::NodePtr &c : sig.item->kids[2]->kids)
          contracted |= c->kind == NodeKind::Requires ||
                        c->kind == NodeKind::Ensures;
      bool isUnsafe = unsafeAt_ == &n;
      if (foreign && !contracted && !isUnsafe)
        return fail(n, "'" + sig.name + "' is a foreign function without a "
                       "contract, so only 'unsafe " + sig.name + " ...' can "
                       "call it; or give its declaration a 'requires' or "
                       "'ensures', even 'ensures true'");
      if (isUnsafe && !(foreign && !contracted))
        return fail(n, "'unsafe' marks a call of a foreign function without "
                       "a contract, and '" + sig.name + "' is not one; "
                       "call it without 'unsafe'");
    }
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
      // A spec parameter's argument is specification (ADR 0058). One the
      // callee may write must be spec state itself, since codegen erases
      // the write: a code buffer would not change at run time.
      bool specArg = sig.params[i].spec && !contract_ && !ghost_;
      if (specArg && writes(sig.params[i])) {
        BindingPtr sb = args[i]->kind == NodeKind::Name &&
                                args[i]->flags.empty()
                            ? lookup(args[i]->text)
                            : nullptr;
        if (!sb || !sb->spec)
          return fail(*args[i], "'" + sig.params[i].name + "' of '" +
                                    sig.name + "' is a spec parameter that "
                                    "it may write, so pass a spec local or "
                                    "spec parameter by name (ADR 0058)");
      }
      if (specArg) contract_ = true;
      R a = early && (*early)[i] ? (*early)[i]
                                 : genExpr(*args[i], sig.params[i].type);
      if (specArg) contract_ = false;
      if (!a) return a;
      R c = coerce(*a, sig.params[i].type, *args[i]);
      if (!c) return c;
      if (writes(sig.params[i]) && isConstantData(c->value))
        return fail(*args[i], "constant data cannot be passed to '" +
                                  sig.params[i].name + "', which is 'out' or "
                                  "'inout'");
      if (!sema::hasModifier(sig.params[i].modifiers, "moved"))
        unconsume(*args[i]);
      else if (!moveArgument(*args[i], c->type, sig, sig.params[i]))
        return std::nullopt;
      // `inout` may update a lender, as `alloc` updates its allocator:
      // what the callee's contract promises keeps the loans valid. `out`
      // makes it anew, which would end them.
      if (sema::hasModifier(sig.params[i].modifiers, "out") &&
          args[i]->kind == NodeKind::Name && args[i]->flags.empty())
        if (BindingPtr b = lookup(args[i]->text))
          if (!notLent(b, *args[i], "passed to '" + sig.params[i].name +
                                        "', which makes it anew,"))
            return std::nullopt;
      operands.push_back(c->value);
    }
    Lenders lenders;
    // A result that mentions a region borrows what the arguments for that
    // region's parameters borrow, not the arguments themselves: so `alloc
    // v.alloc n` does not lend `v` to the buffer it stores in `v`.
    if (!sig.resultRegions.empty() && !contract_ && !ghost_) {
      if (sig.lentType) lentTypes_.insert(sig.lentType.getAsOpaquePointer());
      addLenders(lenders, regionLenders(sig, sig.resultRegions, args));
    }
    if (!sig.resultLender.empty() && !contract_ && !ghost_) {
      if (sig.lentType) lentTypes_.insert(sig.lentType.getAsOpaquePointer());
      size_t i = 0;
      while (sig.params[i].name != sig.resultLender) ++i;
      const Node &a = *args[i];
      lenders = lendersOf(a);
      BindingPtr b = a.kind == NodeKind::Name && a.flags.empty()
                         ? lookup(a.text)
                         : nullptr;
      if (b)
        addLenders(lenders, {b});
      else if (lenders.empty())
        return fail(a, "the result of '" + sig.name + "' is borrowed from '" +
                           sig.params[i].name + "', so this argument must "
                           "be a named value, whose scope the borrow can "
                           "end in; bind it with 'let' first");
    }
    // Each `out` or `inout` argument gets the callee's new value: a mutable
    // variable, or a field of one, as in `take g.small`, which rebuilds `g`
    // with that field replaced.
    struct Rebind {
      BindingPtr b;
      std::vector<std::string> path;  // fields from `b`, outermost first
    };
    std::vector<Rebind> rebind;
    for (size_t i : threaded(sig)) {
      const Node &a = *args[i];
      std::vector<std::string> path;
      const Node *root = &a;
      while (root->kind == NodeKind::Field && !root->kids.empty()) {
        path.insert(path.begin(), root->text);
        root = root->kids[0].get();
      }
      BindingPtr b = root->kind == NodeKind::Name && root->flags.empty()
                         ? lookup(root->text)
                         : nullptr;
      if (contract_ || ghost_) {
        rebind.push_back({nullptr, {}});
        continue;
      }
      if (b && b->isMutable && !path.empty() &&
          !notLent(b, *root, "given a new field"))
        return std::nullopt;
      if (!b || !b->isMutable)
        return fail(a, "'" + sig.params[i].name + "' of '" + sig.name +
                           "' is '" + (sema::hasModifier(sig.params[i].modifiers,
                                                         "out") ? "out" : "inout") +
                           "', so the call gives it a new value: pass a "
                           "mutable variable, as in 'let x : mutable " +
                           typeName(sig.params[i].type) + " = ...'");
      rebind.push_back({b, std::move(path)});
    }
    // In a definition check, a requirement's precondition is a goal at
    // each call, which its uninterpreted function cannot raise itself
    // (ADR 0044: an arrow with `requires` proved once).
    if (checking_ && !contract_ && !ghost_ && sig.item &&
        sig.item->kind == NodeKind::SigVal &&
        std::any_of(promisedSigs_.begin(), promisedSigs_.end(),
                    [&](const sema::FuncSig &r) { return &r == &sig; })) {
      pushScope();
      for (size_t i = 0; i < sig.params.size() && i < operands.size(); ++i)
        bind(sig.params[i].name, operands[i], sig.params[i].type, false);
      for (const syntax::NodePtr &c : sig.item->kids[2]->kids) {
        if (c->kind != NodeKind::Requires) continue;
        R p = genPredicate(*c->kids[0]);
        if (!p) {
          popScope();
          return std::nullopt;
        }
        create<contract::AssertOp>(loc(n), p->value);
      }
      popScope();
    }
    R out = emitCall(n, sig, operands);
    if (out)
      for (size_t k = 0; k < rebind.size(); ++k) {
        BindingPtr b = rebind[k].b;
        if (!b) continue;
        b->value = withField(loc(n), b->value, rebind[k].path, 0,
                             threadedResults_[k]);
        // A closure's referenced captures see what the call wrote.
        if (rebind[k].path.empty())
          if (auto rt = mlir::dyn_cast<RecordType>(b->type))
            for (auto &[field, target] : b->refs)
              if (std::optional<unsigned> i = rt.fieldIndex(field))
                target->value = create<FieldOp>(loc(n), rt.getFieldTypes()[*i],
                                                b->value, field)
                                    .getResult();
      }
    // `(v : borrowed(m) inout mutable vec)`: the new value may hold a loan
    // from the argument passed as `m`, as `push m v x` stores a buffer from
    // `m` in `v`.
    if (out && !contract_ && !ghost_) {
      std::vector<size_t> through = threaded(sig);
      for (size_t k = 0; k < through.size(); ++k) {
        const sema::Param &p = sig.params[through[k]];
        if (!p.regions.empty() && rebind[k].b)
          addLenders(rebind[k].b->lenders, regionLenders(sig, p.regions, args));
        if (p.lender.empty() || !rebind[k].b) continue;
        size_t i = 0;
        while (sig.params[i].name != p.lender) ++i;
        Lenders from = lendersOf(*args[i]);
        if (args[i]->kind == NodeKind::Name && args[i]->flags.empty())
          if (BindingPtr x = lookup(args[i]->text)) addLenders(from, {x});
        if (from.empty())
          return fail(*args[i], "'" + p.name + "' of '" + sig.name +
                                    "' may borrow from '" + p.lender +
                                    "', so this argument must be a named "
                                    "value; bind it with 'let' first");
        addLenders(rebind[k].b->lenders, from);
      }
    }
    // Recorded even when empty: a call's result borrows only what its
    // result type says.
    if (out) lent_[&n] = std::move(lenders);
    if (out && (!sig.resultLender.empty() || sig.lentFromRegion) &&
        (sema::hasModifier(sig.lentModifiers, "out") ||
         sema::hasModifier(sig.lentModifiers, "inout") ||
         sema::hasModifier(sig.lentModifiers, "mutable")))
      writable_.insert(&n);
    return out;
  }

  // A call of a generic function: the type arguments come from `targs`
  // (`f<u8, t = u16>`), then from the arguments whose written types mention
  // a type parameter, then from the type the call is expected to have. The
  // call goes to the instance for those arguments, `f<u8>`, which is made
  // on first use and generated after the current function.
  R genGenericCall(const Node &n, const sema::FuncSig &generic,
                   const Node *targs, const std::vector<const Node *> &args,
                   Type expected,
                   const std::map<std::string, Type> *preBound = nullptr) {
    const std::vector<std::string> &params = generic.typeParams;
    std::map<std::string, Type> bound;
    std::map<std::string, std::string> named;
    // A lemma's arguments are spec, including those generated early to
    // deduce its type arguments.
    struct GhostScope {
      bool &flag, value;
      ~GhostScope() { flag = value; }
    } ghostScope{ghost_, ghost_};
    if (generic.item && hasFlag(*generic.item, "lemma")) ghost_ = true;
    if (!bindTypeArgs(generic, targs, bound, &named)) return std::nullopt;
    // What a higher-order call deduced from its function arguments.
    if (preBound)
      for (auto &[t, type] : *preBound) bound.emplace(t, type);

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
    // `widen`, which boxes a value as a concept (ADR 0046, section 3): the
    // box would hide a @linear value's obligation to be released, and
    // could outlive what a borrowing value lends from.
    if (generic.item && hasFlag(*generic.item, "box_widen"))
      if (auto t = bound.find("t"); t != bound.end()) {
        if (isLinear(t->second))
          return fail(n, "a value of the @linear type " + typeName(t->second) +
                             " cannot be boxed as a concept: the box would "
                             "hide the obligation to release it (ADR 0046)");
        if (holdsRegionField(t->second))
          return fail(n, "a value of " + typeName(t->second) + " borrows, "
                             "and cannot be boxed as a concept: the box "
                             "could outlive its lender (ADR 0046)");
      }
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

  // --- function values (ADR 0044, step 1) ----------------------------
  //
  // A higher-order function, one with parameters of function type, is
  // never lowered itself. Each call that passes a lambda or a top-level
  // function for those parameters goes to a specialisation: a copy of the
  // function without them, in which each one's name is the symbol of a
  // function made from the argument. The copy keeps the type parameters,
  // so a generic one is then called like any generic. A lambda becomes a
  // private top-level function, `lambda@file.pia:12:9`, whose body the
  // verifier knows wherever it is called, as for any pure function.

  struct Capture {
    std::string name;
    BindingPtr binding;
    // "" copied, "borrowed" a shared loan, "inout" an exclusive one
    // (ADR 0044, section 6).
    std::string mode;
  };
  using Captures = std::vector<Capture>;

  // A function type as written: its parameters, its result, and the
  // contracts on its innermost arrow.
  struct Arrow {
    std::vector<const Node *> domains;  // Domain: modifiers, type, where?
    const Node *result = nullptr;
    const Node *contracts = nullptr;  // Contracts, or null
  };
  static Arrow arrowOf(const Node &type) {
    Arrow a;
    const Node *cur = &type;
    for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
      a.domains.push_back(cur->kids[0].get());
      if (cur->kids.size() > 2) a.contracts = cur->kids[2].get();
    }
    a.result = cur;
    return a;
  }

  std::string placeOf(const Node &n) const {
    return llvm::sys::path::filename(file_.getValue()).str() + ":" +
           std::to_string(n.loc.line) + ":" + std::to_string(n.loc.column);
  }

  static NodePtr annotOf(const Node &type, syntax::SourceLoc at) {
    if (type.kind == NodeKind::Annot) return syntax::clone(type);
    auto annot = syntax::makeNode(NodeKind::Annot, at);
    annot->add(syntax::makeNode(NodeKind::Modifiers, at));
    annot->add(syntax::clone(type));
    annot->add(syntax::makeNode(NodeKind::None, at));
    return annot;
  }

  static NodePtr retAnnotNode(NodePtr annot, syntax::SourceLoc at) {
    auto ret = syntax::makeNode(NodeKind::RetAnnot, at);
    ret->add(std::move(annot));
    ret->add(syntax::makeNode(NodeKind::Attrs, at));
    return ret;
  }

  static void relocateTree(Node &n, syntax::SourceLoc at) {
    n.loc = at;
    for (NodePtr &k : n.kids) relocateTree(*k, at);
  }

  // Adds the contracts of `arrow` of kind `kind` to `to`, with the
  // arrow's parameter names renamed. With `at`, they are placed there, so
  // that a failure points at the argument that does not meet them.
  static void arrowContracts(const Arrow &arrow, NodeKind kind,
                             const std::map<std::string, std::string> &rename,
                             Node &to,
                             std::optional<syntax::SourceLoc> at = std::nullopt) {
    if (!arrow.contracts) return;
    for (const NodePtr &c : arrow.contracts->kids) {
      if (c->kind != kind) continue;
      NodePtr copy = syntax::clone(*c);
      if (at) relocateTree(*copy, *at);
      renameNames(*copy, rename, nullptr);
      if (copy->kids[0]->kind == NodeKind::Name)
        if (auto it = rename.find(copy->kids[0]->text); it != rename.end())
          copy->kids[0]->text = it->second;
      to.add(std::move(copy));
    }
  }

  // Makes the function a lambda stands for, once per lambda, and returns
  // its symbol. `arrow` is the type it is passed as, or null when a `let`
  // binds it. Its precondition is the arrow's, its own `requires` are
  // asserted at the start of its body, so they must follow from the
  // arrow's, and its postconditions are its own and the arrow's.
  std::optional<std::string> liftLambda(const Node &lam, const Arrow *arrow,
                                        const std::vector<std::string> &typeParams,
                                        const std::string &what,
                                        const Captures *caps = nullptr,
                                        const std::map<std::string, Type> *bound = nullptr) {
    static const std::map<std::string, Type> none;
    if (!bound) bound = &none;
    std::string symbol = "lambda@" + placeOf(lam);
    // A lambda that captures is the `apply` of its closure type, whose
    // first parameter holds the captures (ADR 0044, section 6).
    std::string closureType = closureName_.empty() ? symbol : closureName_;
    if (caps) symbol = "apply[" + closureType + "]";
    if (sigs_.count(symbol)) return symbol;
    syntax::SourceLoc at = lam.loc;
    std::vector<const Node *> lparams;
    const Node *ret = nullptr, *contracts = nullptr;
    for (size_t i = 0; i + 1 < lam.kids.size(); ++i) {
      const Node &k = *lam.kids[i];
      if (k.kind == NodeKind::LParam) lparams.push_back(&k);
      else if (k.kind == NodeKind::RetAnnot) ret = &k;
      else if (k.kind == NodeKind::Contracts) contracts = &k;
    }
    if (arrow && lparams.size() != arrow->domains.size()) {
      fail(lam, "this lambda takes " + plural(lparams.size(), "parameter") +
                    ", but " + what + " takes " +
                    plural(arrow->domains.size(), "argument") +
                    "; partial application comes later (ADR 0044, step 7)");
      return std::nullopt;
    }
    auto item = syntax::makeNode(NodeKind::LetItem, at, caps ? "apply" : symbol);
    Node *params = item->add(syntax::makeNode(NodeKind::Params, at));
    if (caps) {
      Node *self = params->add(syntax::makeNode(NodeKind::Param, at, kSelf));
      self->add(annotOf(*syntax::makeNode(NodeKind::TypeName, at, closureType),
                        at));
      // A referenced capture is written through the closure, which the
      // call threads back to the caller.
      if (effectful(*caps)) {
        self->kids[0]->kids[0]->text = "inout mutable";
        effectful_.insert(symbol);
      }
    }
    std::map<std::string, std::string> rename;
    // A lambda bound by `let` with untyped parameters is generic: each
    // untyped parameter has an implicit type parameter (ADR 0044, section
    // 2). Explicit ones, `(t : type where Ord t)`, are kept as written.
    std::vector<std::string> generics;
    for (size_t i = 0; i < lparams.size(); ++i) {
      const Node &lp = *lparams[i];
      const Node &pat = *lp.kids[0];
      bool typed = lp.kids.size() > 1 && lp.kids[1]->kind == NodeKind::Annot;
      if (pat.kind != NodeKind::PVar) {
        fail(lp, "a lambda's parameter must be a name for now, as in "
                 "'let (x : u8) => x > 3'");
        return std::nullopt;
      }
      Node *p = params->add(syntax::makeNode(NodeKind::Param, lp.loc, pat.text));
      if (typed && lp.kids[1]->kids[1]->kind == NodeKind::TypeKind) {
        if (arrow || caps) {
          fail(lp, "a lambda with type parameters can only be bound by "
                   "'let' for now");
          return std::nullopt;
        }
        p->add(syntax::clone(*lp.kids[1]));
        generics.push_back(pat.text);
        continue;
      }
      if (typed) {
        p->add(syntax::clone(*lp.kids[1]));
      } else if (arrow) {
        // Its type comes from the parameter's type, with the type
        // parameters the other arguments bound.
        const Node &dom = *arrow->domains[i];
        if (mentionsUnbound(*dom.kids[1], typeParams, *bound)) {
          fail(lp, "cannot tell the type of '" + pat.text + "' from " + what +
                       "; give it, as in '(" + pat.text + " : u8)'");
          return std::nullopt;
        }
        Type t = resolveUnder(*dom.kids[1], *bound);
        if (!t) return std::nullopt;
        p->add(annotOf(*syntax::makeNode(
                           NodeKind::TypeName, lp.loc,
                           typeAlias(t, symbol + "#" + pat.text)),
                       lp.loc));
      } else if (caps) {
        fail(lp, "a lambda that captures needs its parameters' types for "
                 "now, as in 'let (x : u8) => x < lim'");
        return std::nullopt;
      } else {
        // An implicit type parameter, `x#type`.
        std::string t = pat.text + "#type";
        Node *tp = params->kids.insert(
                           params->kids.end() - 1,
                           syntax::makeNode(NodeKind::Param, lp.loc, t))
                       ->get();
        auto annot = syntax::makeNode(NodeKind::Annot, lp.loc);
        annot->add(syntax::makeNode(NodeKind::Modifiers, lp.loc));
        annot->add(syntax::makeNode(NodeKind::TypeKind, lp.loc));
        annot->add(syntax::makeNode(NodeKind::None, lp.loc));
        tp->add(std::move(annot));
        p = params->kids.back().get();
        p->add(annotOf(*syntax::makeNode(NodeKind::TypeName, lp.loc, t),
                       lp.loc));
        generics.push_back(t);
      }
      if (arrow && !arrow->domains[i]->text.empty())
        rename[arrow->domains[i]->text] = pat.text;
    }
    if (ret) {
      item->add(syntax::clone(*ret));
    } else if (arrow && !mentionsUnbound(*arrow->result, typeParams, *bound)) {
      Type t = resolveUnder(*arrow->result, *bound);
      if (!t) return std::nullopt;
      item->add(retAnnotNode(
          annotOf(*syntax::makeNode(NodeKind::TypeName, at,
                                    typeAlias(t, symbol + "#result")),
                  at),
          at));
    } else {
      // Inferred from the body, which is generated on its own first.
      item->add(syntax::makeNode(NodeKind::None, at));
    }
    Node *cs = item->add(syntax::makeNode(NodeKind::Contracts, at));
    if (arrow) arrowContracts(*arrow, NodeKind::Requires, rename, *cs);
    std::vector<const Node *> asserted;
    if (contracts)
      for (const NodePtr &c : contracts->kids) {
        if (c->kind == NodeKind::Requires) {
          asserted.push_back(c->kids[0].get());
        } else if (c->kind == NodeKind::Ensures) {
          cs->add(syntax::clone(*c));
        } else {
          fail(*c, "a lambda takes only 'requires' and 'ensures'; a "
                   "recursive helper is a named 'let rec'");
          return std::nullopt;
        }
      }
    if (arrow) arrowContracts(*arrow, NodeKind::Ensures, rename, *cs, at);
    // The lambda's own preconditions hold wherever the arrow's do.
    NodePtr body = syntax::clone(*lam.kids.back());
    for (auto r = asserted.rbegin(); r != asserted.rend(); ++r) {
      auto check = syntax::makeNode(NodeKind::Assert, (*r)->loc);
      check->add(syntax::clone(**r));
      auto seq = syntax::makeNode(NodeKind::Sequence, (*r)->loc);
      seq->add(std::move(check));
      seq->add(std::move(body));
      body = std::move(seq);
    }
    item->add(std::move(body));
    // A capture is a field of the closure.
    if (caps)
      for (size_t k = 2; k < item->kids.size(); ++k)
        throughSelf(item->kids[k], *caps);
    sema::FuncSig sig;
    sig.name = symbol;
    sig.item = item.get();
    sig.typeParams = generics;
    synthesized_.push_back(std::move(item));
    if (!generics.empty()) {
      // Instantiated at each use. A constrained one is proved once, over
      // its type parameters (ADR 0043).
      bool constrained = false;
      for (const NodePtr &q : sig.item->kids[0]->kids)
        constrained |= sema::isTypeParam(*q) &&
                       q->kids[0]->kids[2]->kind != NodeKind::None;
      sigs_.emplace(symbol, std::move(sig));
      overloads_[symbol].push_back(symbol);
      if (constrained) pendingInstances_.push_back(kDefinition + symbol);
      return symbol;
    }
    if (!sema::resolveSignature(sig, types_, diags_)) return std::nullopt;
    if (!sig.result && !inferResult(sig, lam)) return std::nullopt;
    sigs_.emplace(symbol, std::move(sig));
    overloads_[caps ? "apply" : symbol].push_back(symbol);
    pendingInstances_.push_back(symbol);
    return symbol;
  }

  // A pending entry that checks a generic's definition, not an instance.
  static constexpr const char *kDefinition = "#definition ";

  // A written type with type parameters bound.
  Type resolveUnder(const Node &type, const std::map<std::string, Type> &bound) {
    if (!bound.empty()) types_.pushTypeScope(bound);
    Type t = type.kind == NodeKind::Annot ? types_.resolveAnnot(type)
                                          : types_.resolve(type);
    if (!bound.empty()) types_.popTypeScope();
    return t;
  }

  // How a synthesized item writes the type `t` of a function object: its
  // name, or for a type parameter's stand-in in a definition check, an
  // alias of it (ADR 0044, step 6). Empty when there is neither.
  std::string writtenName(Type t) {
    std::string name = typeName(t);
    if (types_.named(name) == t) return name;
    if (standIns_.contains(t)) return typeAlias(t, "standin#" + name);
    return "";
  }

  // A name for a type, so a synthesized item can write it.
  std::string typeAlias(Type t, const std::string &name) {
    std::string alias = "type#" + name;
    types_.define(alias, t);
    return alias;
  }

  // The result type of a lambda's function that does not write one: its
  // body is generated once on its own, in a function thrown away after,
  // and its type is the result. Errors there come again when the function
  // is generated, so they are dropped.
  bool inferResult(sema::FuncSig &sig, const Node &at) {
    OpBuilder::InsertionGuard guard(b_);
    b_.setInsertionPointToEnd(module_.getBody());
    llvm::SmallVector<Type> argTypes;
    for (const sema::Param &p : sig.params) argTypes.push_back(p.type);
    auto tmp = create<mlir::func::FuncOp>(loc(at), "#infer",
                                          b_.getFunctionType(argTypes, {}));
    Block *entry = tmp.addEntryBlock();
    b_.setInsertionPointToStart(entry);
    auto savedScopes = std::move(scopes_);
    scopes_.clear();
    auto savedFrames = std::move(frames_);
    frames_.clear();
    frames_.emplace_back();
    auto savedMoved = std::move(moved_);
    moved_.clear();
    unsigned savedDepth = loopDepth_;
    loopDepth_ = 0;
    bool savedContract = contract_, savedGhost = ghost_;
    contract_ = false;
    ghost_ = false;
    std::vector<std::map<std::string, Type>> savedTypes =
        types_.replaceTypeScopes({});
    if (!sig.typeArgs.empty()) types_.pushTypeScope(sig.typeArgs);
    pushScope();
    for (size_t i = 0; i < sig.params.size(); ++i)
      bind(sig.params[i].name, entry->getArgument(i), sig.params[i].type, false);
    size_t errors = diags_.count();
    R r = genExpr(*sig.item->kids[3], Type());
    diags_.truncate(errors);
    types_.replaceTypeScopes(std::move(savedTypes));
    scopes_ = std::move(savedScopes);
    frames_ = std::move(savedFrames);
    moved_ = std::move(savedMoved);
    loopDepth_ = savedDepth;
    contract_ = savedContract;
    ghost_ = savedGhost;
    tmp.erase();
    if (!r || isUnit(r->type)) {
      fail(at, "cannot tell what this lambda returns; give its result "
               "type, as in 'let (x : i32) : i32 => x * x'");
      return false;
    }
    sig.result = r->type;
    return true;
  }

  // --- captures (ADR 0044, section 6) ---------------------------------

  static constexpr const char *kSelf = "closure#";

  // Each captured name rewritten as a field of the closure parameter.
  static void throughSelf(NodePtr &n, const Captures &caps) {
    if (n->kind == NodeKind::Name && n->flags.empty())
      for (const Capture &c : caps)
        if (c.name == n->text) {
          auto f = syntax::makeNode(NodeKind::Field, n->loc, c.name);
          f->add(syntax::makeNode(NodeKind::Name, n->loc, kSelf));
          n = std::move(f);
          return;
        }
    for (NodePtr &k : n->kids) throughSelf(k, caps);
  }

  // What a lambda captures: the list it writes after `let`, each name
  // copied, borrowed or referenced (ADR 0044, section 6). Every local the
  // body uses must be listed, once, and every listed name used. A copied
  // or borrowed capture cannot be assigned; a referenced one can.
  std::optional<Captures> capturesOf(const Node &lam) {
    std::set<std::string> params;
    const Node *list = nullptr;
    for (const NodePtr &k : lam.kids) {
      if (k->kind == NodeKind::LParam && !k->kids.empty() &&
          k->kids[0]->kind == NodeKind::PVar)
        params.insert(k->kids[0]->text);
      if (k->kind == NodeKind::Captures) list = k.get();
    }
    Captures caps;
    std::set<std::string> rejected;  // listed, and already reported
    bool ok = true;
    auto error = [&](const Node &at, std::string m) {
      fail(at, std::move(m));
      ok = false;
    };
    if (list)
      for (const NodePtr &c : list->kids) {
        rejected.insert(c->text);
        BindingPtr b = lookup(c->text);
        // A function parameter of a higher-order function, renamed to a
        // top-level function in its specialisation: nothing to capture.
        if (!b && !overloadSet(c->text).empty()) continue;
        if (!b) {
          error(*c, "'" + c->text + "' is not a local, so there is nothing "
                    "to capture; top-level functions and constructors are "
                    "used without capturing them");
          continue;
        }
        if (std::any_of(caps.begin(), caps.end(),
                        [&](const Capture &k) { return k.name == c->text; })) {
          error(*c, "'" + c->text + "' is captured twice; list it once");
          continue;
        }
        if (mlir::isa<AtomicType>(b->type)) {
          error(*c, "a lambda cannot capture the atomic cell '" + c->text +
                        "' yet (ADR 0052); pass it as a borrowed parameter");
          continue;
        }
        if ((isLinear(b->type) || hasDrop(b->type)) && c->flags != "moved") {
          error(*c, "'" + c->text + "' has the type " + typeName(b->type) +
                    ", which is linear or has a 'drop'; move it into the "
                    "lambda, as in '[moved " + c->text + "]', or borrow it");
          continue;
        }
        std::function<bool(Type)> copyable = [&](Type t) {
          if (copied(t)) return true;
          if (auto r = mlir::dyn_cast<RecordType>(t)) {
            for (Type f : r.getFieldTypes())
              if (!copyable(f)) return false;
            return true;
          }
          return false;
        };
        if (c->flags.empty() && !copyable(b->type) && !isLinear(b->type) &&
            !hasDrop(b->type)) {
          error(*c, "'" + c->text + "' is a " + typeName(b->type) +
                    ", which cannot be copied into a lambda; borrow it, "
                    "as in '[borrowed " + c->text + "]'");
          continue;
        }
        if (c->flags == "inout" && !b->isMutable) {
          error(*c, "'" + c->text + "' is not mutable, so a lambda cannot "
                    "write it; capture it as '[" + c->text + "]' (copied) "
                    "or '[borrowed " + c->text + "]'");
          continue;
        }
        caps.push_back({c->text, b, c->flags});
      }
    auto modeOf = [&](const std::string &name) -> const Capture * {
      for (const Capture &k : caps)
        if (k.name == name) return &k;
      return nullptr;
    };
    std::set<std::string> used, reported;
    std::function<void(const Node &)> walk = [&](const Node &k) {
      if (k.kind == NodeKind::LParam || k.kind == NodeKind::Captures) return;
      if (k.kind == NodeKind::Assign && !k.kids.empty()) {
        const Node *root = k.kids[0].get();
        while ((root->kind == NodeKind::Field || root->kind == NodeKind::Index) &&
               !root->kids.empty())
          root = root->kids[0].get();
        if (root->kind == NodeKind::Name && !params.count(root->text))
          if (const Capture *c = modeOf(root->text); c && c->mode != "inout")
            error(k, "'" + root->text + "' is " +
                         (c->mode.empty()       ? "copied into"
                          : c->mode == "moved" ? "moved into"
                                               : "borrowed by") +
                         " this lambda, so it cannot assign it; capture it "
                         "as '[inout " + root->text + "]' to write it");
      }
      if (k.kind == NodeKind::Name && k.flags.empty() && !params.count(k.text)) {
        if (modeOf(k.text)) {
          used.insert(k.text);
        } else if (lookup(k.text) && !rejected.count(k.text) &&
                   reported.insert(k.text).second) {
          const std::string &x = k.text;
          error(k, "'" + x + "' is used but not captured: add it to the "
                   "capture list as [" + x + "] (copied), [borrowed " + x +
                   "] or [inout " + x + "]");
        }
      }
      for (const NodePtr &c : k.kids) walk(*c);
    };
    for (const NodePtr &k : lam.kids) walk(*k);
    if (list)
      for (const NodePtr &c : list->kids)
        if (modeOf(c->text) && !used.count(c->text) && lookup(c->text))
          error(*c, "'" + c->text + "' is captured but never used; remove it "
                    "from the list");
    if (!ok) return std::nullopt;
    return caps;
  }

  static bool effectful(const Captures &caps) {
    return std::any_of(caps.begin(), caps.end(),
                       [](const Capture &c) { return c.mode == "inout"; });
  }

  // Whether a function type says it may have an effect: `inout` before
  // the arrow, `(f : inout t -> unit)` (ADR 0044, section 6).
  static bool effectfulArrow(const Arrow &a) {
    return !a.domains.empty() && !a.domains[0]->kids.empty() &&
           sema::hasModifier(a.domains[0]->kids[0]->text, "inout");
  }

  // A lambda as a value: its closure type, a record of its captures named
  // after the lambda, which meets `Function` through its `apply`, and the
  // record literal that makes the closure. Buffers are captured by
  // borrowing, so the closure borrows from them.
  struct Closure {
    Type type;
    std::string apply;
    const Node *value = nullptr;
    std::vector<BindingPtr> lenders;
    // The referenced captures: each field and the variable it writes back.
    std::vector<std::pair<std::string, BindingPtr>> refs;
  };
  std::optional<Closure> closureOf(const Node &lam, const Arrow *arrow,
                                   const std::vector<std::string> &typeParams,
                                   const std::string &what, const Captures &caps,
                                   const std::map<std::string, Type> *bound = nullptr) {
    std::string name = "lambda@" + placeOf(lam);
    Closure c;
    llvm::SmallVector<mlir::StringAttr> names;
    llvm::SmallVector<Type> fields;
    for (const Capture &k : caps) {
      names.push_back(b_.getStringAttr(k.name));
      fields.push_back(k.binding->type);
    }
    // One lambda in the source may capture different things in different
    // copies of its body, such as a higher-order function's proof and its
    // specialisations: each gets its own closure type.
    for (unsigned k = 2;; ++k) {
      c.type = types_.named(name);
      auto rt = mlir::dyn_cast_or_null<RecordType>(c.type);
      if (!c.type) {
        c.type = RecordType::get(&ctx_, name, names, fields);
        types_.define(name, c.type);
        break;
      }
      if (rt && rt.getFieldTypes() == llvm::ArrayRef<Type>(fields) &&
          rt.getFieldNames() == llvm::ArrayRef<mlir::StringAttr>(names))
        break;
      name = "lambda@" + placeOf(lam) + "#" + std::to_string(k);
    }
    struct Restore {
      std::string &s, saved;
      ~Restore() { s = saved; }
    } restoreName{closureName_, closureName_};
    closureName_ = name;
    std::optional<std::string> symbol =
        liftLambda(lam, arrow, typeParams, what, &caps, bound);
    if (!symbol) return std::nullopt;
    c.apply = *symbol;
    // A closure that owns a value with a `drop` drops it when it is
    // dropped itself, like a record holding it (ADR 0044, step 7).
    bool owns = false;
    for (const Capture &k : caps)
      owns |= k.mode == "moved" && hasDrop(k.binding->type);
    if (owns && !sigs_.count("drop[" + name + "]")) {
      syntax::SourceLoc at = lam.loc;
      auto item = syntax::makeNode(NodeKind::LetItem, at, "drop");
      Node *ps = item->add(syntax::makeNode(NodeKind::Params, at));
      Node *p = ps->add(syntax::makeNode(NodeKind::Param, at, kSelf));
      p->add(annotOf(*syntax::makeNode(NodeKind::TypeName, at, name), at));
      p->kids[0]->kids[0]->text = "moved";
      item->add(retAnnotNode(
          annotOf(*syntax::makeNode(NodeKind::TypeName, at, "unit"), at), at));
      item->add(syntax::makeNode(NodeKind::Contracts, at));
      // `match closure# with | { buf } -> ()`: each field is a local of
      // the arm, dropped at its end.
      auto m = syntax::makeNode(NodeKind::Match, at);
      m->add(syntax::makeNode(NodeKind::Name, at, kSelf));
      Node *arm = m->add(syntax::makeNode(NodeKind::Arm, at));
      Node *rec = arm->add(syntax::makeNode(NodeKind::PRecord, at));
      for (const Capture &k : caps) {
        Node *f = rec->add(syntax::makeNode(NodeKind::PField, at, k.name));
        f->add(syntax::makeNode(NodeKind::PVar, at, k.name));
      }
      arm->add(syntax::makeNode(NodeKind::Unit, at));
      item->add(std::move(m));
      sema::FuncSig sig;
      sig.name = "drop[" + name + "]";
      sig.item = item.get();
      synthesized_.push_back(std::move(item));
      if (!sema::resolveSignature(sig, types_, diags_)) return std::nullopt;
      std::string dsym = sig.name;
      sigs_.emplace(dsym, std::move(sig));
      overloads_["drop"].push_back(dsym);
      pendingInstances_.push_back(dsym);
    }
    auto lit = syntax::makeNode(NodeKind::RecordLit, lam.loc);
    for (const Capture &k : caps) {
      Node *f = lit->add(syntax::makeNode(NodeKind::FieldInit, lam.loc, k.name));
      f->add(syntax::makeNode(NodeKind::Name, lam.loc, k.name));
      // A loan, shared or exclusive, ends at the closure's last use; a
      // copy borrows nothing of the variable.
      if (!k.mode.empty() && k.mode != "moved")
        addLenders(c.lenders, {k.binding});
      addLenders(c.lenders, k.binding->lenders);
      if (k.mode == "inout") c.refs.push_back({k.name, k.binding});
    }
    c.value = keep(std::move(lit));
    return c;
  }

  // The symbol a top-level function passed as `arrow` is called by: its
  // own, or, when the arrow has a contract, a wrapper's that has it, so
  // the function's contract is checked against the arrow's.
  std::optional<std::string> functionArgument(const Node &name,
                                              const Arrow &arrow,
                                              const std::string &what) {
    std::vector<sema::FuncSig *> set = overloadSet(name.text);
    if (set.size() != 1) {
      fail(name, "'" + name.text + "' is overloaded, and passing an overload "
                 "set as a function comes later (ADR 0044, step 2)");
      return std::nullopt;
    }
    const sema::FuncSig &f = *set[0];
    if (f.isGeneric()) {
      fail(name, "'" + name.text + "' is generic, and passing a generic "
                 "function comes later (ADR 0044, step 4); pass a lambda "
                 "that calls it");
      return std::nullopt;
    }
    if (f.params.size() != arrow.domains.size()) {
      fail(name, "'" + name.text + "' takes " +
                     plural(f.params.size(), "argument") + ", but " + what +
                     " takes " + plural(arrow.domains.size(), "argument"));
      return std::nullopt;
    }
    if (!arrow.contracts || arrow.contracts->kids.empty()) return f.name;
    std::string symbol = f.name + "@" + placeOf(name);
    if (sigs_.count(symbol)) return symbol;
    const Node *fRet = retAnnotOf(f);
    if (!fRet) {
      fail(name, "'" + name.text + "' needs its return type written to be "
                 "passed as a function with a contract");
      return std::nullopt;
    }
    syntax::SourceLoc at = name.loc;
    std::vector<const Node *> fParams = valueParamsOf(f);
    auto item = syntax::makeNode(NodeKind::LetItem, at, symbol);
    Node *params = item->add(syntax::makeNode(NodeKind::Params, at));
    auto call = syntax::makeNode(NodeKind::Apply, at);
    call->add(syntax::makeNode(NodeKind::Name, at, f.source()));
    for (size_t i = 0; i < arrow.domains.size(); ++i) {
      std::string pname = arrow.domains[i]->text.empty()
                              ? f.params[i].name
                              : arrow.domains[i]->text;
      Node *p = params->add(syntax::makeNode(NodeKind::Param, at, pname));
      p->add(syntax::clone(*fParams[i]->kids[0]));
      call->add(syntax::makeNode(NodeKind::Name, at, pname));
    }
    item->add(retAnnotNode(syntax::clone(*fRet), at));
    Node *cs = item->add(syntax::makeNode(NodeKind::Contracts, at));
    arrowContracts(arrow, NodeKind::Requires, {}, *cs);
    arrowContracts(arrow, NodeKind::Ensures, {}, *cs, at);
    item->add(std::move(call));
    sema::FuncSig sig;
    sig.name = symbol;
    sig.item = item.get();
    synthesized_.push_back(std::move(item));
    if (!sema::resolveSignature(sig, types_, diags_)) return std::nullopt;
    sigs_.emplace(symbol, std::move(sig));
    overloads_[symbol].push_back(symbol);
    pendingInstances_.push_back(symbol);
    return symbol;
  }

  // The `apply` that makes a value of type `t` a function object of
  // `arity` arguments (ADR 0044, section 4): a function in scope whose
  // first parameter has type `t`. Any record or variant with one qualifies.
  const sema::FuncSig *applyFor(Type t, size_t arity) {
    if (!mlir::isa<RecordType>(t)) return nullptr;
    const sema::FuncSig *found = nullptr;
    for (const sema::FuncSig *s : overloadSet("apply")) {
      if (s->isGeneric() || s->params.size() != arity + 1 ||
          s->params[0].type != t)
        continue;
      if (found) return nullptr;
      found = s;
    }
    return found;
  }

  // What a function object passed as `arrow` is applied through: `apply`,
  // or, when the arrow has a contract, a wrapper with it whose first
  // parameter is the object, so `apply`'s contract is checked against it.
  std::optional<std::string> objectApply(const Node &at_, const sema::FuncSig &ap,
                                         const Arrow &arrow) {
    if (!arrow.contracts || arrow.contracts->kids.empty()) return "apply";
    std::string symbol = "apply@" + placeOf(at_);
    if (sigs_.count(symbol)) return symbol;
    const Node *ret = retAnnotOf(ap);
    if (!ret) {
      fail(at_, "'apply' needs its return type written for its object to be "
                "passed as a function with a contract");
      return std::nullopt;
    }
    syntax::SourceLoc at = at_.loc;
    std::vector<const Node *> apParams = valueParamsOf(ap);
    auto item = syntax::makeNode(NodeKind::LetItem, at, symbol);
    Node *params = item->add(syntax::makeNode(NodeKind::Params, at));
    auto call = syntax::makeNode(NodeKind::Apply, at);
    call->add(syntax::makeNode(NodeKind::Name, at, "apply"));
    for (size_t i = 0; i < apParams.size(); ++i) {
      std::string pname = i == 0 ? ap.params[0].name
                          : arrow.domains[i - 1]->text.empty()
                              ? ap.params[i].name
                              : arrow.domains[i - 1]->text;
      Node *p = params->add(syntax::makeNode(NodeKind::Param, at, pname));
      p->add(syntax::clone(*apParams[i]->kids[0]));
      call->add(syntax::makeNode(NodeKind::Name, at, pname));
    }
    item->add(retAnnotNode(syntax::clone(*ret), at));
    Node *cs = item->add(syntax::makeNode(NodeKind::Contracts, at));
    arrowContracts(arrow, NodeKind::Requires, {}, *cs);
    arrowContracts(arrow, NodeKind::Ensures, {}, *cs, at);
    item->add(std::move(call));
    sema::FuncSig sig;
    sig.name = symbol;
    sig.item = item.get();
    synthesized_.push_back(std::move(item));
    if (!sema::resolveSignature(sig, types_, diags_)) return std::nullopt;
    sigs_.emplace(symbol, std::move(sig));
    overloads_[symbol].push_back(symbol);
    pendingInstances_.push_back(symbol);
    return symbol;
  }

  // Makes each application `p x` in `n` call `via p x`.
  static void applyThrough(Node &n, const std::string &p, const std::string &via) {
    for (NodePtr &k : n.kids) applyThrough(*k, p, via);
    if (n.kind == NodeKind::Apply && !n.kids.empty() &&
        n.kids[0]->kind == NodeKind::Name && n.kids[0]->text == p &&
        n.kids[0]->flags.empty())
      n.kids.insert(n.kids.begin(),
                    syntax::makeNode(NodeKind::Name, n.kids[0]->loc, via));
  }

  // The higher-order functions, each after those its body names, and
  // otherwise in the order they are written. A name is matched by its last
  // component too, since a body from an interface names its module's
  // functions unqualified; matching too much only reorders.
  std::vector<sema::FuncSig *> hofsCalleesFirst() {
    std::vector<sema::FuncSig *> all;
    for (auto &[name, list] : hofs_)
      for (sema::FuncSig &h : list) all.push_back(&h);
    std::stable_sort(all.begin(), all.end(),
                     [](const sema::FuncSig *a, const sema::FuncSig *b) {
                       return a->item->loc.offset < b->item->loc.offset;
                     });
    auto last = [](llvm::StringRef n) { return n.rsplit('.').second.empty() ? n : n.rsplit('.').second; };
    std::map<std::string, std::vector<sema::FuncSig *>> byLast;
    for (sema::FuncSig *h : all) byLast[last(h->name).str()].push_back(h);
    std::vector<sema::FuncSig *> out;
    std::set<sema::FuncSig *> done, active;
    std::function<void(sema::FuncSig *)> visit = [&](sema::FuncSig *h) {
      if (done.count(h) || active.count(h)) return;
      active.insert(h);
      std::function<void(const Node &)> walk = [&](const Node &n) {
        if (n.kind == NodeKind::Name)
          if (auto c = byLast.find(last(n.text).str()); c != byLast.end())
            for (sema::FuncSig *callee : c->second)
              if (callee != h) visit(callee);
        for (const NodePtr &k : n.kids) walk(*k);
      };
      walk(*h->item);
      active.erase(h);
      done.insert(h);
      out.push_back(h);
    };
    for (sema::FuncSig *h : all) visit(h);
    return out;
  }

  // Proves a higher-order function once (ADR 0044, step 6, with ADR
  // 0043): each pure function parameter `p` becomes a parameter of a type
  // `p#type` that meets a concept made for it, whose one requirement is
  // `apply` with the arrow's types and `ensures`. The copy is checked and
  // proved like any generic, with `apply` uninterpreted, and each
  // specialisation is then an instance of that proof: its argument was
  // checked against the arrow's contract where it was passed. An
  // effectful arrow, or one with a `requires`, is left to the
  // specialisations, since the generic proof cannot assume it yet.
  void proveOnce(const sema::FuncSig &hof) {
    // A spec function has no goals of its own to share.
    if (hasFlag(*hof.item, "spec") || hasFlag(*hof.item, "import")) return;
    syntax::SourceLoc at = hof.item->loc;
    std::vector<NodePtr> concepts;
    NodePtr proof = syntax::clone(*hof.item);
    std::string symbol = hof.name + "#proof";
    proof->text = symbol;
    std::vector<NodePtr> params;
    for (NodePtr &q : proof->kids[0]->kids) {
      if (!sema::isFunctionParam(*q)) {
        params.push_back(std::move(q));
        continue;
      }
      Arrow arrow = arrowOf(*q->kids[0]->kids[1]);
      if (effectfulArrow(arrow)) return;
      if (arrow.contracts)
        for (const NodePtr &c : arrow.contracts->kids)
          if (c->kind != NodeKind::Ensures && c->kind != NodeKind::Requires)
            return;
      // Named after the function too: two proofs must not share the
      // instances made at their stand-ins.
      std::string tp = hof.name + "#" + q->text + "#type";
      std::string cname = hof.name + "#" + q->text;
      // `let meta find#p (f : type) (t : type) : concept = sig
      //    let apply : (g : f) -> (x : t) -> bool ensures ... end`
      auto concept = syntax::makeNode(NodeKind::LetItem, at, cname);
      concept->flags = "meta";
      Node *cps = concept->add(syntax::makeNode(NodeKind::Params, at));
      auto typeParam = [&](Node &into, const std::string &name) {
        Node *p = into.add(syntax::makeNode(NodeKind::Param, at, name));
        Node *a = p->add(syntax::makeNode(NodeKind::Annot, at));
        a->add(syntax::makeNode(NodeKind::Modifiers, at));
        a->add(syntax::makeNode(NodeKind::TypeKind, at));
        a->add(syntax::makeNode(NodeKind::None, at));
        return a;
      };
      // The concept's parameter has the copy's name for it, so the
      // requirement's contract reads the same in both.
      typeParam(*cps, tp);
      for (const std::string &t : hof.typeParams) typeParam(*cps, t);
      concept->add(retAnnotNode(
          annotOf(*syntax::makeNode(NodeKind::TypeName, at, "concept"), at), at));
      concept->add(syntax::makeNode(NodeKind::Contracts, at));
      Node *sig = concept->add(syntax::makeNode(NodeKind::Sig, at));
      Node *req = sig->add(syntax::makeNode(NodeKind::SigVal, at, "apply"));
      NodePtr type = syntax::clone(*q->kids[0]->kids[1]);
      Node *inner = type.get();
      while (inner->kids[1]->kind == NodeKind::ArrowType) inner = inner->kids[1].get();
      NodePtr contracts = inner->kids.size() > 2
                              ? std::move(inner->kids[2])
                              : syntax::makeNode(NodeKind::Contracts, at);
      if (inner->kids.size() > 2) inner->kids.pop_back();
      unsigned k = 0;
      for (Node *d = type.get(); d->kind == NodeKind::ArrowType;
           d = d->kids[1].get())
        if (d->kids[0]->text.empty())
          d->kids[0]->text = "x#" + std::to_string(++k);
      auto self = syntax::makeNode(NodeKind::ArrowType, at);
      Node *dom = self->add(syntax::makeNode(NodeKind::Domain, at, "g"));
      dom->add(syntax::makeNode(NodeKind::Modifiers, at));
      dom->add(syntax::makeNode(NodeKind::TypeName, at, tp));
      dom->add(syntax::makeNode(NodeKind::None, at));
      self->add(std::move(type));
      req->add(annotOf(*self, at));
      req->add(syntax::makeNode(NodeKind::Attrs, at));
      req->add(std::move(contracts));
      // `(p#type : type where find#p p#type t)` and `(p : p#type)`.
      auto tparam = syntax::makeNode(NodeKind::Param, q->loc, tp);
      Node *ta = tparam->add(syntax::makeNode(NodeKind::Annot, q->loc));
      ta->add(syntax::makeNode(NodeKind::Modifiers, q->loc));
      ta->add(syntax::makeNode(NodeKind::TypeKind, q->loc));
      auto where = syntax::makeNode(NodeKind::Apply, q->loc);
      where->add(syntax::makeNode(NodeKind::Name, q->loc, cname));
      where->add(syntax::makeNode(NodeKind::Name, q->loc, tp));
      for (const std::string &t : hof.typeParams)
        where->add(syntax::makeNode(NodeKind::Name, q->loc, t));
      ta->add(std::move(where));
      params.push_back(std::move(tparam));
      q->kids[0] = annotOf(*syntax::makeNode(NodeKind::TypeName, q->loc, tp), q->loc);
      params.push_back(std::move(q));
      concepts.push_back(std::move(concept));
    }
    proof->kids[0]->kids = std::move(params);
    for (NodePtr &c : concepts) {
      if (concepts_.count(c->text)) return;
      concepts_[c->text] = c.get();
      synthesized_.push_back(std::move(c));
    }
    sema::FuncSig sig;
    sig.name = symbol;
    sig.item = proof.get();
    for (const NodePtr &q : proof->kids[0]->kids)
      if (sema::isTypeParam(*q)) sig.typeParams.push_back(q->text);
    synthesized_.push_back(std::move(proof));
    sigs_.emplace(symbol, std::move(sig));
    // A check that fails only means the specialisations are proved each.
    size_t errors = diags_.count(), notes = notParametric_.size();
    checkDefinition(symbol);
    bool kept = diags_.count() == errors && notParametric_.size() == notes &&
                module_.lookupSymbol<mlir::func::FuncOp>("definition of " + symbol);
    // Why, as a note: a module with no specialisation of its own would
    // otherwise pass without proving the function at all.
    std::optional<NotParametric> why;
    if (diags_.count() > errors) {
      const syntax::Diagnostic &d = diags_.errors()[errors];
      why = NotParametric{file_.str() + ":" + std::to_string(d.loc.line) +
                              ":" + std::to_string(d.loc.column),
                          hof.name,
                          "its check over any function argument failed here: " +
                              d.message};
    } else if (notParametric_.size() > notes) {
      why = notParametric_[notes];
      why->generic = hof.name;
    }
    diags_.truncate(errors);
    notParametric_.resize(notes);
    if (why) notParametric_.push_back(std::move(*why));
    if (kept) hofProof_[hof.name] = symbol;
  }

  // A call of a name with higher-order overloads (ADR 0044, section 4): a
  // parameter of function type takes only a lambda, a named function or a
  // function object, and a value parameter never takes a lambda or a named
  // function, so `find xs 3` and `find xs (let (x : u8) => x > 3)` each
  // have one candidate.
  R genMixedCall(const Node &n, const std::string &name,
                 std::vector<sema::FuncSig> &hofs, const Node *targs,
                 const std::vector<const Node *> &args, Type expected) {
    // A lone higher-order function explains a wrong argument itself.
    if (hofs.size() == 1 && overloadSet(name).empty())
      return genHigherOrderCall(n, hofs[0], targs, args, expected);
    auto isFunction = [&](const Node &a) {
      if (a.kind == NodeKind::Lambda || partialOf(a)) return true;
      if (a.kind != NodeKind::Name || !a.flags.empty() || lookup(a.text))
        return false;
      return !overloadSet(a.text).empty() || hofs_.count(a.text) > 0;
    };
    auto known = [&](const Node &a) -> Type {
      if (a.kind == NodeKind::Name && a.flags.empty())
        if (BindingPtr b = lookup(a.text)) return b->type;
      return Type();
    };
    std::vector<std::pair<std::string, bool>> notes;  // label, chosen
    std::vector<std::string> rejected;
    std::vector<sema::FuncSig *> viableHofs;
    for (sema::FuncSig &h : hofs) {
      std::string label = "the higher-order '" + name + "' at line " +
                          std::to_string(h.item->loc.line);
      std::vector<const Node *> vps = valueParamsOf(h);
      if (vps.size() != args.size()) {
        rejected.push_back(label + " takes " + plural(vps.size(), "argument"));
        continue;
      }
      std::string why;
      for (size_t i = 0; i < args.size() && why.empty(); ++i) {
        const Node &p = *vps[i];
        if (sema::isFunctionParam(p)) {
          size_t arity = arrowOf(*p.kids[0]->kids[1]).domains.size();
          Type t = known(*args[i]);
          if (!isFunction(*args[i]) && !(t && applyFor(t, arity)))
            why = "'" + p.text + "' takes a function, and argument " +
                  std::to_string(i + 1) + " is not one";
        } else if (isFunction(*args[i])) {
          why = "'" + p.text + "' takes a value, and argument " +
                std::to_string(i + 1) + " is a function";
        }
      }
      if (!why.empty()) {
        rejected.push_back(label + ": " + why);
        continue;
      }
      viableHofs.push_back(&h);
      notes.push_back({label, false});
    }
    // The other overloads take values only. A candidate whose parameter
    // types clash with the types of the named arguments does not fit.
    std::vector<sema::FuncSig *> values;
    for (sema::FuncSig *sig : overloadSet(name)) {
      std::string label = sig->isGeneric()
                              ? "the generic '" + name + "' at line " +
                                    std::to_string(sig->item->loc.line)
                              : "'" + sig->name + "'";
      std::vector<const Node *> vps = valueParamsOf(*sig);
      std::string why;
      if (vps.size() != args.size())
        why = "takes " + plural(vps.size(), "argument");
      std::map<std::string, Type> bound;
      for (size_t i = 0; i < args.size() && why.empty(); ++i) {
        if (isFunction(*args[i])) {
          why = "'" + vps[i]->text + "' takes a value, and argument " +
                std::to_string(i + 1) + " is a function";
          break;
        }
        Type t = known(*args[i]);
        if (!t) continue;
        if (sig->isGeneric()) {
          const Node &q = *vps[i];
          if (!q.kids.empty() && q.kids[0]->kind == NodeKind::Annot &&
              !types_.unify(*q.kids[0], t, sig->typeParams, bound))
            why = "argument " + std::to_string(i + 1) + " has type " +
                  typeName(t) + ", which does not fit '" + q.text + "'";
        } else if (t != sig->params[i].type &&
                   !converts(t, sig->params[i].type)) {
          why = "argument " + std::to_string(i + 1) + " has type " +
                typeName(t);
        }
      }
      if (!why.empty()) {
        rejected.push_back(label + ": " + why);
        continue;
      }
      values.push_back(sig);
      notes.push_back({label, false});
    }
    size_t viable = viableHofs.size() + values.size();
    std::string outcome;
    if (viable == 1)
      notes.back().second = true;
    else
      outcome = viable ? "it is ambiguous" : "no candidate is left";
    if (options_.explanations && !checking_ &&
        n.loc.line == options_.explainLine) {
      auto note = [&](std::string m) {
        options_.explanations->push_back({n.loc, std::move(m)});
      };
      note("the call of '" + name + "' has " +
           plural(viable + rejected.size(), "candidate"));
      for (auto &[label, chosen] : notes)
        note("  " + label + (chosen ? ": viable, and chosen" : ": viable"));
      for (const std::string &r : rejected) note("  removed: " + r);
      if (!outcome.empty()) note("  " + outcome);
    }
    if (viable == 0) {
      std::string list;
      for (const std::string &r : rejected) list += "\n  " + r;
      return fail(n, "no '" + name + "' takes these arguments:" + list);
    }
    if (viable > 1) {
      std::string list;
      for (auto &[label, chosen] : notes) list += "\n  " + label;
      return fail(n, "the call of '" + name + "' is ambiguous; these all "
                     "fit:" + list);
    }
    if (!viableHofs.empty())
      return genHigherOrderCall(n, *viableHofs[0], targs, args, expected);
    sema::FuncSig &sig = *values[0];
    if (sig.isGeneric()) return genGenericCall(n, sig, targs, args, expected);
    if (targs)
      return fail(*targs, "'" + name + "' is not generic, so it takes no "
                          "type arguments");
    return genCall(n, sig, args);
  }

  // The type parameters of a generic higher-order function that its
  // arguments fix before any lambda is made: from named values, and from
  // the written types of typed lambdas, function objects and named
  // functions (ADR 0044, section 2). An untyped lambda then takes its
  // parameter types from these.
  std::map<std::string, Type> deduceFromArguments(
      const sema::FuncSig &hof, const std::vector<const Node *> &valueParams,
      const std::vector<const Node *> &args) {
    std::map<std::string, Type> bound;
    if (hof.typeParams.empty()) return bound;
    const std::vector<std::string> &tps = hof.typeParams;
    for (size_t i = 0; i < args.size() && i < valueParams.size(); ++i) {
      const Node &p = *valueParams[i];
      const Node &a = *args[i];
      if (p.kids.empty() || p.kids[0]->kind != NodeKind::Annot) continue;
      BindingPtr local = a.kind == NodeKind::Name && a.flags.empty()
                             ? lookup(a.text)
                             : nullptr;
      if (!sema::isFunctionParam(p)) {
        if (local) (void)types_.unify(*p.kids[0], local->type, tps, bound);
        continue;
      }
      Arrow arrow = arrowOf(*p.kids[0]->kids[1]);
      std::vector<Type> doms;
      Type result;
      if (a.kind == NodeKind::Lambda) {
        for (const NodePtr &k : a.kids) {
          if (k->kind == NodeKind::LParam)
            doms.push_back(k->kids.size() > 1 &&
                                   k->kids[1]->kind == NodeKind::Annot &&
                                   k->kids[1]->kids[1]->kind != NodeKind::TypeKind
                               ? quietResolve(*k->kids[1])
                               : Type());
          if (k->kind == NodeKind::RetAnnot && !k->kids.empty() &&
              k->kids[0]->kind == NodeKind::Annot)
            result = quietResolve(*k->kids[0]);
        }
      } else if (local) {
        if (const sema::FuncSig *ap = applyFor(local->type, arrow.domains.size())) {
          for (size_t j = 1; j < ap->params.size(); ++j)
            doms.push_back(ap->params[j].type);
          result = ap->result;
        }
      } else if (a.kind == NodeKind::Name && a.flags.empty()) {
        std::vector<sema::FuncSig *> set = overloadSet(a.text);
        if (set.size() == 1 && !set[0]->isGeneric()) {
          for (const sema::Param &q : set[0]->params) doms.push_back(q.type);
          result = set[0]->result;
        }
      }
      for (size_t j = 0; j < doms.size() && j < arrow.domains.size(); ++j)
        if (doms[j]) (void)types_.unify(*arrow.domains[j]->kids[1], doms[j], tps, bound);
      if (result) (void)types_.unify(*arrow.result, result, tps, bound);
    }
    return bound;
  }

  // A written type resolved without reporting errors: a deduction that
  // does not work out is reported where the type is used.
  Type quietResolve(const Node &annot) {
    size_t errors = diags_.count();
    Type t = types_.resolveAnnot(annot);
    diags_.truncate(errors);
    return t;
  }

  // The function a partial application `f a` applies: a lone top-level
  // function of more parameters than the arguments given (ADR 0044, step
  // 7).
  const sema::FuncSig *partialOf(const Node &n) {
    if (n.kind != NodeKind::Apply || n.kids.size() < 2 ||
        n.kids[0]->kind != NodeKind::Name || !n.kids[0]->flags.empty() ||
        lookup(n.kids[0]->text))
      return nullptr;
    std::vector<sema::FuncSig *> set = overloadSet(n.kids[0]->text);
    if (set.size() != 1 || set[0]->isGeneric() || set[0]->isHigherOrder())
      return nullptr;
    return set[0]->params.size() > n.kids.size() - 1 ? set[0] : nullptr;
  }

  // `f a` with parameters left is `let [a] (x : t) => f a x`: a local
  // argument is captured (copied, or borrowed when it cannot be), a
  // literal is written in, and anything else must be bound first.
  const Node *partialLambda(const Node &n, const sema::FuncSig &f) {
    syntax::SourceLoc at = n.loc;
    auto lam = syntax::makeNode(NodeKind::Lambda, at);
    auto caps = syntax::makeNode(NodeKind::Captures, at);
    auto body = syntax::makeNode(NodeKind::Apply, at);
    body->add(syntax::makeNode(NodeKind::Name, at, f.source()));
    for (size_t i = 1; i < n.kids.size(); ++i) {
      const Node &a = *n.kids[i];
      if (a.kind == NodeKind::Name && a.flags.empty()) {
        if (BindingPtr b = lookup(a.text)) {
          Node *c = caps->add(syntax::makeNode(NodeKind::Capture, a.loc, a.text));
          if (!copied(b->type)) c->flags = "borrowed";
        }
      } else if (!isLiteral(a) && a.kind != NodeKind::Unit) {
        fail(a, "a partial application captures its arguments: bind this "
                "one with 'let' first, as in 'let k = ... in " + f.source() +
                    " k'");
        return nullptr;
      }
      body->add(syntax::clone(a));
    }
    if (!caps->kids.empty()) lam->add(std::move(caps));
    std::vector<const Node *> fps = valueParamsOf(f);
    for (size_t j = n.kids.size() - 1; j < fps.size(); ++j) {
      std::string name = "arg#" + std::to_string(j);
      Node *lp = lam->add(syntax::makeNode(NodeKind::LParam, at));
      lp->add(syntax::makeNode(NodeKind::PVar, at, name));
      lp->add(syntax::clone(*fps[j]->kids[0]));
      body->add(syntax::makeNode(NodeKind::Name, at, name));
    }
    if (const Node *ret = retAnnotOf(f))
      lam->add(retAnnotNode(syntax::clone(*ret), at));
    lam->add(std::move(body));
    return keep(std::move(lam));
  }

  // A call of a higher-order function: to its specialisation at these
  // function arguments, `find[lambda@f.pia:12:9]`, made on first use, with
  // the other arguments.
  R genHigherOrderCall(const Node &n, const sema::FuncSig &hof,
                       const Node *targs, const std::vector<const Node *> &args,
                       Type expected) {
    // A spec function over function values, such as a law, is what
    // contracts call (ADR 0044, section 5).
    if ((contract_ || ghost_) && !hasFlag(*hof.item, "spec"))
      return fail(n, "only a spec function that takes a function can be "
                     "called in a contract (ADR 0044)");
    std::vector<const Node *> valueParams = valueParamsOf(hof);
    if (args.size() != valueParams.size())
      return fail(n, "'" + hof.source() + "' takes " +
                         plural(valueParams.size(), "argument") + ", given " +
                         std::to_string(args.size()) +
                         "; partial application is not supported yet");
    std::map<std::string, Type> bound = deduceFromArguments(hof, valueParams, args);
    std::vector<std::string> symbols;
    std::map<std::string, std::string> rename;
    // Function objects: each parameter's type, and what its applications
    // call, `apply` or a wrapper with the arrow's contract.
    std::map<std::string, std::pair<Type, std::string>> objects;
    // The function parameters given closures that write a capture: the
    // specialisation takes them `inout`, and each call writes back.
    std::set<std::string> writing;
    struct ScopeGuard {
      Gen &g;
      bool pushed = false;
      ~ScopeGuard() {
        if (pushed) g.popScope();
      }
    } hidden{*this};
    std::vector<const Node *> rest;
    for (size_t i = 0; i < args.size(); ++i) {
      const Node &p = *valueParams[i];
      if (!sema::isFunctionParam(p)) {
        rest.push_back(args[i]);
        continue;
      }
      Arrow arrow = arrowOf(*p.kids[0]->kids[1]);
      std::string what = "'" + p.text + "' of '" + hof.source() + "'";
      // `lt 3`, a partial application, is a lambda of what is left.
      const Node *argNode = args[i];
      if (const sema::FuncSig *f = partialOf(*argNode)) {
        argNode = partialLambda(*argNode, *f);
        if (!argNode) return std::nullopt;
      }
      const Node &a = *argNode;
      std::optional<std::string> symbol;
      BindingPtr g = a.kind == NodeKind::Name && a.flags.empty()
                         ? lookup(a.text)
                         : nullptr;
      if (g && mlir::isa<RecordType>(g->type)) {
        const sema::FuncSig *ap = applyFor(g->type, arrow.domains.size());
        if (!ap)
          return fail(a, what + " is a function, and '" + a.text + "' has "
                         "type " + typeName(g->type) + ", which has no "
                         "'apply' taking " +
                         plural(arrow.domains.size(), "argument") +
                         " after it, so it is not a function object");
        std::string tname = writtenName(g->type);
        if (tname.empty())
          return fail(a, "a function object of the generic type " +
                             typeName(g->type) + " cannot be passed yet");
        if (!g->refs.empty()) {
          if (!effectfulArrow(arrow))
            return fail(a, "'" + a.text + "' writes a captured variable, "
                           "and " + what + " is not a function type that "
                           "may: write it as '(" + p.text + " : inout t -> "
                           "unit)' (ADR 0044, section 6)");
          writing.insert(p.text);
        }
        std::optional<std::string> via = objectApply(a, *ap, arrow);
        if (!via) return std::nullopt;
        objects[p.text] = {g->type, *via};
        symbols.push_back(tname);
        rest.push_back(args[i]);
        continue;
      }
      if (a.kind == NodeKind::Lambda) {
        std::optional<Captures> caps = capturesOf(a);
        if (!caps) return std::nullopt;
        if (!caps->empty()) {
          // A lambda that captures is passed as its closure, a function
          // object whose fields are the captures.
          std::optional<Closure> c =
              closureOf(a, &arrow, hof.typeParams, what, *caps, &bound);
          if (!c) return std::nullopt;
          std::optional<std::string> via =
              objectApply(a, sigs_.at(c->apply), arrow);
          if (!via) return std::nullopt;
          objects[p.text] = {c->type, *via};
          symbols.push_back("lambda@" + placeOf(a));
          if (effectful(*caps)) {
            if (!effectfulArrow(arrow))
              return fail(a, "this lambda writes a captured variable, and " +
                                 what + " is not a function type that may: "
                                 "write it as '(" + p.text + " : inout t -> "
                                 "unit)' (ADR 0044, section 6)");
            // Made here, in a hidden mutable local the call threads, so
            // its writes reach the captured variables after the call.
            R v = genExpr(*c->value, c->type);
            if (!v) return std::nullopt;
            if (!hidden.pushed) {
              pushScope();
              hidden.pushed = true;
            }
            std::string name = std::string(kSelf) + placeOf(a);
            BindingPtr hb = bind(name, v->value, c->type, true);
            hb->refs = c->refs;
            hb->lenders = c->lenders;
            writing.insert(p.text);
            rest.push_back(keep(syntax::makeNode(NodeKind::Name, a.loc, name)));
            continue;
          }
          rest.push_back(c->value);
          continue;
        }
        symbol = liftLambda(a, &arrow, hof.typeParams, what, nullptr, &bound);
      } else if (a.kind == NodeKind::Name && a.flags.empty() &&
                 !overloadSet(a.text).empty()) {
        symbol = functionArgument(a, arrow, what);
      } else if (a.kind == NodeKind::Name && a.flags.empty() &&
                 hofs_.count(a.text)) {
        return fail(a, "'" + a.text + "' is a higher-order function, and "
                       "passing one comes later (ADR 0044)");
      } else {
        return fail(a, what + " is a function: pass a lambda, as in "
                       "'(let (x : u8) => x > 3)', or the name of a "
                       "top-level function; other function values come "
                       "later (ADR 0044)");
      }
      if (!symbol) return std::nullopt;
      symbols.push_back(*symbol);
      rename[p.text] = *symbol;
    }
    std::string key = hof.name + "[" + llvm::join(symbols, ", ") + "]";
    auto it = sigs_.find(key);
    if (it == sigs_.end()) {
      NodePtr item = syntax::clone(*hof.item);
      item->text = key;
      std::vector<NodePtr> &ps = item->kids[0]->kids;
      // A function object stays a parameter, of its own type, and each
      // application of it calls its `apply`.
      for (NodePtr &q : ps)
        if (auto o = objects.find(q->text);
            sema::isFunctionParam(*q) && o != objects.end())
        {
          q->kids[0]->kids[1] = syntax::makeNode(
              NodeKind::TypeName, q->loc, writtenName(o->second.first));
          if (writing.count(q->text)) q->kids[0]->kids[0]->text = "inout mutable";
        }
      for (auto &[name, object] : objects)
        applyThrough(*item, name, object.second);
      ps.erase(std::remove_if(ps.begin(), ps.end(),
                              [](const NodePtr &q) {
                                return sema::isFunctionParam(*q);
                              }),
               ps.end());
      renameNames(*item, rename, nullptr);
      sema::FuncSig sig;
      sig.name = key;
      sig.item = item.get();
      sig.typeParams = hof.typeParams;
      synthesized_.push_back(std::move(item));
      if (!sig.isGeneric()) {
        if (!sema::resolveSignature(sig, types_, diags_)) return std::nullopt;
        pendingInstances_.push_back(key);
      }
      it = sigs_.emplace(key, std::move(sig)).first;
      overloads_[key].push_back(key);
      // Discharged by the higher-order function's proof, unless a closure
      // writes through it, which the proof does not cover.
      if (auto p = hofProof_.find(hof.name); p != hofProof_.end() && writing.empty())
        provedBy_[key] = p->second;
    }
    sema::FuncSig &spec = it->second;
    if (spec.isGeneric())
      return genGenericCall(n, spec, targs, rest, expected, &bound);
    if (targs)
      return fail(*targs, "'" + hof.source() + "' is not generic, so it takes "
                          "no type arguments");
    return genCall(n, spec, rest);
  }

  // The functions a written name may call: one, or an overload set.
  // The higher-order functions named `name`: in code from another module,
  // that module's by their own names too.
  std::map<std::string, std::vector<sema::FuncSig>>::iterator findHof(
      const std::string &name) {
    auto h = hofs_.find(name);
    if (h == hofs_.end() && !adlModule_.empty() &&
        name.find('.') == std::string::npos)
      h = hofs_.find(adlModule_ + "." + name);
    return h;
  }

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
    // In code from another module, that module's functions by their own
    // names (ADR 0039, section 6).
    if (!adlModule_.empty() && name.find('.') == std::string::npos)
      if (auto m = overloads_.find(adlModule_ + "." + name);
          m != overloads_.end())
        for (const std::string &symbol : m->second)
          if (auto s = sigs_.find(symbol); s != sigs_.end())
            if (!llvm::is_contained(out, &s->second)) out.push_back(&s->second);
    // A concept's function, called by its own name in a generic over an
    // imported concept, is also found in the concept's module: a generic of
    // Pia.Core.Algo.Search calls `same`, which Pia.Core.Order defines for
    // u8 as Pia.Core.Order.same (ADR 0039, section 6). The arguments'
    // types choose among them and this module's own (genOverloadedCall),
    // as when Pia.Core.Option's generic `same` over options calls Eq's
    // `same` on its elements; one with the parameter types of a function
    // already found is left out, so it never makes a call ambiguous.
    auto shadowed = [&](const sema::FuncSig &f) {
      for (const sema::FuncSig *o : out) {
        if (o->isGeneric() || f.isGeneric() ||
            o->params.size() != f.params.size())
          continue;
        bool same = true;
        for (size_t i = 0; same && i < f.params.size(); ++i)
          same = o->params[i].type == f.params[i].type;
        if (same) return true;
      }
      return false;
    };
    if (name.find('.') == std::string::npos)
      for (auto &[cname, item] : concepts_) {
        llvm::StringRef module = llvm::StringRef(cname).rsplit('.').first;
        if (module == cname) continue;
        bool requires = false;
        for (const syntax::NodePtr &r : item->kids[3]->kids)
          requires |= r->kind == NodeKind::SigVal && r->text == name;
        if (!requires) continue;
        if (auto m = overloads_.find(module.str() + "." + name); m != overloads_.end())
          for (const std::string &symbol : m->second)
            if (auto s = sigs_.find(symbol); s != sigs_.end())
              if (!llvm::is_contained(out, &s->second) && !shadowed(s->second))
                out.push_back(&s->second);
      }
    return out;
  }

  // The module an imported item came from: its `from:M` flag.
  static std::string fromModule(const Node &item) {
    llvm::SmallVector<llvm::StringRef> words;
    llvm::StringRef(item.flags).split(words, ' ', -1, false);
    for (llvm::StringRef w : words)
      if (w.consume_front("from:")) return w.str();
    return "";
  }

  // Sets the module whose functions code may call by their own names,
  // while it is generated, and restores the one before. An empty module
  // keeps the one already set.
  struct AdlScope {
    std::string &slot;
    std::string saved;
    AdlScope(std::string &s, std::string module) : slot(s), saved(s) {
      if (!module.empty()) slot = std::move(module);
    }
    ~AdlScope() { slot = std::move(saved); }
  };

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
    std::vector<const syntax::NodePtr *> items;
    if (functionConcept_)
      for (const syntax::NodePtr &item : functionConcept_->kids)
        items.push_back(&item);
    for (const syntax::NodePtr &item : program.kids) items.push_back(&item);
    for (const syntax::NodePtr *itemPtr : items) {
      const syntax::NodePtr &item = *itemPtr;
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
    // A generic that meets a requirement only if its own arguments already
    // meet the concept would be circular (genericMeeting).
    if (deciding_.count(key) && meetingGeneric_)
      return "it would meet it only through itself";
    if (auto it = met_.find(key); it != met_.end()) return it->second;
    // An `include` that comes back to this concept adds nothing new.
    met_[key] = std::nullopt;
    deciding_.insert(key);
    const Node &item = *concepts_.at(cname);
    // An imported concept's requirements are met by functions of its
    // module too, as `Pia.Core.Order.less` meets Ord's `less` (ADR 0039).
    AdlScope adl(adlModule_, fromModule(item));
    std::map<std::string, Type> scope;
    size_t i = 0;
    for (const syntax::NodePtr &p : item.kids[0]->kids)
      if (sema::isTypeParam(*p) && i < args.size()) scope[p->text] = args[i++];
    std::vector<std::map<std::string, Type>> saved =
        types_.replaceTypeScopes({scope});
    size_t queued = queuedLog_.size(), matched = matchedLog_.size();
    std::string outer = std::exchange(requirer_, "the concept '" + cname + "'");
    std::optional<std::string> why = requirementsUnmet(item, key, scope, via);
    requirer_ = std::move(outer);
    types_.replaceTypeScopes(std::move(saved));
    deciding_.erase(key);
    met_[key] = why;
    if (!why && !via) certify(fromModule(item), args, queued, matched);
    return why;
  }

  // An imported concept met at types of its own module, or built-in ones,
  // by functions of that module alone was checked there: a module proves
  // every such instance its interfaces allow (checkModule). So the laws and
  // requirement contracts queued for it are its module's proofs, which
  // this program does not repeat (ADR 0039, step 6).
  void certify(const std::string &from, const std::vector<Type> &args,
               size_t queued, size_t matched) {
    if (from.empty()) return;
    for (Type t : args) {
      if (mlir::isa<ArrayType, SliceType>(t)) return;
      if (auto rec = mlir::dyn_cast<RecordType>(t))
        if (!llvm::StringRef(rec.getName()).starts_with(from + ".")) return;
    }
    for (size_t i = matched; i < matchedLog_.size(); ++i) {
      const sema::FuncSig &sig = sigs_.at(matchedLog_[i]);
      if (!sig.item || fromModule(*sig.item) != from) return;
    }
    for (size_t i = queued; i < queuedLog_.size(); ++i)
      certified_[queuedLog_[i]] = from;
  }

  // Proves, in a module, each instance of the concepts its interfaces list
  // that its exported functions meet at its own types or built-in ones, so
  // importers can rely on it (certify). A type that does not meet a
  // concept is no error, and leaves nothing to prove.
  void proveExportedConcepts(const std::vector<std::string> &concepts) {
    llvm::SetVector<Type> types;
    auto candidate = [&](Type t) {
      if (!t || mlir::isa<ArrayType, SliceType>(t)) return;
      if (auto rec = mlir::dyn_cast<RecordType>(t)) {
        llvm::StringRef name = rec.getName();
        if (name.contains('<') || name.contains('.')) return;
      }
      types.insert(t);
    };
    for (const auto &[symbol, path] : exports_) {
      const sema::FuncSig &sig = sigs_.at(symbol);
      for (const sema::Param &p : sig.params) candidate(p.type);
      candidate(sig.result);
    }
    for (const std::string &cname : concepts) {
      auto c = concepts_.find(cname);
      if (c == concepts_.end()) continue;
      size_t params = 0;
      for (const syntax::NodePtr &p : c->second->kids[0]->kids)
        params += sema::isTypeParam(*p);
      if (params != 1) continue;
      for (Type t : types) {
        size_t queued = queuedLog_.size();
        std::vector<std::string> before(pendingInstances_.begin(),
                                        pendingInstances_.end());
        if (!unmet(cname, {t})) continue;
        // Unmet: what it queued for the requirements it did meet goes.
        for (size_t i = queued; i < queuedLog_.size(); ++i)
          sigs_.erase(queuedLog_[i]);
        pendingInstances_.assign(before.begin(), before.end());
        queuedLog_.resize(queued);
      }
    }
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
        if (std::optional<std::string> why =
                sigValUnmet(*r, key, scope, via, nullptr))
          return why;
      } else if (r->kind == NodeKind::SigLemma) {
        queueLemma(key + "." + r->text, syntax::clone(*r->kids[0]),
                   syntax::clone(*r->kids[1]),
                   syntax::makeNode(NodeKind::Unit, r->loc), scope, r->loc,
                   via);
      }
    }
    return std::nullopt;
  }

  // Why no function meets the requirement `r`, a `let name : type`
  // contracts item of a concept or an interface, or nothing when one does:
  // a function with that name, exactly that type and modifiers, and a
  // contract at least as strong, which is queued as a lemma. `matched`, if
  // given, gets the function's symbol.
  std::optional<std::string> sigValUnmet(
      const Node &req, const std::string &key,
      const std::map<std::string, Type> &scope, const AdapterInfo *via,
      std::string *matched, bool strict = false) {
    const Node *r = &req;
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
    for (sema::FuncSig *cand : overloadSet(r->text)) cands.push_back(cand);
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
    // A generic function meets it at the type arguments its parameters
    // deduce, as a generic `alloc` over `bump t` meets `Allocator (bump
    // u16) u16` at t = u16.
    for (sema::FuncSig *cand : cands) {
      if (found)
        break;
      if (!cand->isGeneric())
        continue;
      found = genericMeeting(*cand, ptypes, mods, result);
    }
    if (!found) return "no function '" + spelled + "'";
    if (matched) *matched = found->name;
    matchedLog_.push_back(found->name);
    // An interface is all its importers will see (ADR 0039), so a
    // function's own `requires` must follow from the interface's even when
    // the interface states none.
    bool ownRequires = false;
    for (const syntax::NodePtr &c : found->item->kids[2]->kids)
      ownRequires = ownRequires || c->kind == NodeKind::Requires;
    if (!r->kids[2]->kids.empty() || (strict && ownRequires))
      queueContractLemma(*r, key, names, *found, scope, via);
    return std::nullopt;
  }

  // The instance of `generic` with exactly the parameter types `ptypes`,
  // modifiers `mods` and result `result`, deduced from them, or null.
  sema::FuncSig *genericMeeting(const sema::FuncSig &generic,
                                const std::vector<Type> &ptypes,
                                const std::vector<std::string> &mods,
                                Type result) {
    std::vector<const Node *> written = valueParamsOf(generic);
    if (written.size() != ptypes.size())
      return nullptr;
    std::map<std::string, Type> bound;
    for (size_t i = 0; i < written.size(); ++i) {
      const Node &p = *written[i];
      if (p.kids.empty() || p.kids[0]->kind != NodeKind::Annot ||
          !types_.unify(*p.kids[0], ptypes[i], generic.typeParams, bound))
        return nullptr;
    }
    if (const Node *ret = retAnnotOf(generic))
      if (!types_.unify(*ret, result, generic.typeParams, bound))
        return nullptr;
    for (const std::string &t : generic.typeParams)
      if (!bound.count(t))
        return nullptr;
    bool outer = std::exchange(meetingGeneric_, true);
    bool unmetHere = constraintsUnmet(generic, bound).has_value();
    meetingGeneric_ = outer;
    if (unmetHere)
      return nullptr;
    sema::FuncSig *inst = genericInstance(generic, bound);
    if (!inst || inst->result != result)
      return nullptr;
    for (size_t i = 0; i < ptypes.size(); ++i)
      if (inst->params[i].type != ptypes[i] ||
          inst->params[i].modifiers != mods[i])
        return nullptr;
    return inst;
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
    if (writesParam(*req.kids[0]->kids[1])) {
      queueContractCall(req, key, names, found, scope, via);
      return;
    }
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
      p->flags = cur->kids[0]->flags;  // its regions (ADR 0042)
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
    // A lemma's postcondition names no `result`, so the body ends with a
    // call of it, which assumes what the lemma proved (#305).
    NodePtr body = hasFlag(*found.item, "lemma")
                       ? syntax::clone(*call)
                       : syntax::makeNode(NodeKind::Unit, at);
    const Node &own = *found.item->kids[2];
    for (size_t i = own.kids.size(); i-- > 0;) {
      if (own.kids[i]->kind != NodeKind::Requires) continue;
      auto seq = syntax::makeNode(NodeKind::Sequence, at);
      Node *a = seq->add(syntax::makeNode(NodeKind::Assert, own.kids[i]->loc));
      a->add(syntax::clone(*own.kids[i]->kids[0]));
      seq->add(std::move(body));
      body = std::move(seq);
    }
    // Each overload of a name meets its own requirement, so its lemma is
    // named after the overload's symbol, as `eq(u8, u8)`: a lemma whose
    // symbol is already queued is not queued again.
    std::string what = overloadSet(req.text).size() > 1 ? found.name : req.text;
    std::string symbol = key + "." + what + ".contract";
    // Its assertions say whose precondition they check, and what gives it.
    if (!requirer_.empty())
      assertClaims_.emplace(symbol, requirer_ + " gives the precondition of '" +
                                        req.text + "'");
    queueLemma(symbol, std::move(params), std::move(contracts), std::move(body),
               scope, at, via);
  }

  // A function that writes its parameters honours a requirement's contract
  // when a call of it, under the requirement's precondition, meets the
  // requirement's postcondition, which may name the parameters after the
  // call and, with `old`, before it. A lemma cannot say that, so the proof
  // is a function with the requirement's contract and the parameters'
  // modifiers, whose body is the call. Nothing calls it.
  void queueContractCall(const Node &req, const std::string &key,
                         const std::vector<std::string> &names,
                         const sema::FuncSig &found,
                         const std::map<std::string, Type> &scope,
                         const AdapterInfo *via) {
    syntax::SourceLoc at = req.loc;
    std::string what = overloadSet(req.text).size() > 1 ? found.name : req.text;
    std::string symbol = key + "." + what + ".contract";
    if (sigs_.count(symbol)) return;
    std::map<std::string, std::string> rename;
    auto params = syntax::makeNode(NodeKind::Params, at);
    auto call = syntax::makeNode(NodeKind::Apply, at);
    call->add(syntax::makeNode(NodeKind::Name, at, req.text));
    const Node *cur = req.kids[0]->kids[1].get();
    for (size_t i = 0; i < names.size(); ++i, cur = cur->kids[1].get()) {
      const std::string &mine = found.params[i].name;
      rename[names[i]] = mine;
      Node *p = params->add(syntax::makeNode(NodeKind::Param, at, mine));
      p->flags = cur->kids[0]->flags;  // its regions (ADR 0042)
      Node *annot = p->add(syntax::makeNode(NodeKind::Annot, at));
      annot->add(syntax::clone(*cur->kids[0]->kids[0]));
      annot->add(syntax::clone(*cur->kids[0]->kids[1]));
      annot->add(syntax::makeNode(NodeKind::None, at));
      call->add(syntax::makeNode(NodeKind::Name, at, mine));
    }
    auto contracts = syntax::makeNode(NodeKind::Contracts, at);
    for (const syntax::NodePtr &c : req.kids[2]->kids) {
      NodePtr copy = syntax::clone(*c);
      renameNames(*copy, rename, nullptr);
      contracts->add(std::move(copy));
    }
    auto item = syntax::makeNode(NodeKind::LetItem, at, symbol);
    if (!adlModule_.empty()) item->flags = "from:" + adlModule_;
    item->add(std::move(params));
    Node *ret = item->add(syntax::makeNode(NodeKind::RetAnnot, at));
    if (const Node *l = sema::findLender(*cur); l && l->flags == "region")
      ret->flags = "regions:" + l->text;
    Node *annot = ret->add(syntax::makeNode(NodeKind::Annot, at));
    annot->add(syntax::makeNode(NodeKind::Modifiers, at));
    annot->add(syntax::clone(*cur));
    annot->add(syntax::makeNode(NodeKind::None, at));
    ret->add(syntax::makeNode(NodeKind::Attrs, at));
    item->add(std::move(contracts));
    item->add(std::move(call));
    sema::FuncSig sig;
    sig.name = symbol;
    sig.item = item.get();
    sig.typeArgs = scope;
    for (auto &[name, type] : scope) sig.typeParams.push_back(name);
    if (via) sig.adapted = via->fns;
    synthesized_.push_back(std::move(item));
    if (!sema::resolveSignature(sig, types_, diags_)) return;
    sigs_.emplace(symbol, std::move(sig));
    pendingInstances_.push_back(symbol);
    queuedLog_.push_back(symbol);
  }

  // Renames free names in a contract; `result` becomes `call` when given.
  static void renameNames(Node &n, const std::map<std::string, std::string> &to,
                          const Node *call) {
    for (syntax::NodePtr &k : n.kids) {
      if (k->kind == NodeKind::Name && call && k->text == "result") {
        k = syntax::clone(*call);
        continue;
      }
      // A capture list names locals too, `[f, g]` (ADR 0044).
      if (k->kind == NodeKind::Name || k->kind == NodeKind::Capture)
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
    if (!adlModule_.empty()) item->flags += " from:" + adlModule_;
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
    queuedLog_.push_back(symbol);
  }

  // --- modules (ADR 0039) ---------------------------------------------

  // Checks the file's module header against the interfaces it claims, and
  // records what the module exports: the functions those interfaces list.
  // Everything else is private. A file with no header exports nothing but
  // its `main`.
  void checkModule(const Node &program) {
    const Node *header = nullptr;
    std::map<std::string, const Node *> interfaces;
    for (const syntax::NodePtr &item : program.kids) {
      if (item->kind == NodeKind::ModuleHeader) header = item.get();
      if (item->kind != NodeKind::Interface) continue;
      if (!interfaces.emplace(item->text, item.get()).second)
        diags_.error(item->loc,
                     "the interface '" + item->text + "' is already defined");
      checkInterfaceAttrs(*item);
    }
    // `main` is the program's entry point, and is never in an interface.
    for (const std::string &symbol : overloads_["main"])
      if (!sigs_.at(symbol).overloaded) {
        exports_[symbol] = header ? header->text : "";
        abiC_.insert(symbol);
      }
    if (!header) return;
    for (const syntax::NodePtr &a : header->kids[0]->kids)
      if (a->text != "trusted" || !a->kids.empty())
        diags_.error(a->loc, "unknown module attribute '@" + a->text +
                                 "'; a module header takes only @trusted");
    // The types the module's interfaces list, abstract or not. An exported
    // signature may name only these, so importers can always form it.
    std::set<std::string> shown;
    for (const syntax::NodePtr &path : header->kids[1]->kids)
      if (auto it = interfaces.find(path->text); it != interfaces.end())
        for (const syntax::NodePtr &item : it->second->kids) {
          const Node &r = *item;
          if (r.kind == NodeKind::SigType ||
              (r.kind == NodeKind::SigVal &&
               r.kids[0]->kids[1]->kind == NodeKind::TypeKind))
            shown.insert(r.text);
        }
    std::set<std::string> claimed;
    for (const syntax::NodePtr &path : header->kids[1]->kids) {
      if (!claimed.insert(path->text).second) {
        diags_.error(path->loc, "the module '" + header->text +
                                    "' claims the interface '" + path->text +
                                    "' twice");
        continue;
      }
      auto it = interfaces.find(path->text);
      if (it == interfaces.end()) {
        diags_.error(path->loc,
                     path->text.find('.') != std::string::npos
                         ? "the interface '" + path->text +
                               "' is in another module; a module can claim "
                               "only interfaces declared in its own file "
                               "for now"
                         : "no interface '" + path->text + "' in this file");
        continue;
      }
      checkInterface(*header, *it->second, shown);
    }
    std::vector<std::string> concepts;
    for (const syntax::NodePtr &path : header->kids[1]->kids)
      if (auto it = interfaces.find(path->text); it != interfaces.end())
        for (const syntax::NodePtr &r : it->second->kids)
          if (r->kind == NodeKind::SigVal && r->flags == "meta")
            concepts.push_back(r->text);
    proveExportedConcepts(concepts);
    // An exported function's symbols come from what the interfaces list,
    // never from private overloads (#204): a name exported once is linked
    // and entered by that name, and only a name exported with several
    // overloads carries the parameter types, as `f(u8)`.
    std::map<std::string, unsigned> listed;
    for (const auto &[symbol, path] : exports_) ++listed[sigs_.at(symbol).source()];
    for (const auto &[symbol, path] : exports_) {
      const std::string &name = sigs_.at(symbol).source();
      linkNames_[symbol] = listed[name] == 1 ? name : symbol;
    }
  }

  // `@abi(c)` and `@within(Prefix)` are an interface's attributes.
  void checkInterfaceAttrs(const Node &iface) {
    for (const syntax::NodePtr &a : attrsOf(iface).kids) {
      if (a->text == "abi" && a->kids.size() == 1 &&
          a->kids[0]->kind == NodeKind::Name && a->kids[0]->text == "c")
        continue;
      if (a->text == "within" && a->kids.size() == 1) continue;
      diags_.error(a->loc, a->text == "abi"
                               ? "@abi takes one argument, c"
                               : "unknown interface attribute '@" + a->text +
                                     "'; an interface takes @abi(c) and "
                                     "@within(...)");
    }
  }

  // An interface's attributes, which comments do not displace.
  static const Node &attrsOf(const Node &iface) {
    for (const syntax::NodePtr &k : iface.kids)
      if (k->kind == NodeKind::Attrs) return *k;
    return *iface.kids[0];
  }

  static bool hasAbiC(const Node &iface) {
    for (const syntax::NodePtr &a : attrsOf(iface).kids)
      if (a->text == "abi") return true;
    return false;
  }

  // The module meets each item its interface lists: a function or value
  // of exactly that type, with a contract at least as strong (proved, as a
  // concept's requirement is), a type for `let t : type`, and the same
  // definition for `let t = type ...`.
  void checkInterface(const Node &header, const Node &iface,
                      const std::set<std::string> &shown) {
    const std::string key = header.text + "." + iface.text;
    std::string outer =
        std::exchange(requirer_, "the interface '" + iface.text + "'");
    struct Restore {
      std::string &to, from;
      ~Restore() { to = std::move(from); }
    } restore{requirer_, std::move(outer)};
    std::string unmet =
        "the module '" + header.text + "' does not meet '" + iface.text + "': ";
    for (const syntax::NodePtr &item : iface.kids) {
      const Node &r = *item;
      if (r.kind == NodeKind::Hole) {
        diags_.error(r.loc, "the interface '" + iface.text +
                                "' is unfinished ('...')");
        continue;
      }
      if (r.kind == NodeKind::SigType) {
        if (std::optional<std::string> name = privateType(*r.kids[0], shown))
          diags_.error(r.loc, "the type '" + r.text + "' is shown, but its "
                                  "definition names '" + *name + "', which "
                                  "no interface of '" + header.text +
                                  "' lists");
        const Node *own = typeItem(r.text);
        if (!own)
          diags_.error(r.loc, unmet + "no type '" + r.text + "'");
        else if (!sameTree(*own->kids[3], *r.kids[0]))
          diags_.error(r.loc, unmet + "the type '" + r.text +
                                  "' is defined differently; an interface "
                                  "that shows a type with '=' must show its "
                                  "definition exactly");
        continue;
      }
      if (r.kind != NodeKind::SigVal) continue;
      // `let meta C : concept`: the concept, exported with its definition.
      // `let meta m : item` (any other result): a metaprogram, which
      // expansion has run and removed; the expander checks it is defined.
      if (r.flags == "meta") {
        const Node &t = *r.kids[0]->kids[1];
        if (t.kind == NodeKind::TypeName && t.text != "concept")
          continue;
        if (!concepts_.count(r.text))
          diags_.error(r.loc, unmet + "no concept '" + r.text + "'");
        continue;
      }
      const Node &type = *r.kids[0]->kids[1];
      // `let spec f : ...`: a spec function, exported with its definition
      // so importers reason with its body; codegen erases it, so it has
      // no link symbol.
      if (r.flags == "spec") {
        if (std::optional<std::string> name = privateType(type, shown))
          diags_.error(r.loc, "'" + r.text + "' is exported, but its type "
                                  "names '" + *name + "', which no "
                                  "interface of '" + header.text + "' lists");
        bool found = false;
        for (const std::string &symbol : overloads_[r.text])
          found = found || (sigs_.at(symbol).item &&
                            hasFlag(*sigs_.at(symbol).item, "spec") &&
                            sameSignature(r, *sigs_.at(symbol).item));
        // A spec function over function values, such as a law (ADR 0044).
        if (auto h = hofs_.find(r.text); h != hofs_.end())
          for (const sema::FuncSig &f : h->second)
            found = found || (hasFlag(*f.item, "spec") &&
                              sameSignature(r, *f.item));
        if (!found)
          diags_.error(r.loc, unmet + "no spec function '" + r.text +
                                  "' with exactly this signature; a spec "
                                  "function is exported with its definition, "
                                  "so its interface entry repeats its "
                                  "parameters and result");
        continue;
      }
      // A generic function is exported with its definition, which
      // importers instantiate, so the interface repeats its signature and
      // contract exactly.
      if (isGenericSig(type)) {
        if (std::optional<std::string> name = privateType(type, shown))
          diags_.error(r.loc, "'" + r.text + "' is exported, but its type "
                                  "names '" + *name + "', which no "
                                  "interface of '" + header.text + "' lists");
        bool found = false;
        for (const std::string &symbol : overloads_[r.text])
          found = found || (sigs_.at(symbol).isGeneric() &&
                            sameSignature(r, *sigs_.at(symbol).item));
        if (auto h = hofs_.find(r.text); h != hofs_.end())
          for (const sema::FuncSig &f : h->second)
            found = found || (f.isGeneric() && sameSignature(r, *f.item));
        if (!found)
          diags_.error(r.loc, unmet + "no generic function '" + r.text +
                                  "' with exactly this signature; a generic "
                                  "function is exported with its definition, "
                                  "so its interface entry repeats its "
                                  "parameters and result");
        continue;
      }
      if (type.kind == NodeKind::TypeKind) {
        if (!types_.named(r.text) && !typeItem(r.text))
          diags_.error(r.loc, unmet + "no type '" + r.text + "'");
        continue;
      }
      if (auto c = consts_.find(r.text); c != consts_.end()) {
        if (types_.resolve(type) != Type(c->second.type))
          diags_.error(r.loc, unmet + "'" + r.text + "' has type " +
                                  typeName(c->second.type));
        continue;
      }
      if (std::optional<std::string> name = privateType(type, shown))
        diags_.error(r.loc, "'" + r.text + "' is exported, but its type "
                                "names '" + *name + "', which no interface "
                                "of '" + header.text + "' lists");
      std::string symbol;
      if (std::optional<std::string> why =
              sigValUnmet(r, key, {}, nullptr, &symbol, /*strict=*/true)) {
        diags_.error(r.loc, unmet + *why);
        continue;
      }
      // `let lemma f : ...`: proved here, and a fact to importers, who call
      // it as one: its precondition a goal, its postcondition assumed. It
      // has no code, so no link symbol (#305).
      if (r.flags == "lemma" || hasFlag(*sigs_.at(symbol).item, "lemma")) {
        if (r.flags != "lemma" || !hasFlag(*sigs_.at(symbol).item, "lemma"))
          diags_.error(
              r.loc,
              unmet + "'" + r.text + "' is " +
                  (r.flags == "lemma"
                       ? "listed as a lemma but defined as a function"
                       : "a lemma, so the interface lists it as 'let lemma'"));
        continue;
      }
      // `let n : u32 = 4096`: importers get the value from the interface,
      // so it must be the definition's.
      if (r.kids.size() > 3) {
        const Node &own = *sigs_.at(symbol).item;
        if (!own.kids[0]->kids.empty() || own.kids.size() < 4 ||
            !sameTree(*own.kids[3], *r.kids[3]))
          diags_.error(r.loc, unmet + "'" + r.text + "' is defined "
                                  "differently; an interface that shows a "
                                  "value with '=' must show its definition "
                                  "exactly");
      }
      if (sigs_.at(symbol).isGeneric() || !sigs_.at(symbol).typeArgs.empty())
        continue;
      // A function in a C interface keeps its C name.
      exports_.emplace(symbol, header.text);
      if (hasAbiC(iface)) abiC_.insert(symbol);
    }
  }

  // Whether a signature's type takes a type parameter, `(t : type) -> ...`.
  static bool isGenericSig(const Node &type) {
    for (const Node *cur = &type; cur->kind == NodeKind::ArrowType;
         cur = cur->kids[1].get())
      if (cur->kids[0]->kids.size() > 1 &&
          cur->kids[0]->kids[1]->kind == NodeKind::TypeKind)
        return true;
    return false;
  }

  // Whether `let f : (a : t) -> r` in a sig has exactly the parameters
  // and result of the definition `let f (a : t) : r = ...`.
  static bool sameSignature(const Node &sigVal, const Node &def) {
    const Node *cur = sigVal.kids[0]->kids[1].get();
    const Node &params = *def.kids[0];
    auto none = [](const Node *n) { return !n || n->kind == NodeKind::None; };
    for (const syntax::NodePtr &p : params.kids) {
      if (p->kind != NodeKind::Param || cur->kind != NodeKind::ArrowType ||
          p->kids.empty())
        return false;
      const Node &dom = *cur->kids[0];
      const Node &annot = *p->kids[0];
      // A spec parameter is erased at the call, so both must agree on it
      // (ADR 0058).
      if ((dom.flags == "spec") != (p->flags == "spec")) return false;
      if (dom.text != p->text || dom.kids.size() < 2 || annot.kids.size() < 2 ||
          !sameTree(*dom.kids[0], *annot.kids[0]) ||
          !sameTree(*dom.kids[1], *annot.kids[1]))
        return false;
      const Node *w1 = dom.kids.size() > 2 ? dom.kids[2].get() : nullptr;
      const Node *w2 = annot.kids.size() > 2 ? annot.kids[2].get() : nullptr;
      if (none(w1) != none(w2) || (!none(w1) && !sameTree(*w1, *w2)))
        return false;
      cur = cur->kids[1].get();
    }
    if (cur->kind == NodeKind::ArrowType) return false;
    const Node &ret = *def.kids[1];
    if (ret.kind != NodeKind::RetAnnot || ret.kids.empty() ||
        ret.kids[0]->kids.size() < 2 || !sameTree(*ret.kids[0]->kids[1], *cur))
      return false;
    // Importers get the definition's contract with its body, so the
    // interface's copy is documentation; the artifact holds the real one.
    return true;
  }

  static bool hasEnsures(const Node &sigVal) {
    for (const syntax::NodePtr &c : sigVal.kids[2]->kids)
      if (c->kind == NodeKind::Ensures) return true;
    return false;
  }

  // Whether a function type has an `out`, `inout` or `mutable` parameter.
  static bool writesParam(const Node &type) {
    for (const Node *cur = &type; cur->kind == NodeKind::ArrowType;
         cur = cur->kids[1].get()) {
      const std::string &mods = cur->kids[0]->kids[0]->text;
      if (sema::hasModifier(mods, "out") || sema::hasModifier(mods, "inout") ||
          sema::hasModifier(mods, "mutable"))
        return true;
    }
    return false;
  }

  // A type of this program that `type` names and no interface lists. A
  // qualified name, `M.t`, is a type imported from another module's
  // interface, so it is already public there (ADR 0039).
  std::optional<std::string> privateType(const Node &type,
                                         const std::set<std::string> &shown) {
    if ((type.kind == NodeKind::TypeName || type.kind == NodeKind::TypeInst) &&
        typeItem(type.text) && !shown.count(type.text) &&
        type.text.find('.') == std::string::npos)
      return type.text;
    for (const syntax::NodePtr &k : type.kids)
      if (std::optional<std::string> name = privateType(*k, shown))
        return name;
    return std::nullopt;
  }

  // The top-level `let t = type ...` named `name`, if any.
  const Node *typeItem(const std::string &name) const {
    for (const auto &[n, item] : typeItems_)
      if (n == name) return item;
    return nullptr;
  }

  // Whether two trees are the same apart from locations and comments.
  static bool sameTree(const Node &a, const Node &b) {
    if (a.kind != b.kind || a.text != b.text || a.flags != b.flags)
      return false;
    auto code = [](const Node &n) {
      std::vector<const Node *> out;
      for (const syntax::NodePtr &k : n.kids)
        if (k->kind != NodeKind::Comment) out.push_back(k.get());
      return out;
    };
    std::vector<const Node *> x = code(a), y = code(b);
    if (x.size() != y.size()) return false;
    for (size_t i = 0; i < x.size(); ++i)
      if (!sameTree(*x[i], *y[i])) return false;
    return true;
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
    AdlScope adl(adlModule_, fromModule(*generic.item));
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
      promisedArgs_.clear();
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
    size_t errors = diags_.count();
    bool generated = false;
    if (sema::resolveSignature(check, types_, diags_) && !opaqueStandIn_) {
      sigs_.emplace(key, std::move(check));
      genFunction(key);
      generated = true;
    }
    // A body that passed the check is proved once, over its type
    // parameters as uninterpreted sorts, when it is parametric (ADR 0043,
    // step 1). Otherwise only its instances are proved, and the report
    // says why.
    std::set<std::string> kept;
    if (generated && diags_.count() == errors)
      keepGenericProof(generic, key, bound, pending, kept);
    else if (generated || opaqueStandIn_)
      notParametric(generic, "its signature applies a type-level "
                             "metaprogram to a type parameter");
    checking_ = false;
    // Nothing else the check made survives it.
    if (!kept.count(key))
      if (auto f = module_.lookupSymbol<mlir::func::FuncOp>(key)) f.erase();
    for (auto it = sigs_.begin(); it != sigs_.end();)
      it = before.count(it->first) || kept.count(it->first)
               ? std::next(it)
               : sigs_.erase(it);
    pendingInstances_.resize(pending);
    met_ = std::move(savedMet);
    promised_.clear();
      promisedArgs_.clear();
    promisedFns_.clear();
    promisedSigs_.clear();
    archetypes_.clear();
  }

  // --- generic proofs (ADR 0043, step 1) ------------------------------

  // `a = b` for values of the stand-in type `t`: a call of `pia.eq<t>`,
  // which the verifier encodes as equality in t's sort (ADR 0043).
  Value standInEq(Location l, Value a, Value b, Type t) {
    std::string name = "pia.eq<" + typeName(t) + ">";
    if (!module_.lookupSymbol<mlir::func::FuncOp>(name)) {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPointToEnd(module_.getBody());
      auto f = create<mlir::func::FuncOp>(l, name,
                                          b_.getFunctionType({t, t}, {b_.getI1Type()}));
      f.setPrivate();
      f->setAttr(PiaDialect::getSpecAttrName(), b_.getUnitAttr());
      f->setAttr("pia.generic_eq", b_.getUnitAttr());
      f->setAttr("pia.generic_proof", b_.getStringAttr("="));
    }
    return create<mlir::func::CallOp>(l, name, mlir::TypeRange{b_.getI1Type()},
                                      mlir::ValueRange{a, b})
        .getResult(0);
  }

  // Records why `generic` is proved only at its instances, for the report.
  void notParametric(const sema::FuncSig &generic, const std::string &why) {
    for (const NotParametric &n : notParametric_)
      if (n.generic == generic.name) return;
    syntax::SourceLoc at = generic.item->loc;
    notParametric_.push_back(
        {file_.str() + ":" + std::to_string(at.line) + ":" +
             std::to_string(at.column),
         generic.name, why});
  }

  // Why the function `f`, made at stand-in types, is not one the verifier
  // can prove over sorts, or empty. Values of a type parameter may only be
  // passed on, stored in and loaded from buffers, chosen between by `if`,
  // and given to the concepts' functions.
  std::string notAbstract(mlir::func::FuncOp f) {
    auto plain = [&](Type t) -> bool {
      if (!t) return true;
      if (standIns_.contains(t)) return true;
      if (mlir::isa<RecordType>(t)) return false;
      if (auto a = mlir::dyn_cast<ArrayType>(t))
        return standIns_.contains(a.getElementType()) ||
               !mlir::isa<RecordType>(a.getElementType());
      if (auto sl = mlir::dyn_cast<SliceType>(t))
        return standIns_.contains(sl.getElementType()) ||
               !mlir::isa<RecordType>(sl.getElementType());
      return true;
    };
    auto touches = [&](Type t) -> bool {
      if (standIns_.contains(t)) return true;
      if (auto a = mlir::dyn_cast<ArrayType>(t))
        return standIns_.contains(a.getElementType());
      if (auto sl = mlir::dyn_cast<SliceType>(t))
        return standIns_.contains(sl.getElementType());
      return false;
    };
    std::string why;
    for (Type t : f.getArgumentTypes())
      if (!plain(t)) why = "it takes a value of " + typeName(t);
    for (Type t : f.getResultTypes())
      if (!plain(t)) why = "it returns a value of " + typeName(t);
    if (!why.empty()) return why;
    f.walk([&](mlir::Operation *op) {
      if (!why.empty()) return;
      for (Type t : op->getResultTypes())
        if (!plain(t)) why = "it makes a value of " + typeName(t);
      for (Type t : op->getOperandTypes())
        if (!plain(t)) why = "it uses a value of " + typeName(t);
      if (!why.empty()) return;
      bool abstract = llvm::any_of(op->getOperandTypes(), touches) ||
                      llvm::any_of(op->getResultTypes(), touches);
      if (!abstract) return;
      if (mlir::isa<mlir::func::CallOp, mlir::func::ReturnOp,
                    mlir::scf::IfOp, mlir::scf::YieldOp, mlir::scf::WhileOp,
                    mlir::scf::ConditionOp, mlir::scf::ForOp, LoadOp,
                    StoreOp, SliceOp, LenOp>(op))
        return;
      if (op->getDialect() &&
          op->getDialect()->getNamespace() == "pia_contract")
        return;
      why = "it applies '" + op->getName().getStringRef().str() +
            "' to a value of a type parameter";
    });
    return why;
  }

  // Keeps the check's body of `generic`, made at the stand-ins `bound`, as
  // its generic proof: the instances it made at the stand-ins, each
  // requirement of its constraints as an uninterpreted function, and each
  // requirement's contract as an axiom about it. The use check proves
  // every requirement contract at every type that meets the concept, so
  // the axioms hold of every instance. Laws wait for step 3. `pending` is
  // where the check's queued instances start; `kept` gets the symbols that
  // survive.
  void keepGenericProof(const sema::FuncSig &generic, const std::string &key,
                        const std::map<std::string, Type> &bound,
                        size_t pending, std::set<std::string> &kept) {

    for (const syntax::NodePtr &p : generic.item->kids[0]->kids)
      if (const Node *pred = wherePredicate(*p)) {
        std::vector<const Node *> cs, preds;
        constraintsOf(*pred, cs, &preds);
        if (!preds.empty()) {
          notParametric(generic, "a 'where' predicate that is not a concept "
                                 "constrains '" + p->text + "'");
          return;
        }
      }
    for (const sema::FuncSig &r : promisedSigs_) {
      // A requirement's precondition is a goal at each call in the body
      // (genCall), and its axiom holds where the precondition does.
      if (!r.result || mlir::isa<RecordType>(r.result) &&
                           !standIns_.contains(r.result)) {
        notParametric(generic, "the requirement '" + r.name +
                                   "' returns a record");
        return;
      }
    }
    std::vector<std::string> made = {key};
    // The instances the body made at the stand-ins are part of its proof;
    // the laws and contracts queued for the stand-ins are not proved, they
    // are what the proof assumes.
    for (size_t i = pending; i < pendingInstances_.size(); ++i) {
      std::string k = pendingInstances_[i];
      auto it = sigs_.find(k);
      if (it == sigs_.end()) continue;
      // A concept's law or requirement contract at the stand-ins, such as
      // `Ord<t>.irreflexive`, is assumed, not proved; a generic lemma's
      // instance at them is part of the proof.
      if (hasFlag(*it->second.item, "lemma") &&
          promised_.count(llvm::StringRef(k).split('.').first.str()))
        continue;
      if (module_.lookupSymbol<mlir::func::FuncOp>(k)) continue;
      size_t errors = diags_.count();
      genFunction(k);
      made.push_back(k);
      if (diags_.count() != errors) return dropProof(generic, made, errors);
    }
    // Each requirement: an uninterpreted function of the concept's theory,
    // `Ord<t>.less`, and its contract as that theory's axiom.
    std::vector<std::string> &decls = made;
    for (const sema::FuncSig &r : promisedSigs_) {
      // The concept at the stand-ins, `Pia.Core.Order.Ord<t>`: the name
      // up to its requirement.
      std::string theory = llvm::StringRef(r.name).rsplit('.').first.str();
      if (!module_.lookupSymbol<mlir::func::FuncOp>(r.name)) {
        llvm::SmallVector<Type> ins;
        for (const sema::Param &p : r.params) ins.push_back(p.type);
        llvm::SmallVector<Type> outs;
        if (!isUnit(r.result)) outs.push_back(r.result);
        b_.setInsertionPointToEnd(module_.getBody());
        auto f = create<mlir::func::FuncOp>(loc(*r.item), r.name,
                                            b_.getFunctionType(ins, outs));
        f.setPrivate();
        f->setAttr(PiaDialect::getSpecAttrName(), b_.getUnitAttr());
        f->setAttr(PiaDialect::getAbstractAttrName(), b_.getUnitAttr());
        f->setAttr("pia.theory", b_.getStringAttr(theory));
        f->setAttr("pia.generic_proof", b_.getStringAttr(generic.name));
        decls.push_back(r.name);
      } else if (!llvm::is_contained(decls, r.name)) {
        // Another generic's proof declared it: shared, and kept by it.
      }
      std::string axiom = r.name + ".contract";
      // A requirement with only a precondition has no fact to assume: its
      // precondition is a goal at each call.
      bool ensures = false;
      for (const syntax::NodePtr &c : r.item->kids[2]->kids)
        ensures |= c->kind == NodeKind::Ensures;
      if (!ensures || sigs_.count(axiom)) continue;
      size_t errors = diags_.count();
      if (!queueRequirementAxiom(r, axiom, bound)) {
        made.push_back(axiom);
        return dropProof(generic, made, errors);
      }
      genFunction(axiom);
      made.push_back(axiom);
      if (diags_.count() != errors) return dropProof(generic, made, errors);
    }
    // Each law of each concept the constraints promise, as an axiom of the
    // concept's theory (ADR 0043, step 3): the use check proves every law
    // at every type that meets the concept.
    for (auto &[key, ca] : promisedArgs_) {
      auto c = concepts_.find(ca.first);
      if (c == concepts_.end()) continue;
      const Node &item = *c->second;
      std::map<std::string, Type> scope;
      size_t i = 0;
      for (const syntax::NodePtr &p : item.kids[0]->kids)
        if (sema::isTypeParam(*p) && i < ca.second.size())
          scope[p->text] = ca.second[i++];
      for (const syntax::NodePtr &r : item.kids[3]->kids) {
        if (r->kind != NodeKind::SigLemma) continue;
        std::string axiom = key + "." + r->text + ".law";
        if (sigs_.count(axiom) || module_.lookupSymbol<mlir::func::FuncOp>(axiom))
          continue;
        size_t errors = diags_.count();
        if (!queueLawAxiom(axiom, *r, scope)) {
          made.push_back(axiom);
          return dropProof(generic, made, errors);
        }
        genFunction(axiom);
        if (diags_.count() != errors) {
          made.push_back(axiom);
          return dropProof(generic, made, errors);
        }
        // A law the solver could not instantiate is left out: the proof
        // then assumes less, which is sound.
        if (auto f = module_.lookupSymbol<mlir::func::FuncOp>(axiom)) {
          verify::AxiomTriggers t = verify::axiomTriggers(module_, f);
          if (t.triggers.empty()) {
            f.erase();
            continue;
          }
        }
        made.push_back(axiom);
      }
    }
    for (const std::string &m : made) {
      auto f = module_.lookupSymbol<mlir::func::FuncOp>(m);
      if (!f) return;
      if (f.isExternal()) continue;
      std::string why = notAbstract(f);
      if (!why.empty()) {
        for (const std::string &k : made)
          if (k != key)
            if (auto g = module_.lookupSymbol<mlir::func::FuncOp>(k)) g.erase();
        notParametric(generic, why);
        return;
      }
    }
    // An imported generic was proved over sorts by its own module, which a
    // build of it requires (ADR 0039: an exported generic is checked once,
    // in its module). Its proof is kept here only so that instances can be
    // matched against it; it is not proved again.
    bool imported = llvm::StringRef(generic.item->flags).contains("from:");
    // The theories a proof may use: the concepts its constraints promise.
    llvm::SmallVector<mlir::Attribute> concepts;
    for (auto &[key, ca] : promisedArgs_) concepts.push_back(b_.getStringAttr(key));
    for (const std::string &m : made) {
      auto f = module_.lookupSymbol<mlir::func::FuncOp>(m);
      if (!f->hasAttr("pia.generic_proof"))
        f->setAttr("pia.generic_proof", b_.getStringAttr(generic.name));
      if (imported && !f.isExternal() &&
          !f->hasAttr(PiaDialect::getAxiomAttrName()))
        f->setAttr("pia.generic_imported", b_.getUnitAttr());
      // An axiom belongs to its concept's theory, named in full.
      if (f->hasAttr(PiaDialect::getAxiomAttrName())) {
        llvm::StringRef n = f.getSymName();
        // `Pia.Core.Order.Ord<t>.less.contract`, `...Ord<t>.irreflexive.law`.
        llvm::StringRef theory = n.rsplit('.').first.rsplit('.').first;
        f->setAttr("pia.theory", b_.getStringAttr(theory));
      } else if (!f.isExternal()) {
        f->setAttr("pia.concepts", b_.getArrayAttr(concepts));
      }
      kept.insert(m);
    }
  }

  // Gives up the generic proof of `generic`: erases what it made but its
  // definition body, which the caller erases, and drops the errors after
  // the first `errors`, which only meant the proof cannot be made.
  void dropProof(const sema::FuncSig &generic,
                 const std::vector<std::string> &made, size_t errors) {
    std::string why = "it cannot be generated over its type parameters";
    if (diags_.count() > errors) why += ": " + diags_.errors()[errors].message;
    diags_.truncate(errors);
    for (size_t i = 1; i < made.size(); ++i)
      if (auto g = module_.lookupSymbol<mlir::func::FuncOp>(made[i])) g.erase();
    notParametric(generic, why);
  }

  // The law `r` of a concept, `let lemma name (params) requires ...
  // ensures ...`, as the axiom `name` at the stand-ins `scope`.
  bool queueLawAxiom(const std::string &name, const Node &r,
                     const std::map<std::string, Type> &scope) {
    syntax::SourceLoc at = r.loc;
    auto item = syntax::makeNode(NodeKind::LetItem, at, name);
    item->flags = "axiom theory";
    item->add(syntax::clone(*r.kids[0]));
    Node *ret = item->add(syntax::makeNode(NodeKind::RetAnnot, at));
    Node *annot = ret->add(syntax::makeNode(NodeKind::Annot, at));
    annot->add(syntax::makeNode(NodeKind::Modifiers, at));
    annot->add(syntax::makeNode(NodeKind::TypeName, at, "unit"));
    annot->add(syntax::makeNode(NodeKind::None, at));
    Node *attrs = ret->add(syntax::makeNode(NodeKind::Attrs, at));
    // A law whose hypotheses chain calls, such as transitivity's `less a b`
    // and `less b c`, is triggered by all of them together: one pattern of
    // the calls its `requires` makes (ADR 0036, "Triggers").
    std::vector<const Node *> calls;
    std::function<void(const Node &)> collect = [&](const Node &n) {
      if (n.kind == NodeKind::Apply && !n.kids.empty() &&
          n.kids[0]->kind == NodeKind::Name && promisedFns_.count(n.kids[0]->text)) {
        calls.push_back(&n);
        return;
      }
      for (const syntax::NodePtr &k : n.kids) collect(*k);
    };
    for (const syntax::NodePtr &c : r.kids[1]->kids)
      if (c->kind == NodeKind::Requires) collect(*c);
    if (calls.size() > 1) {
      Node *trig = attrs->add(syntax::makeNode(NodeKind::Attribute, at, "trigger"));
      for (const Node *c : calls) trig->add(syntax::clone(*c));
    }
    item->add(syntax::clone(*r.kids[1]));
    item->add(syntax::makeNode(NodeKind::Unit, at));
    sema::FuncSig sig;
    sig.name = name;
    sig.item = item.get();
    sig.typeArgs = scope;
    for (auto &[n, t] : scope) sig.typeParams.push_back(n);
    synthesized_.push_back(std::move(item));
    if (!sema::resolveSignature(sig, types_, diags_)) return false;
    sigs_.emplace(name, std::move(sig));
    return true;
  }

  // The axiom `name` about the requirement `r` at the stand-ins `scope`:
  // `forall params. requires ==> ensures`, with `result` as the call.
  bool queueRequirementAxiom(const sema::FuncSig &r, const std::string &name,
                             const std::map<std::string, Type> &scope) {
    const Node &req = *r.item;
    syntax::SourceLoc at = req.loc;
    auto item = syntax::makeNode(NodeKind::LetItem, at, name);
    item->flags = "axiom theory";
    Node *params = item->add(syntax::makeNode(NodeKind::Params, at));
    auto call = syntax::makeNode(NodeKind::Apply, at);
    call->add(syntax::makeNode(NodeKind::Name, at, req.text));
    const Node *cur = req.kids[0]->kids[1].get();
    std::vector<std::string> names;
    for (; cur->kind == NodeKind::ArrowType; cur = cur->kids[1].get()) {
      const Node &d = *cur->kids[0];
      if (d.text.empty()) return false;
      names.push_back(d.text);
      Node *p = params->add(syntax::makeNode(NodeKind::Param, at, d.text));
      Node *annot = p->add(syntax::makeNode(NodeKind::Annot, at));
      annot->add(syntax::makeNode(NodeKind::Modifiers, at));
      annot->add(syntax::clone(*d.kids[1]));
      annot->add(syntax::makeNode(NodeKind::None, at));
      call->add(syntax::makeNode(NodeKind::Name, at, d.text));
    }
    Node *ret = item->add(syntax::makeNode(NodeKind::RetAnnot, at));
    Node *annot = ret->add(syntax::makeNode(NodeKind::Annot, at));
    annot->add(syntax::makeNode(NodeKind::Modifiers, at));
    annot->add(syntax::makeNode(NodeKind::TypeName, at, "unit"));
    annot->add(syntax::makeNode(NodeKind::None, at));
    ret->add(syntax::makeNode(NodeKind::Attrs, at));
    auto contracts = syntax::makeNode(NodeKind::Contracts, at);
    for (const syntax::NodePtr &c : req.kids[2]->kids) {
      NodePtr copy = syntax::clone(*c);
      renameNames(*copy, {}, c->kind == NodeKind::Ensures ? call.get() : nullptr);
      contracts->add(std::move(copy));
    }
    item->add(std::move(contracts));
    item->add(syntax::makeNode(NodeKind::Unit, at));
    sema::FuncSig sig;
    sig.name = name;
    sig.item = item.get();
    sig.typeArgs = scope;
    for (auto &[n, t] : scope) sig.typeParams.push_back(n);
    synthesized_.push_back(std::move(item));
    if (!sema::resolveSignature(sig, types_, diags_)) return false;
    sigs_.emplace(name, std::move(sig));
    return true;
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
      promisedArgs_.clear();
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
    promisedArgs_[key] = {cname, args};
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
        param.regions = regionsOfFlags(d.flags);
        ok = ok && param.type;
        sig.params.push_back(std::move(param));
      }
      sig.result = types_.resolve(*cur);
      if (!ok || !sig.result) continue;
      // `borrowed(r)` of the concept's region r (ADR 0042, step 2).
      if (const Node *l = sema::findLender(*cur); l && l->flags == "region") {
        const Node &lent = *sema::findLentAnnot(*cur);
        sig.lentType = types_.resolveAnnot(lent);
        sig.lentModifiers = lent.kids[0]->text;
        sig.lentFromRegion = true;
        sig.resultRegions = {l->text};
      }
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
      // A generic lambda's instance infers what it returns.
      if (!inst.result && !retAnnotOf(generic) &&
          llvm::StringRef(generic.name).starts_with("lambda@") &&
          !inferResult(inst, *generic.item))
        return nullptr;
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
    std::vector<size_t> through = threaded(sig);
    for (size_t i : through) results.push_back(sig.params[i].type);
    auto call = create<mlir::func::CallOp>(loc(n), sig.name, results,
                                              operands);
    threadedResults_.clear();
    for (size_t k = 0; k < through.size(); ++k)
      threadedResults_.push_back(
          call.getResult(results.size() - through.size() + k));
    if (unsafeAt_ == &n) call->setAttr("pia.unsafe", b_.getUnitAttr());
    // A call left open between overloads told apart by their
    // preconditions: the verifier chooses (verify::resolveOverloads).
    if (openCandidates_ && sig.name == openFor_) {
      call->setAttr("pia.overload_candidates", openCandidates_);
      openCandidates_ = {};
    }
    if (isUnit(sig.result)) return unit();
    return TV{call.getResult(0), sig.result};
  }

  // The parameters whose final values a call hands back: `inout` or `out`
  // ones that are not buffers. A buffer is written in place; a scalar or a
  // record is an SSA value, so the callee returns its new value after its
  // result, and the caller rebinds its variable to it.
  static std::vector<size_t> threaded(const sema::FuncSig &sig) {
    std::vector<size_t> out;
    for (size_t i = 0; i < sig.params.size(); ++i) {
      const sema::Param &p = sig.params[i];
      if ((sema::hasModifier(p.modifiers, "inout") ||
           sema::hasModifier(p.modifiers, "out")) &&
          p.type && !mlir::isa<ArrayType, SliceType>(p.type))
        out.push_back(i);
    }
    return out;
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
    // A type parameter's stand-in has no fields, so field by field it would
    // always equal itself: in a generic's proof its values are equal only
    // when they are the same element of its sort (ADR 0043).
    if (checking_ && standIns_.contains(t)) return standInEq(l, a, b, t);
    if (mlir::isa<IntType>(t)) return cmp(l, CmpPredicate::eq, a, b);
    if (mlir::isa<UnboundedIntType, RealType, SortType>(t))
      return create<ExactCmpOp>(l, b_.getI1Type(),
                                CmpPredicateAttr::get(&ctx_, CmpPredicate::eq),
                                a, b);
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
    unconsume(*n.kids[0]);
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
    if (spread_ && n.kids[0]->kind == NodeKind::Name)
      if (BindingPtr b = lookup(n.kids[0]->text))
        if (!ownedHere(n, b, *idx, false))
          return std::nullopt;
    Value v = create<LoadOp>(loc(n), elem, buf->value, *idx);
    if (!contract_ && !ghost_ && ownsSlices(elem))
      noteMoveOut(n, buf->value, *idx, v, elem);
    return TV{v, elem};
  }

  // `xs.[i]` read as a value moves the element out when it owns slices,
  // as a box does (ADR 0048, section 6): the element left behind keeps
  // empty slices, so it owns nothing and its old slots are the moved
  // value's alone. The emptying store is spec-only; codegen erases it. A
  // read that turns out to be a borrow, `xs.[i].slot`, undoes it
  // (`unconsume`).
  void noteMoveOut(const Node &n, Value buf, Value idx, Value v, Type elem) {
    const Node &place = *n.kids[0];
    if (!writable(place) && !writablePath(place)) {
      copiedOut_[&n] = n.loc;
      return;
    }
    Location l = loc(n);
    auto store = create<StoreOp>(l, emptied(l, v, elem), buf, idx);
    store->setAttr("pia.moved_out", b_.getUnitAttr());
    movedOut_[&n] = store;
  }

  // `v` with every slice it holds, directly or in a field, empty.
  Value emptied(Location l, Value v, Type t) {
    if (mlir::isa<SliceType>(t)) {
      Value zero = create<mlir::arith::ConstantIndexOp>(l, 0);
      return create<SliceOp>(l, t, v, zero, zero);
    }
    auto rt = mlir::dyn_cast<RecordType>(t);
    if (!rt || types_.isVariant(rt) || !holdsSlice(t))
      return v;
    llvm::SmallVector<Value> fields;
    for (auto [ft, name] : llvm::zip(rt.getFieldTypes(), rt.getFieldNames()))
      fields.push_back(emptied(l, create<FieldOp>(l, ft, v, name), ft));
    return create<RecordOp>(l, rt, fields);
  }

  static bool holdsSlice(Type t) {
    if (mlir::isa<SliceType>(t))
      return true;
    if (auto rt = mlir::dyn_cast<RecordType>(t))
      return llvm::any_of(rt.getFieldTypes(), holdsSlice);
    return false;
  }

  // An element read only to be borrowed was not moved out: erase the
  // emptying store and what fed it.
  void keepElement(const Node &n) {
    copiedOut_.erase(&n);
    auto m = movedOut_.find(&n);
    if (m == movedOut_.end())
      return;
    mlir::Operation *store = m->second;
    movedOut_.erase(m);
    // The store, then each record, field read, view and constant made
    // only for it, once nothing else uses it.
    llvm::SmallVector<mlir::Operation *> work{store};
    llvm::SmallPtrSet<mlir::Operation *, 8> erased;
    while (!work.empty()) {
      mlir::Operation *op = work.pop_back_val();
      if (erased.count(op) || !op->use_empty())
        continue;
      llvm::SmallVector<mlir::Operation *> feeds;
      for (Value o : op->getOperands())
        if (mlir::Operation *d = o.getDefiningOp();
            d &&
            mlir::isa<RecordOp, FieldOp, SliceOp, mlir::arith::ConstantIndexOp>(
                d))
          feeds.push_back(d);
      erased.insert(op);
      op->erase();
      for (mlir::Operation *d : feeds)
        if (!erased.count(d))
          work.push_back(d);
    }
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

  // `rec` with the field at `path[at..]` replaced by `v`.
  Value withField(Location l, Value rec, const std::vector<std::string> &path,
                  size_t at, Value v) {
    if (at == path.size()) return v;
    auto rt = mlir::cast<RecordType>(rec.getType());
    llvm::SmallVector<Value> fields;
    for (auto [name, ft] : llvm::zip(rt.getFieldNames(), rt.getFieldTypes())) {
      Value f = create<FieldOp>(l, ft, rec, name);
      fields.push_back(name.getValue() == path[at]
                           ? withField(l, f, path, at + 1, v)
                           : f);
    }
    return create<RecordOp>(l, rt, fields);
  }

  R genField(const Node &n) {
    R obj = genExpr(*n.kids[0], Type());
    if (!obj) return obj;
    unconsume(*n.kids[0]);
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
    if (!writableBuffer(*b))
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
      if (!usable(b, obj)) return std::nullopt;
      auto rt = mlir::dyn_cast<RecordType>(b->type);
      if (!rt)
        return fail(place, "'." + place.text + "' needs a record, found " +
                               typeName(b->type));
      if (!b->isMutable)
        return fail(obj, "'" + obj.text + "' is not mutable; declare it "
                         "as 'let " + obj.text + " : mutable T = ...'");
      if (!notLent(b, obj, "assigned")) return std::nullopt;
      std::optional<unsigned> i = rt.fieldIndex(place.text);
      struct AddLenders {
        Gen &g;
        BindingPtr b;
        const Node &v;
        ~AddLenders() { addLenders(b->lenders, g.lendersOf(v)); }
      } addAfter{*this, b, valueNode};
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
      if (b->spec && !isSpecScalar(b->type))
        return fail(place, "assigning a whole spec array is not supported "
                           "yet; write its elements");
      if (!b->isMutable)
        return fail(place, "'" + place.text + "' is not mutable; declare it "
                           "as 'let " + place.text + " : mutable T = ...'");
      if (mlir::isa<ArrayType, SliceType>(b->type))
        return fail(place, "assigning a whole array is not supported yet");
      if (!notLent(b, place, "assigned")) return std::nullopt;
      R v = genExpr(valueNode, b->type);
      if (!v) return v;
      R c = coerce(*v, b->type, valueNode);
      if (!c) return c;
      b->value = c->value;
      addLenders(b->lenders, lendersOf(valueNode));
      moved_.erase(b);  // a moved local holds a value again
      return unit();
    }
    if (place.kind == NodeKind::Index) {
      const Node &obj = *place.kids[0];
      // `r.f.[i] <- v` writes the buffer the field holds, as
      // `let b = r.f in b.[i] <- v` does.
      if (obj.kind == NodeKind::Field) {
        if (spread_ && !contract_ && !ghost_)
          return fail(obj, "writing a record's buffer in a spread is not "
                           "supported yet; name the buffer (ADR 0060)");
        R buf = genExpr(obj, Type());
        if (!buf) return buf;
        Type elem = elementType(buf->type);
        if (!elem)
          return fail(obj, "only arrays and slices can be indexed, found " +
                               typeName(buf->type));
        // The record the field chain starts from: an `out` or `inout`
        // parameter, or a writable borrow, lets its buffers be written.
        const Node *root = &obj;
        while (root->kind == NodeKind::Field && !root->kids.empty())
          root = root->kids[0].get();
        BindingPtr rb = root->kind == NodeKind::Name && root->flags.empty()
                            ? lookup(root->text)
                            : nullptr;
        if (!writable(obj) && !(rb && writableValue(*rb)))
          return fail(obj, "cannot write to this buffer: its record must be "
                           "an 'out' or 'inout' parameter or a writable "
                           "borrow");
        auto idx = genIndexValue(*place.kids[1]);
        if (!idx) return std::nullopt;
        R v = genExpr(valueNode, elem);
        if (!v) return v;
        R c = coerce(*v, elem, valueNode);
        if (!c) return c;
        fillElement(create<StoreOp>(loc(n), c->value, buf->value, *idx), elem);
        return unit();
      }
      if (obj.kind != NodeKind::Name)
        return fail(obj, "only a named array or slice can be written");
      BindingPtr b = lookup(obj.text);
      if (!b) return fail(obj, "unknown name '" + obj.text + "'");
      Type elem = elementType(b->type);
      if (!elem)
        return fail(obj, "only arrays and slices can be indexed, found " +
                             typeName(b->type));
      if (!writableBuffer(*b))
        return fail(obj, "cannot write to '" + obj.text + "': " +
                             (b->isParam ? "declare the parameter 'out' or 'inout'"
                                         : "declare the local 'mutable'"));
      // A lambda that captures the buffer reads it until its last use.
      if (!contract_ && !ghost_)
        for (const auto &scope : scopes_)
          for (const auto &[name, x] : scope)
            if (x->closure && llvm::is_contained(x->lenders, b))
              if (const Node *use = usedAfter(x, obj))
                return fail(obj, "'" + b->name + "' is lent to '" + x->name +
                                     "', so it cannot be assigned here; " +
                                     stillUsed(x, obj, use) +
                                     ", and a borrow lasts until its last "
                                     "use");
      // A write to spec state is specification: its index and value may
      // read spec state, and codegen erases it (ADR 0058). A spec write
      // is per-thread state, so it is no spread's ownership goal.
      if (b->spec && !contract_ && !ghost_) {
        contract_ = true;
        auto idx = genIndexValue(*place.kids[1]);
        R v = idx ? genExpr(valueNode, elem) : std::nullopt;
        R c = v ? coerce(*v, elem, valueNode) : std::nullopt;
        contract_ = false;
        if (!c) return std::nullopt;
        create<StoreOp>(loc(n), c->value, b->value, *idx);
        return unit();
      }
      auto idx = genIndexValue(*place.kids[1]);
      if (!idx) return std::nullopt;
      if (!ownedHere(place, b, *idx, true))
        return std::nullopt;
      R v = genExpr(valueNode, elem);
      if (!v) return v;
      R c = coerce(*v, elem, valueNode);
      if (!c) return c;
      fillElement(create<StoreOp>(loc(n), c->value, b->value, *idx), elem);
      return unit();
    }
    return fail(place, "only a name or an element can be assigned");
  }

  // A store of a whole element that owns its slices must find the element
  // empty, so that no box is lost by writing over it (ADR 0048, section
  // 6). The verifier proves it from the mark.
  void fillElement(StoreOp store, Type elem) {
    if (contract_ || ghost_ || !ownsSlices(elem))
      return;
    store->setAttr("pia.fills", b_.getUnitAttr());
  }

  // --- ownership: `moved` (docs/design.md) ---------------------------

  // A local after it is moved, and where. `maybe` when only some paths to
  // here move it.
  struct Move {
    syntax::SourceLoc at;
    std::string what;              // "moved to 'take'"
    bool maybe = false;
    const Node *node = nullptr;    // the use that moved it
  };

  struct Deeper {
    unsigned &depth;
    explicit Deeper(unsigned &d) : depth(d) { ++depth; }
    ~Deeper() { --depth; }
  };

  // Values of scalar types are copied, so passing one as `moved` leaves
  // the caller's copy alive.
  bool copied(Type t) {
    return mlir::isa<IntType>(t) || isBool(t) || mlir::isa<mlir::FloatType>(t) ||
           isUnit(t);
  }

  // Whether `b` may be used at `n`: not after it was moved. Contracts and
  // ghost code may still name it, since they describe values, not use them.
  bool usable(const BindingPtr &b, const Node &n) {
    if (contract_ || ghost_) return true;
    auto m = moved_.find(b);
    if (m == moved_.end()) return true;
    fail(n, "'" + n.text + "' " + (m->second.maybe ? "may have been" : "was") +
                " " + m->second.what + " at " +
                std::to_string(m->second.at.line) + ":" +
                std::to_string(m->second.at.column) +
                ", so it can no longer be used here" +
                (m->second.maybe ? " (it is moved on some paths to here)"
                                 : ""));
    return false;
  }

  // The argument `arg` passed as the `moved` parameter `p` of `sig`: a
  // local is dead after the call.
  bool moveArgument(const Node &arg, Type t, const sema::FuncSig &sig,
                    const sema::Param &p) {
    if (contract_ || ghost_ || copied(t)) return true;
    if (arg.kind != NodeKind::Name || !arg.flags.empty()) return true;
    BindingPtr b = lookup(arg.text);
    if (!b) return true;
    if (b->isParam && !sema::hasModifier(b->modifiers, "moved")) {
      fail(arg, "'" + arg.text + "' is borrowed by this function, so it "
                "cannot be moved to '" + p.name + "' of '" + sig.name +
                "'; take it as 'moved', as in '(" + arg.text + " : moved " +
                typeName(t) + ")'");
      return false;
    }
    if (b->loopDepth < loopDepth_) {
      fail(arg, "'" + arg.text + "' is moved inside a loop, so the next "
                "iteration would use it after the move; bind it inside the "
                "loop, or move it after the loop");
      return false;
    }
    moved_[b] = Move{arg.loc, "moved to '" + sig.name + "'", false, &arg};
    return true;
  }

  // --- `@linear` (#56) --------------------------------------------------

  // The types marked `@linear`: a value of one must be consumed, passed as
  // `moved` or used as a value, on every path out of its scope.
  void collectLinear(const Node &program) {
    for (const syntax::NodePtr &item : program.kids) {
      // A generic type marked `@linear` makes each instance linear, as
      // `box t r` is: `box<u16>`.
      if (sema::isGenericTypeItem(*item)) {
        const Node &tv = *item->kids[3]->kids.back();
        if (tv.kids.size() >= 2)
          for (const syntax::NodePtr &a : tv.kids[1]->kids)
            if (a->text == "linear") linearGenerics_.insert(item->text);
        continue;
      }
      if (!sema::isTypeItem(*item)) continue;
      const Node &tv = *item->kids[3];
      if (tv.kids.size() < 2) continue;
      for (const syntax::NodePtr &a : tv.kids[1]->kids)
        if (a->text == "linear")
          if (Type t = types_.named(item->text))
            linear_.insert(t.getAsOpaquePointer());
    }
  }

  // A `@linear` type, or a record, variant or instance holding one.
  // Whether a value of type `t` owns the slices it holds: it is
  // `@linear` or has a `drop`, so it is never copied (ADR 0048).
  bool ownsSlices(Type t) {
    return mlir::isa_and_nonnull<RecordType>(t) && (isLinear(t) || hasDrop(t));
  }

  bool isLinear(Type t) {
    if (!t || (linear_.empty() && linearGenerics_.empty())) return false;
    if (linear_.count(t.getAsOpaquePointer())) return true;
    if (auto rt = mlir::dyn_cast<RecordType>(t)) {
      llvm::StringRef name = rt.getName();
      if (size_t lt = name.find('<'); lt != llvm::StringRef::npos)
        if (linearGenerics_.count(name.substr(0, lt).str())) return true;
    }
    if (auto rt = mlir::dyn_cast<RecordType>(t))
      for (Type f : rt.getFieldTypes())
        if (isLinear(f)) return true;
    return false;
  }

  // --- FFI (#55) -------------------------------------------------------

  // Whether `body` is `extern "symbol"`, and the symbol.
  static bool externSymbol(const Node &body, std::string &symbol) {
    if (body.kind != NodeKind::Apply || body.kids.size() != 2) return false;
    const Node &f = *body.kids[0], &s = *body.kids[1];
    if (f.kind != NodeKind::Name || f.text != "extern" || !f.flags.empty() ||
        s.kind != NodeKind::StringLit)
      return false;
    symbol = s.text;
    if (symbol.size() >= 2 && symbol.front() == '"' && symbol.back() == '"')
      symbol = symbol.substr(1, symbol.size() - 2);
    return true;
  }

  bool foreignType(Type t) {
    if (mlir::isa<IntType>(t) || isBool(t)) return true;
    if (mlir::isa<ArrayType, SliceType>(t))
      return mlir::isa<IntType>(elementType(t));
    return false;
  }

  // A C variadic function's arguments after its named ones are promoted
  // by C: integers narrower than an int and bools become an int, which
  // the callee reads with va_arg. Pia does not promote silently, so those
  // types are errors, and the declaration says the type C reads
  // (ADR 0051, section 6).
  bool checkVariadic(const sema::FuncSig &sig) {
    if (*variadic_ > sig.params.size()) {
      fail(*variadicNode_, "@variadic(" + std::to_string(*variadic_) +
                               ") names more parameters than the "
                               "declaration has");
      return false;
    }
    for (size_t i = *variadic_; i < sig.params.size(); ++i) {
      const sema::Param &p = sig.params[i];
      if (mlir::isa<ArrayType, SliceType>(p.type))
        continue;
      auto it = mlir::dyn_cast<IntType>(p.type);
      if (it && it.getStorageWidth() >= 32)
        continue;
      diags_.error(p.loc,
                   "'" + p.name +
                       "' is a variadic argument of a C "
                       "function, which C promotes to int, so it must be "
                       "an integer of 32 bits or more, or a buffer: give "
                       "it the type the function reads, such as i32 or "
                       "u32, instead of " +
                       typeName(p.type));
      return false;
    }
    return true;
  }

  // An extern's body: the C call, with the parameters as its arguments.
  R genForeign(const Node &body, const std::string &symbol,
               const sema::FuncSig &sig, Block *entry) {
    if (symbol.empty() ||
        !llvm::all_of(symbol, [](char c) {
          return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
        }))
      return fail(*body.kids[1], "a C symbol is letters, digits and '_'");
    for (const sema::Param &p : sig.params)
      if (!foreignType(p.type)) {
        diags_.error(p.loc, "a foreign function takes integers, bools and "
                            "buffers of integers for now, but '" + p.name +
                            "' has type " + typeName(p.type));
        return std::nullopt;
      }
    if (!sig.result || !(isUnit(sig.result) || mlir::isa<IntType>(sig.result) ||
                         isBool(sig.result)))
      return fail(body, "a foreign function returns unit, an integer or a "
                        "bool for now");
    if (variadic_ && !checkVariadic(sig))
      return std::nullopt;
    llvm::SmallVector<Type> results;
    if (!isUnit(sig.result)) results.push_back(sig.result);
    llvm::SmallVector<Value> args(entry->getArguments().begin(),
                                  entry->getArguments().end());
    auto op = create<ForeignOp>(loc(body), results,
                                b_.getStringAttr(symbol), args);
    if (variadic_)
      op->setAttr("pia.variadic", b_.getI64IntegerAttr(*variadic_));
    if (results.empty()) return unit();
    return TV{op.getResult(0), sig.result};
  }

  // `unsafe f x`: a call of a foreign function that has no contract. The
  // caller vouches for it; the verifier assumes nothing it does.
  R genUnsafe(const Node &n, Type expected) {
    if (n.kids.size() < 2 || n.kids[1]->kind != NodeKind::Name)
      return fail(n, "'unsafe' marks one call, as in 'unsafe f x'");
    if (n.kids[1]->text == "view" && n.kids[1]->flags.empty() &&
        !lookup("view") && overloadSet("view").empty())
      return genView(n, expected);
    syntax::NodePtr call;
    if (n.kids.size() == 2) {
      call = syntax::clone(*n.kids[1]);
    } else {
      call = syntax::makeNode(NodeKind::Apply, n.kids[1]->loc);
      for (size_t i = 1; i < n.kids.size(); ++i)
        call->add(syntax::clone(*n.kids[i]));
    }
    const Node *c = keep(std::move(call));
    const Node *saved = unsafeAt_;
    unsafeAt_ = c;
    R r = genExpr(*c, Type());
    unsafeAt_ = saved;
    return r;
  }

  // `unsafe view addr n`: the n elements at the address addr, such as the
  // pages a foreign `mmap` returned. The caller vouches that the memory is
  // there and overlaps no other buffer; the view may be written, and it
  // borrows nothing, since the foreign code that made it owns it.
  R genView(const Node &n, Type expected) {
    if (n.kids.size() != 4)
      return fail(n, "'unsafe view' takes an address and a length, as in "
                     "'unsafe view addr n'");
    auto sl = mlir::dyn_cast_or_null<SliceType>(expected);
    if (!sl || !mlir::isa<IntType>(sl.getElementType()))
      return fail(n, "'unsafe view' needs its slice type from the context, "
                     "a slice of integers, as in 'let mem : [u8] = unsafe "
                     "view addr n'");
    R addr = genExpr(*n.kids[2], types_.usize());
    if (!addr) return addr;
    addr = coerce(*addr, types_.usize(), *n.kids[2]);
    if (!addr) return addr;
    auto len = genIndexValue(*n.kids[3]);
    if (!len) return std::nullopt;
    auto op = create<ViewOp>(loc(n), sl, addr->value, *len);
    op->setAttr("pia.unsafe", b_.getUnitAttr());
    writable_.insert(&n);
    return TV{op.getResult(), sl};
  }

  // --- `drop` (#85) -----------------------------------------------------

  // A type has a drop when a non-generic `drop (x : moved t) : unit` is in
  // scope: the `Drop` concept, met by name like any other (ADR 0034).
  bool hasDrop(Type t) {
    if (!t || copied(t)) return false;
    for (const sema::FuncSig *f : overloadSet("drop"))
      if (!f->isGeneric() && f->params.size() == 1 &&
          f->params[0].type == t &&
          sema::hasModifier(f->params[0].modifiers, "moved") &&
          f->result && isUnit(f->result))
        return true;
    return false;
  }

  bool needsDrop(const BindingPtr &b) {
    return !contract_ && !ghost_ && b->name.find('#') == std::string::npos &&
           b->type != dropping_ && hasDrop(b->type);
  }

  const Node *keep(syntax::NodePtr n) {
    const Node *p = n.get();
    matchTrees_.push_back(std::move(n));  // diagnostics may point into it
    return p;
  }

  // `#region n`, the memory of a `with_arena`: n fresh, zeroed bytes. The
  // arena's `mem` holds a view of them, which is what a value allocated
  // in the arena borrows.
  // Regions live on the stack, so they are kept small; larger ones wait
  // for pages over mmap.
  static constexpr uint64_t kMaxRegion = 1 << 20;
  R genRegion(const Node &n, Type expected) {
    auto sl = mlir::dyn_cast_or_null<SliceType>(expected);
    if (!sl) return fail(n, "internal error: a region needs a slice type");
    auto lit = sema::parseIntLiteral(n.kids[1]->text);
    if (!lit || !lit->suffix.empty() || lit->value.getActiveBits() > 63)
      return fail(*n.kids[1], "an arena's size must be an integer literal "
                              "without a suffix, as in 'with_arena 256 ...'");
    uint64_t size = lit->value.getZExtValue();
    if (size > kMaxRegion)
      return fail(*n.kids[1], "an arena lives on the stack, so it can hold "
                              "at most " + std::to_string(kMaxRegion) +
                              " bytes for now");
    lentTypes_.insert(sl.getAsOpaquePointer());
    auto t = ArrayType::get(&ctx_, size, sl.getElementType());
    return TV{create<RegionOp>(loc(n), t), t};
  }

  // `drop x`, marked so that it runs only where `x` is not consumed.
  const Node &dropNode(const std::string &name, syntax::SourceLoc at) {
    auto call = syntax::makeNode(NodeKind::Apply, at);
    call->flags = "drop";
    call->add(syntax::makeNode(NodeKind::Name, at, "drop"));
    call->add(syntax::makeNode(NodeKind::Name, at, name));
    return *keep(std::move(call));
  }

  // An exit's drop: nothing where the value was consumed on the way, the
  // call where it was not.
  R genDrop(const Node &n) {
    const Node &arg = *n.kids[1];
    BindingPtr b = lookup(arg.text);
    if (!b) return unit();
    auto m = moved_.find(b);
    if (m != moved_.end()) {
      if (!m->second.maybe) return unit();
      return fail(n, "'" + arg.text + "' is consumed on only some paths to "
                     "here, so whether to drop it at the end of its scope "
                     "is unknown; consume it on every path, or on none");
    }
    auto call = syntax::clone(n);
    call->flags.clear();
    const Node &c = *keep(std::move(call));
    return genApply(c, Type());
  }

  // --- Borrows (#70) ----------------------------------------------------

  // " inout mutable" from "borrowed inout mutable".
  static std::string withoutBorrowed(llvm::StringRef mods) {
    std::string out;
    llvm::SmallVector<llvm::StringRef> words;
    mods.split(words, ' ', -1, false);
    for (llvm::StringRef w : words)
      if (w != "borrowed") out += " " + w.str();
    return out;
  }

  using Lenders = std::vector<BindingPtr>;

  static void addLenders(Lenders &to, const Lenders &from) {
    for (const BindingPtr &b : from)
      if (llvm::find(to, b) == to.end()) to.push_back(b);
  }

  // "regions:r,s" (Regions.cpp) -> {r, s}.
  static std::vector<std::string> regionsOfFlags(llvm::StringRef flags) {
    std::vector<std::string> out;
    if (!flags.consume_front("regions:")) return out;
    llvm::SmallVector<llvm::StringRef> names;
    flags.split(names, ',', -1, false);
    for (llvm::StringRef n : names) out.push_back(n.str());
    return out;
  }

  // The binding that stands for the region `r` in the current function.
  BindingPtr regionBinding(const std::string &r, const std::string &of = "") {
    BindingPtr &b = regionBindings_[r];
    if (!b) {
      b = std::make_shared<Binding>();
      b->name = r;
      b->region = true;
      b->regionOf = of;
    }
    return b;
  }

  // Whether a value of type `t` holds a field that borrows from a region,
  // as `vec<u8>` holds `buf`. Each such field's type then may borrow.
  bool holdsRegionField(Type t, unsigned depth = 0) {
    auto rt = mlir::dyn_cast_or_null<RecordType>(t);
    if (!rt || depth > 8) return false;
    std::string base = rt.getName().split('<').first.str();
    bool any = false;
    for (auto [f, ft] : llvm::zip(rt.getFieldNames(), rt.getFieldTypes())) {
      if (regionInfo_.lentFields.count(base + "." + f.str())) {
        lentTypes_.insert(ft.getAsOpaquePointer());
        any = true;
      }
      any |= holdsRegionField(ft, depth + 1);
    }
    return any;
  }

  // What the arguments for the regions `regions` of `sig` borrow from.
  Lenders regionLenders(const sema::FuncSig &sig,
                        const std::vector<std::string> &regions,
                        const std::vector<const Node *> &args) {
    Lenders out;
    for (size_t i = 0; i < sig.params.size() && i < args.size(); ++i)
      for (const std::string &r : sig.params[i].regions)
        if (llvm::is_contained(regions, r)) {
          addLenders(out, lendersOf(*args[i]));
          break;
        }
    return out;
  }

  Lenders lendersOf(const Node &n) {
    auto it = lent_.find(&n);
    if (it != lent_.end()) return it->second;
    // A name read without `genExpr`, such as the hidden scrutinee of
    // `#payload #match0 Ok`.
    if (n.kind == NodeKind::Name && !contract_ && !ghost_)
      if (BindingPtr b = lookup(n.text)) return b->lenders;
    return {};
  }

  // Whether `n`'s value is a buffer borrowed as writable.
  bool writable(const Node &n) {
    if (writable_.count(&n)) return true;
    if (n.kind == NodeKind::Name && !contract_ && !ghost_)
      if (BindingPtr b = lookup(n.text)) return writableValue(*b);
    return false;
  }

  // Whether the buffers `b` holds may be written: a borrow that may, or an
  // `out` or `inout` parameter, whose fields' buffers may be too.
  static bool writableValue(const Binding &b) {
    return b.writable || (b.isParam && (sema::hasModifier(b.modifiers, "out") ||
                                        sema::hasModifier(b.modifiers, "inout")));
  }

  // `n` was generated as `other`, a tree made from it.
  void passLenders(const Node &n, const Node &other) {
    if (writable(other)) writable_.insert(&n);
    Lenders l = lendersOf(other);
    if (l.empty()) lent_.erase(&n);
    else lent_[&n] = std::move(l);
  }

  // What `n`'s value, just generated, is borrowed from: a local that holds
  // a borrow, a part of one, or either branch's. A call records its own.
  // A copied value, such as an integer read from a borrowed slice, borrows
  // nothing.
  void noteLenders(const Node &n, const TV &r) {
    // An element of a writable buffer that owns its slices, such as a box,
    // may be written through (ADR 0048): ownership keeps the elements'
    // slices apart.
    if (!contract_ && !ghost_ && n.kind == NodeKind::Index &&
        n.kids[1]->kind != NodeKind::Range && ownsSlices(r.type) &&
        (writable(*n.kids[0]) || writablePath(*n.kids[0]))) {
      writable_.insert(&n);
      // What it holds is lent from the buffer, or the record whose field
      // holds it, while it is live, so the element cannot be replaced
      // under it.
      const Node *root = n.kids[0].get();
      while (root->kind == NodeKind::Field && !root->kids.empty())
        root = root->kids[0].get();
      if (root->kind == NodeKind::Name && root->flags.empty())
        if (BindingPtr b = lookup(root->text)) {
          Lenders l = b->lenders;
          addLenders(l, {b});
          lent_[&n] = std::move(l);
          lentTypes_.insert(r.type.getAsOpaquePointer());
          return;
        }
    }
    if (!contract_ && !ghost_ && n.kind == NodeKind::Field &&
        n.kids[0]->kind == NodeKind::Index && writable_.count(n.kids[0].get()))
      writable_.insert(&n);
    if (contract_ || ghost_ || lent_.count(&n) || !mayBorrow(r.type)) return;
    Lenders l;
    bool w = false;
    switch (n.kind) {
      case NodeKind::Name:
        if (n.flags.empty())
          if (BindingPtr b = lookup(n.text)) {
            l = b->lenders;
            w = writableValue(*b);
          }
        break;
      case NodeKind::Apply:
        // Not a call, which records its own: a constructor, `Ok (lend p)`,
        // or `#payload x Ok` from a match or a `?`. Either holds what its
        // arguments borrow.
        for (size_t i = 1; i < n.kids.size(); ++i) {
          addLenders(l, lendersOf(*n.kids[i]));
          w |= writable(*n.kids[i]);
        }
        break;
      case NodeKind::Field:
        l = lendersOf(*n.kids[0]);
        w = writable(*n.kids[0]);
        break;
      case NodeKind::Index:
        if (n.kids[1]->kind == NodeKind::Range) {
          l = lendersOf(*n.kids[0]);
          w = writable(*n.kids[0]);
        }
        break;
      case NodeKind::Sequence:
        l = lendersOf(*n.kids.back());
        w = writable(*n.kids.back());
        break;
      case NodeKind::Cleanup:
        l = lendersOf(*n.kids[0]);
        w = writable(*n.kids[0]);
        break;
      case NodeKind::If:
        w = n.kids.size() > 2;
        for (size_t i = 1; i < n.kids.size(); ++i) {
          addLenders(l, lendersOf(*n.kids[i]));
          w &= writable(*n.kids[i]);
        }
        break;
      case NodeKind::RecordLit:
        for (const syntax::NodePtr &f : n.kids)
          if (!f->kids.empty()) addLenders(l, lendersOf(*f->kids[0]));
        break;
      default:
        break;
    }
    if (w) writable_.insert(&n);
    if (!l.empty()) lent_[&n] = std::move(l);
  }

  // Whether a value of type `t` can hold a borrow: it is, or holds, a type
  // that some call's result borrows, such as the `[u8]` of `result
  // (borrowed(m) [u8]) e`. So the error of that result, a copy of a
  // field, or a length borrows nothing.
  bool mayBorrow(Type t, unsigned depth = 0) {
    if (!t || copied(t) || depth > 8) return false;
    if (lentTypes_.count(t.getAsOpaquePointer())) return true;
    if (auto rt = mlir::dyn_cast<RecordType>(t)) {
      if (holdsRegionField(rt)) return true;
      for (Type f : rt.getFieldTypes())
        if (mayBorrow(f, depth + 1)) return true;
    }
    if (Type e = elementType(t)) return mayBorrow(e, depth + 1);
    return false;
  }

  // Whether the buffer `n` reaches may be written: one a writable name
  // holds, a field of an `out` or `inout` record, or a field of an element
  // that owns its slices of a writable buffer (ADR 0048).
  bool writablePath(const Node &n) {
    if (writable_.count(&n)) return true;
    if (n.kind == NodeKind::Name && n.flags.empty() && !contract_ && !ghost_)
      if (BindingPtr b = lookup(n.text))
        return writableBuffer(*b) || writableValue(*b);
    if (n.kind == NodeKind::Field && !n.kids.empty())
      return writablePath(*n.kids[0]);
    return false;
  }

  // Whether the buffer `b` names may be written: an `out` or `inout`
  // parameter, or a local holding a borrow whose result type lets it be
  // written, as `alloc`'s does.
  static bool writableBuffer(const Binding &b) {
    if (b.isParam)
      return sema::hasModifier(b.modifiers, "out") ||
             sema::hasModifier(b.modifiers, "inout");
    return b.writable;
  }

  // A use of the local `x` after `at`, which keeps its loans alive there
  // (ADR 0042): a mention of it later in its scope, in evaluation order,
  // which follows the source except around loops. In a loop opened after
  // `x` was bound, every use is later, so `at` itself is returned.
  const Node *usedAfter(const BindingPtr &x, const Node &at) {
    if (!x->scope || x->loopDepth < loopDepth_) return &at;
    std::set<const Node *> inside;
    std::function<void(const Node &)> mark = [&](const Node &k) {
      inside.insert(&k);
      for (const NodePtr &c : k.kids) mark(*c);
    };
    mark(at);
    // A cleanup, such as a `defer` or a drop, runs after the exit it is
    // attached to, wherever its source is, so a use in one is later unless
    // `at` is in that cleanup itself.
    std::function<bool(const Node &)> holdsAt = [&](const Node &k) {
      if (&k == &at) return true;
      for (const NodePtr &c : k.kids)
        if (holdsAt(*c)) return true;
      return false;
    };
    std::function<bool(const Node &)> holdsCopyOfAt = [&](const Node &k) {
      if (&k == &at || (k.kind == at.kind && k.loc.offset == at.loc.offset))
        return true;
      for (const NodePtr &c : k.kids)
        if (holdsCopyOfAt(*c)) return true;
      return false;
    };
    const Node *use = nullptr;
    std::function<void(const Node &, bool)> find = [&](const Node &k,
                                                       bool later) {
      if (use || inside.count(&k)) return;
      if (k.kind == NodeKind::Name && k.text == x->name &&
          (later || k.loc.offset > at.loc.offset)) {
        use = &k;
        return;
      }
      // A `defer` in the source is generated from a copy of its scope, so
      // `at` may be a copy of a node here: it is the same node if it has
      // the same kind and place.
      if (k.kind == NodeKind::Defer && !holdsCopyOfAt(k)) later = true;
      for (size_t i = 0; i < k.kids.size(); ++i) {
        bool cleanup = k.kind == NodeKind::Cleanup && i > 0 &&
                       !holdsAt(*k.kids[i]);
        find(*k.kids[i], later || cleanup);
      }
    };
    find(*x->scope, false);
    return use;
  }

  // A closure that captures `b` as `inout`, is in scope, and is used after
  // `at`, if any, with that use (ADR 0044, section 6).
  std::pair<BindingPtr, const Node *> writerOf(const BindingPtr &b,
                                               const Node &at) {
    for (const auto &scope : scopes_)
      for (const auto &[name, x] : scope)
        if (x != b && name.find('#') == std::string::npos &&
            std::any_of(x->refs.begin(), x->refs.end(),
                        [&](const auto &r) { return r.second == b; }))
          if (const Node *use = usedAfter(x, at)) return {x, use};
    return {nullptr, nullptr};
  }

  // A named local that borrows from `b`, is in scope, and is used after
  // `at`, if any, with that use.
  std::pair<BindingPtr, const Node *> borrowerOf(const BindingPtr &b,
                                                 const Node &at) {
    for (const auto &scope : scopes_)
      for (const auto &[name, x] : scope)
        if (x != b && name.find('#') == std::string::npos &&
            llvm::find(x->lenders, b) != x->lenders.end())
          if (const Node *use = usedAfter(x, at)) return {x, use};
    return {nullptr, nullptr};
  }

  // Why `x`'s loan is still alive at `at`.
  std::string stillUsed(const BindingPtr &x, const Node &at, const Node *use) {
    if (use == &at)
      return "'" + x->name + "' was bound outside this loop, so its borrow "
             "lasts through the loop";
    return "'" + x->name + "' is used later, at " + where(*use);
  }

  // `b` is about to change: not while something that borrows from it is
  // used later.
  bool notLent(const BindingPtr &b, const Node &at, const std::string &how) {
    if (contract_ || ghost_) return true;
    auto [x, use] = borrowerOf(b, at);
    if (!x) return true;
    fail(at, "'" + b->name + "' is lent to '" + x->name + "', so it cannot "
             "be " + how + " here; " + stillUsed(x, at, use) +
             ", and a borrow lasts until its last use");
    return false;
  }

  // At the end of `b`'s scope, the 'let' `n` with body `body`: its value
  // cannot outlive `b` by being borrowed from it, and none of `b`'s own
  // lenders may have been moved while `b` was in scope.
  bool borrowsEnd(const BindingPtr &b, const Node &n, const Node &body) {
    if (contract_ || ghost_) return true;
    Lenders out = lendersOf(body);
    if (b->arena) {
      if (llvm::is_contained(out, b)) {
        fail(*n.kids[4], "this value is in the arena '" + b->name + "', or "
                         "borrowed from it, so it cannot leave the "
                         "'with_arena', which frees the arena here");
        return false;
      }
      if (auto m = moved_.find(b); m != moved_.end()) {
        fail(m->second.node ? *m->second.node : n,
             "the arena '" + b->name + "' cannot be " + m->second.what +
                 ", since its memory is freed when its 'with_arena' ends");
        return false;
      }
      lent_[&n] = std::move(out);
      b->lenders.clear();  // it lent itself; break the cycle
      return true;
    }
    if (llvm::find(out, b) != out.end()) {
      fail(*n.kids[4], "this value is borrowed from '" + b->name +
                           "', so it cannot outlive '" + b->name +
                           "', whose scope ends here");
      return false;
    }
    for (const BindingPtr &l : b->lenders) {
      auto m = moved_.find(l);
      if (m == moved_.end()) continue;
      const Node &at = m->second.node ? *m->second.node : n;
      const Node *use = m->second.node ? usedAfter(b, at) : &at;
      if (!use) continue;  // moved after `b`'s last use
      fail(at, "'" + l->name + "' is lent to '" + b->name + "', so it cannot "
               "be " + m->second.what + " here; " + stillUsed(b, at, use) +
               ", and a borrow lasts until its last use");
      return false;
    }
    lent_[&n] = std::move(out);
    if (writable(body)) writable_.insert(&n);
    return true;
  }

  // A use of a linear local, or of one with a drop, as a value consumes
  // it, unless the use turns out to be a borrow (`unconsume`).
  void consumeValue(const BindingPtr &b, const Node &n) {
    if (contract_ || ghost_ || n.text.find('#') != std::string::npos)
      return;
    // An atomic cell is a place: copying one would not be atomic, so a use
    // as a value moves it (ADR 0052, section 1).
    if (mlir::isa<AtomicType>(b->type)) {
      moved_[b] = Move{n.loc,
                       "moved by its use as a value (an atomic cell "
                       "is not copyable; borrow it instead)",
                       false, &n};
      return;
    }
    if (!(isLinear(b->type) || hasDrop(b->type)))
      return;
    moved_[b] = Move{n.loc, "consumed by its use as a value", false, &n};
  }

  // `n` was only borrowed: a field read, `len`, or an argument of a
  // borrowed parameter.
  void unconsume(const Node &n) {
    if (n.kind == NodeKind::Index)
      keepElement(n);
    if (n.kind != NodeKind::Name || !n.flags.empty()) return;
    BindingPtr b = lookup(n.text);
    if (!b) return;
    auto m = moved_.find(b);
    if (m != moved_.end() && m->second.node == &n) moved_.erase(m);
  }

  // At the end of `b`'s scope: a linear value must have been consumed on
  // every path.
  bool consumed(const BindingPtr &b, syntax::SourceLoc at) {
    // Contracts and ghost code describe values; they consume nothing.
    if (contract_ || ghost_ || b->name.find('#') != std::string::npos ||
        !isLinear(b->type))
      return true;
    auto m = moved_.find(b);
    if (m != moved_.end() && !m->second.maybe) return true;
    diags_.error(at, "'" + b->name + "' has the @linear type " +
                         typeName(b->type) + ", so it must be consumed on "
                         "every path out of its scope, by passing it as "
                         "'moved' or returning it" +
                         (m != moved_.end()
                              ? "; it is consumed on only some paths"
                              : "; nothing consumes it"));
    return false;
  }

  // After a loop body: nothing bound outside the loop was moved in it.
  bool checkLoopMoves() {
    for (auto &[b, m] : moved_)
      if (b->loopDepth < loopDepth_) {
        diags_.error(m.at, "'" + b->name + "' is moved inside a loop, so the "
                           "next iteration would use it after the move; "
                           "bind it inside the loop, or move it after the "
                           "loop");
        return false;
      }
    return true;
  }

  // After an `if`: a local moved on either branch is moved, or maybe
  // moved, after it. `moved_` holds the else branch's moves.
  void mergeMoves(const std::map<BindingPtr, Move> &thenMoves) {
    std::map<BindingPtr, Move> out;
    for (auto &[b, m] : thenMoves) {
      auto e = moved_.find(b);
      Move merged = m;
      merged.maybe = m.maybe || e == moved_.end() || e->second.maybe;
      out[b] = merged;
    }
    for (auto &[b, m] : moved_)
      if (!thenMoves.count(b)) {
        Move merged = m;
        merged.maybe = true;
        out[b] = merged;
      }
    moved_ = std::move(out);
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
      std::map<BindingPtr, Move> movedBefore = moved_;
      pushScope();
      R t = genExpr(thenNode, expected);
      popScope();
      if (!t) return t;
      tv = *t;
      thenVars = values(vars);
      setValues(vars, before);
      std::map<BindingPtr, Move> movedThen = std::move(moved_);
      moved_ = std::move(movedBefore);
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
      mergeMoves(movedThen);
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
      Deeper deeper(loopDepth_);
      R r = ok ? genExpr(body, Type()) : std::nullopt;
      if (r && !checkLoopMoves()) r = std::nullopt;
      if (r && !mustUse(*r, body)) r = std::nullopt;
      if (r) create<mlir::scf::YieldOp>(l, values(vars));
      popScope();
      if (!r) return r;
    }
    setValues(vars, forOp.getResults());
    return unit();
  }

  // --- spread (ADR 0060) --------------------------------------------------

  // The innermost `spread` being generated: its loop variable, and for each
  // buffer the body writes, the owner array that says which of its cells an
  // iteration owns (none: the identity, iteration i owns cell i).
  struct SpreadScope {
    std::string var;
    Value iv;                          // the loop variable, at its range type
    std::set<const Binding *> outside; // the bindings in scope before it
    std::set<std::string> written;     // the buffers the body writes
    std::map<std::string, BindingPtr> owners;
    bool footprint = false; // a function's @owns, not a spread
  };
  std::optional<SpreadScope> spread_;

  // The names of buffers the body writes: element by element, or by
  // passing them to a call's `out` or `inout` parameter.
  void collectWrittenBuffers(const Node &n, std::set<std::string> &out) {
    if (n.kind == NodeKind::Assign && n.kids[0]->kind == NodeKind::Index &&
        n.kids[0]->kids[0]->kind == NodeKind::Name)
      out.insert(n.kids[0]->kids[0]->text);
    if (n.kind == NodeKind::Apply && n.kids[0]->kind == NodeKind::Name)
      if (auto it = sigs_.find(n.kids[0]->text); it != sigs_.end()) {
        const sema::FuncSig &sig = it->second;
        for (size_t k = 1; k < n.kids.size() && k - 1 < sig.params.size(); ++k)
          if (n.kids[k]->kind == NodeKind::Name &&
              (sema::hasModifier(sig.params[k - 1].modifiers, "out") ||
               sema::hasModifier(sig.params[k - 1].modifiers, "inout")))
            out.insert(n.kids[k]->text);
      }
    for (const syntax::NodePtr &k : n.kids)
      if (k)
        collectWrittenBuffers(*k, out);
  }

  // A written buffer may only be indexed, or measured with `len`, in a
  // spread body: anything else could reach a cell the iteration does not
  // own (ADR 0060, section 1).
  const Node *strayUse(const Node &n, const Node *parent,
                       const std::set<std::string> &written) {
    if (n.kind == NodeKind::Name && written.count(n.text)) {
      bool indexed = parent && parent->kind == NodeKind::Index &&
                     parent->kids[0].get() == &n;
      // `len xs`, or `old xs`, which only contracts and lemmas can use.
      bool measured =
          parent && parent->kind == NodeKind::Apply &&
          parent->kids.size() == 2 && parent->kids[1].get() == &n &&
          parent->kids[0]->kind == NodeKind::Name &&
          (parent->kids[0]->text == "len" || parent->kids[0]->text == "old");
      // An argument of a call to a function with a footprint for it, or
      // of a lemma, which is erased; checked at the call.
      bool passed = false;
      if (parent && parent->kind == NodeKind::Apply &&
          parent->kids[0]->kind == NodeKind::Name &&
          parent->kids[0].get() != &n)
        if (auto it = sigs_.find(parent->kids[0]->text); it != sigs_.end()) {
          const sema::FuncSig &sig = it->second;
          size_t at = 0;
          for (size_t k = 1; k < parent->kids.size(); ++k)
            if (parent->kids[k].get() == &n)
              at = k - 1;
          // A lemma is erased, and a spec function is only for contracts
          // and lemmas: neither runs.
          bool lemma = sig.item && (hasFlag(*sig.item, "lemma") ||
                                    hasFlag(*sig.item, "spec"));
          passed =
              lemma || llvm::any_of(footprintsOf(sig), [&](const Footprint &f) {
                return f.buf == at;
              });
        }
      if (!indexed && !measured && !passed)
        return &n;
    }
    // Contracts are erased, so what they read cannot race.
    if (n.kind == NodeKind::Assert || n.kind == NodeKind::Assume)
      return nullptr;
    for (const syntax::NodePtr &k : n.kids)
      if (k)
        if (const Node *bad = strayUse(*k, &n, written))
          return bad;
    return nullptr;
  }

  // The goal that iteration `i` owns cell `idx` of `buf`, at an access in a
  // spread body: `idx = i`, or `owner.[idx] = i` under `@owns(buf, owner)`.
  bool ownedHere(const Node &at, const BindingPtr &buf, Value idx, bool write) {
    if (!spread_ || contract_ || ghost_)
      return true;
    if (!spread_->outside.count(buf.get()) ||
        !spread_->written.count(buf->name))
      return true;
    Location l = loc(at);
    Value cell;
    std::string by;
    auto owner = spread_->owners.find(buf->name);
    if (owner != spread_->owners.end()) {
      Type et = elementType(owner->second->type);
      cell = create<LoadOp>(l, et, owner->second->value, idx);
      by = owner->second->name + ".[c] = " + spread_->var;
    } else {
      cell = create<FromIndexOp>(l, types_.usize(), idx);
      by = "c = " + spread_->var;
    }
    Value ok = cmp(l, CmpPredicate::eq, cell, spread_->iv);
    auto a = create<contract::AssertOp>(l, ok);
    a->setAttr("pia.claim",
               b_.getStringAttr("the iteration owns the cell it " +
                                std::string(write ? "writes" : "reads") +
                                " in '" + buf->name + "' (" + by + ")"));
    return true;
  }

  // The `@owns` attributes of the function being generated.
  std::vector<const Node *> owns_;

  // Sets up the footprint checks of a function with `@owns` (ADR 0060):
  // its owned buffers can only be indexed, measured, or passed to a call
  // with a footprint of its own, and every access is a goal.
  bool footprintScope(const Node &item) {
    SpreadScope sc;
    const Node *bNode = nullptr;
    for (const Node *a : owns_) {
      BindingPtr buf = lookup(a->kids[0]->text);
      BindingPtr owner = lookup(a->kids[1]->text);
      BindingPtr b = lookup(a->kids[2]->text);
      if (!buf || !buf->isParam || !elementType(buf->type)) {
        fail(*a->kids[0], "@owns names a buffer parameter first");
        return false;
      }
      if (!owner || !owner->isParam || !elementType(owner->type) ||
          !mlir::isa<IntType>(elementType(owner->type))) {
        fail(*a->kids[1], "@owns names an owner array parameter second");
        return false;
      }
      if (!b || !b->isParam || !mlir::isa<IntType>(b->type)) {
        fail(*a->kids[2], "@owns names an integer parameter third, the owner "
                          "of the cells it may touch");
        return false;
      }
      if (bNode && bNode->text != a->kids[2]->text) {
        fail(*a->kids[2], "every @owns of a function names the same owner");
        return false;
      }
      bNode = a->kids[2].get();
      sc.var = b->name;
      sc.iv = b->value;
      sc.written.insert(buf->name);
      sc.owners[buf->name] = owner;
      sc.outside.insert(buf.get());
    }
    const Node &body = *item.kids.back();
    if (const Node *bad = strayUse(body, nullptr, sc.written)) {
      fail(*bad,
           "'" + bad->text +
               "' has a footprint (@owns), so it can only "
               "be indexed here, or passed to a function with a footprint");
      return false;
    }
    sc.footprint = true;
    spread_ = std::move(sc);
    return true;
  }

  // Where a callee's `@owns(buf, owner, b)` puts its buffer, owner and
  // owner value among its parameters.
  struct Footprint {
    size_t buf, owner, b;
  };
  std::vector<Footprint> footprintsOf(const sema::FuncSig &sig) {
    std::vector<Footprint> out;
    if (!sig.item)
      return out;
    const Node &ret = *sig.item->kids[1];
    if (ret.kind != NodeKind::RetAnnot || ret.kids.size() < 2)
      return out;
    auto index = [&](const std::string &name) -> std::optional<size_t> {
      for (size_t i = 0; i < sig.params.size(); ++i)
        if (sig.params[i].name == name)
          return i;
      return std::nullopt;
    };
    for (const syntax::NodePtr &a : ret.kids[1]->kids) {
      if (a->text != "owns" || a->kids.size() != 3)
        continue;
      auto x = index(a->kids[0]->text), o = index(a->kids[1]->text),
           b = index(a->kids[2]->text);
      if (x && o && b)
        out.push_back({*x, *o, *b});
    }
    return out;
  }

  // A buffer that a spread writes, or that a function owns, passed to a
  // call: the callee must own it by the same owner array, and the goal is
  // that it touches the iteration's cells, `b = i` (ADR 0060).
  bool checkFootprintCall(const Node &n, const sema::FuncSig &sig,
                          const std::vector<const Node *> &args) {
    if (!spread_ || contract_ || ghost_)
      return true;
    std::vector<Footprint> fps = footprintsOf(sig);
    for (size_t i = 0; i < args.size(); ++i) {
      const Node &arg = *args[i];
      if (arg.kind != NodeKind::Name || !spread_->written.count(arg.text))
        continue;
      BindingPtr buf = lookup(arg.text);
      if (!buf || !spread_->outside.count(buf.get()))
        continue;
      auto fp =
          llvm::find_if(fps, [&](const Footprint &f) { return f.buf == i; });
      auto owner = spread_->owners.find(arg.text);
      if (fp == fps.end())
        return fail(arg, "'" + arg.text + "' is passed to '" + sig.name +
                             "', which has no footprint for it: give it "
                             "@owns(" +
                             sig.params[i].name +
                             ", owner, b) "
                             "(ADR 0060)"),
               false;
      if (owner == spread_->owners.end())
        return fail(arg, "'" + arg.text +
                             "' has no owner array here, so it "
                             "cannot be passed to a call with a footprint: "
                             "give the spread @owns(" +
                             arg.text + ", owner) (ADR 0060)"),
               false;
      const Node &ownerArg = *args[fp->owner];
      if (ownerArg.kind != NodeKind::Name ||
          lookup(ownerArg.text) != owner->second)
        return fail(ownerArg, "the footprint's owner must be '" +
                                  owner->second->name + "', the owner of '" +
                                  arg.text + "' here"),
               false;
      R bv = genExpr(*args[fp->b], Type());
      if (!bv)
        return false;
      Location l = loc(*args[fp->b]);
      auto as = create<contract::AssertOp>(
          l, cmp(l, CmpPredicate::eq, bv->value, spread_->iv));
      as->setAttr("pia.claim",
                  b_.getStringAttr("the call touches only the cells the "
                                   "iteration owns in '" +
                                   arg.text + "' (its '" +
                                   sig.params[fp->b].name + "' is '" +
                                   spread_->var + "')"));
    }
    return true;
  }

  R genSpread(const Node &n) {
    Location l = loc(n);
    const Node &pattern = *n.kids[0];
    const Node &iterable = *n.kids[1];
    const Node &attrs = *n.kids[2];
    const Node &annots = *n.kids[3];
    const Node &body = *n.kids[4];
    if (spread_)
      return fail(n, spread_->footprint
                         ? "a spread in a function with @owns is not "
                           "supported yet"
                         : "a spread inside a spread is not supported yet");
    if (pattern.kind != NodeKind::PVar)
      return fail(pattern, "a spread binds a single name for now");
    if (iterable.kind != NodeKind::Range)
      return fail(iterable,
                  "a spread runs over a range 'lo..hi' for now (ADR 0060)");
    for (const syntax::NodePtr &a : annots.kids)
      if (a->kind != NodeKind::Ensures)
        return fail(*a, "a spread takes 'ensures', not a loop invariant or a "
                        "measure: its iterations are not in sequence");
    std::vector<BindingPtr> vars = carried({&body});
    if (!vars.empty())
      return fail(n, "a spread body cannot assign '" + vars[0]->name +
                         "', which is declared outside it: iterations run at "
                         "the same time (ADR 0060)");
    SpreadScope sc;
    sc.var = pattern.text;
    collectWrittenBuffers(body, sc.written);
    for (const auto &scope : scopes_)
      for (const auto &[name, b] : scope)
        sc.outside.insert(b.get());
    if (const Node *bad = strayUse(body, nullptr, sc.written))
      return fail(*bad,
                  "'" + bad->text +
                      "' is written in this spread, so it "
                      "can only be indexed here: passing it on could reach "
                      "a cell another iteration writes (ADR 0060)");
    for (const syntax::NodePtr &a : attrs.kids) {
      if (a->text != "owns")
        return fail(*a, "the attribute @" + a->text +
                            " is not supported on a spread yet");
      if (a->kids.size() != 2 || a->kids[0]->kind != NodeKind::Name ||
          a->kids[1]->kind != NodeKind::Name)
        return fail(*a, "@owns takes a buffer and an owner array: "
                        "@owns(buf, owner)");
      BindingPtr owner = lookup(a->kids[1]->text);
      if (!owner || !elementType(owner->type) ||
          !mlir::isa<IntType>(elementType(owner->type)))
        return fail(*a->kids[1], "an owner must be an array of integers");
      if (sc.written.count(owner->name))
        return fail(*a->kids[1], "the owner array '" + owner->name +
                                     "' must not be written in the spread");
      sc.owners[a->kids[0]->text] = owner;
    }
    auto bounds = genRange(iterable);
    if (!bounds)
      return std::nullopt;
    Type t = bounds->first.type;
    Value lb = toIndex(l, bounds->first.value);
    Value ub = toIndex(l, bounds->second.value);
    Value step = create<mlir::arith::ConstantIndexOp>(l, 1);
    auto forOp = create<mlir::scf::ForOp>(l, lb, ub, step, mlir::ValueRange{});
    forOp->setAttr("pia.spread", b_.getUnitAttr());
    Block *block = forOp.getBody();
    {
      OpBuilder::InsertionGuard guard(b_);
      if (!block->empty() &&
          block->back().hasTrait<mlir::OpTrait::IsTerminator>())
        block->back().erase();
      b_.setInsertionPointToEnd(block);
      pushScope();
      Value i = create<FromIndexOp>(loc(pattern), t, forOp.getInductionVar());
      if (!checkFresh(pattern.text, pattern.loc)) {
        popScope();
        return std::nullopt;
      }
      bind(pattern.text, i, t, false);
      sc.iv = i;
      // The iteration starts with its own cells as they were before the
      // loop: no other iteration writes them (ADR 0060).
      for (const std::string &name : sc.written) {
        BindingPtr wb = lookup(name);
        if (!wb || !sc.outside.count(wb.get()))
          continue;
        auto owner = sc.owners.find(name);
        Value ov = owner != sc.owners.end() ? owner->second->value : Value();
        auto h = create<contract::HavocOthersOp>(l, wb->value, i, ov);
        h->setAttr("pia.from_start", b_.getUnitAttr());
      }
      spread_ = std::move(sc);
      LoopScope inLoop(frames_);
      Deeper deeper(loopDepth_);
      R r = genExpr(body, Type());
      if (r && !checkLoopMoves())
        r = std::nullopt;
      if (r && !mustUse(*r, body))
        r = std::nullopt;
      // Each `ensures` is proved at the end of one iteration, with every
      // cell of a written buffer that another iteration owns forgotten,
      // so it holds whatever the others write (ADR 0060).
      if (r && !annots.kids.empty()) {
        for (const std::string &name : spread_->written) {
          BindingPtr wb = lookup(name);
          if (!wb || !spread_->outside.count(wb.get()))
            continue;
          auto owner = spread_->owners.find(name);
          Value ov =
              owner != spread_->owners.end() ? owner->second->value : Value();
          create<contract::HavocOthersOp>(l, wb->value, spread_->iv, ov);
        }
        for (const syntax::NodePtr &a : annots.kids) {
          SpreadScope saved = *spread_;
          spread_.reset();
          R p = genPredicate(*a->kids[0]);
          spread_ = std::move(saved);
          if (!p) {
            r = std::nullopt;
            break;
          }
          auto as = create<contract::AssertOp>(loc(*a), p->value);
          as->setAttr("pia.claim",
                      b_.getStringAttr("the spread's postcondition holds for "
                                       "an iteration, whatever the others "
                                       "write"));
        }
      }
      spread_.reset();
      if (r)
        create<mlir::scf::YieldOp>(l);
      popScope();
      if (!r)
        return r;
    }
    // After the loop, every iteration's `ensures` holds:
    // `forall (i in lo .. hi). p`.
    for (const syntax::NodePtr &a : annots.kids) {
      auto q = std::make_unique<Node>();
      q->kind = NodeKind::Quantifier;
      q->text = "forall";
      q->loc = a->loc;
      auto binder = std::make_unique<Node>();
      binder->kind = NodeKind::RangeBinder;
      binder->text = pattern.text;
      binder->loc = pattern.loc;
      binder->kids.push_back(syntax::clone(iterable));
      q->kids.push_back(std::move(binder));
      q->kids.push_back(syntax::clone(*a->kids[0]));
      R all = genPredicate(*q);
      if (!all)
        return all;
      create<contract::AssumeOp>(loc(*a), all->value);
    }
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
          Deeper deeper(loopDepth_);
          R r = genExpr(body, Type());
          if (r && !checkLoopMoves()) r = std::nullopt;
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

  // Each `with_arena n (let (a) => body)` in `n` becomes
  // `let a : mutable arena = { mem = #region n; used = 0 } in body`, a `let`
  // marked "arena": `#region n` is n fresh bytes, and the `let`'s end is
  // where they are freed, so nothing borrowed from `a` may outlive it.
  // A malformed one is left for genApply to report.
  static void desugarArenas(syntax::NodePtr &n) {
    for (syntax::NodePtr &k : n->kids) desugarArenas(k);
    if (n->kind != NodeKind::Apply || n->kids.size() != 3) return;
    const Node &f = *n->kids[0];
    const Node &lam = *n->kids[2];
    if (f.kind != NodeKind::Name || f.text != "with_arena" ||
        !f.flags.empty() || n->kids[1]->kind != NodeKind::IntLit ||
        lam.kind != NodeKind::Lambda || lam.kids.size() != 2 ||
        lam.kids[0]->kind != NodeKind::LParam ||
        lam.kids[0]->kids.empty() ||
        lam.kids[0]->kids[0]->kind != NodeKind::PVar ||
        (lam.kids[0]->kids.size() > 1 &&
         lam.kids[0]->kids[1]->kind != NodeKind::None))
      return;
    using syntax::makeNode;
    syntax::SourceLoc at = n->loc;
    auto let = makeNode(NodeKind::LetIn, lam.kids[0]->loc,
                        lam.kids[0]->kids[0]->text);
    let->flags = "arena";
    let->add(makeNode(NodeKind::Params, at));
    Node *ret = let->add(makeNode(NodeKind::RetAnnot, at));
    Node *annot = ret->add(makeNode(NodeKind::Annot, at));
    annot->add(makeNode(NodeKind::Modifiers, at, "mutable"));
    annot->add(makeNode(NodeKind::TypeName, at, "arena"));
    annot->add(makeNode(NodeKind::None, at));
    ret->add(makeNode(NodeKind::Attrs, at));
    let->add(makeNode(NodeKind::Contracts, at));
    Node *rec = let->add(makeNode(NodeKind::RecordLit, at));
    Node *mem = rec->add(makeNode(NodeKind::FieldInit, at, "mem"));
    Node *region = mem->add(makeNode(NodeKind::Apply, at));
    region->flags = "region";
    region->add(makeNode(NodeKind::Name, at, "#region"));
    region->add(std::move(n->kids[1]));
    Node *used = rec->add(makeNode(NodeKind::FieldInit, at, "used"));
    used->add(makeNode(NodeKind::IntLit, at, "0"));
    let->add(std::move(n->kids[2]->kids[1]));
    n = std::move(let);
  }

  static bool mentions(const Node &n, llvm::StringRef name) {
    if (n.kind == NodeKind::Name && n.text == name) return true;
    for (const syntax::NodePtr &k : n.kids)
      if (mentions(*k, name)) return true;
    return false;
  }

  static bool definesItem(const Node &program, llvm::StringRef name) {
    for (const syntax::NodePtr &k : program.kids)
      if (k->kind == NodeKind::LetItem && k->text == name) return true;
    return false;
  }

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
      case NodeKind::Defer:  // cleanup runs later, and cannot fail
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
    {
      BindingPtr h = bind(hidden, r->value, r->type, false);
      h->lenders = lendersOf(*t.kids[0]);
      h->writable = writable(*t.kids[0]);
    }
    R out = genExpr(chain, expected);
    popScope();
    passLenders(n, chain);
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
    if (frames_.empty()) {
      R out = genExpr(r, expected);
      passLenders(n, r);
      return out;
    }
    if (frames_.back().tails.count(&n)) addTails(r);
    frames_.back().defers.push_back(&d);
    R out = genExpr(r, expected);
    frames_.back().defers.pop_back();
    passLenders(n, r);
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
    // `let sq = let (x : i32) : i32 => x * x in sq 3` (ADR 0044): the
    // lambda is a function, and `sq` its name in the body.
    std::optional<Captures> letCaps;
    if (n.kids[3]->kind == NodeKind::Lambda && ret.kind == NodeKind::None &&
        !contract_ && !ghost_) {
      letCaps = capturesOf(*n.kids[3]);
      if (!letCaps) return std::nullopt;
    }
    if (letCaps && letCaps->empty()) {
      if (!checkFresh(n.text, n.loc)) return std::nullopt;
      std::optional<std::string> symbol =
          liftLambda(*n.kids[3], nullptr, {}, "");
      if (!symbol) return std::nullopt;
      NodePtr body = syntax::clone(*n.kids[4]);
      std::map<std::string, std::string> rename{{n.text, *symbol}};
      if (body->kind == NodeKind::Name && body->text == n.text)
        body->text = *symbol;
      renameNames(*body, rename, nullptr);
      return genExpr(*keep(std::move(body)), expected);
    }
    // `let spec ref : mutable [u8; 4096] = zeros`: spec state (ADR 0058).
    bool isSpecLet = hasFlag(n, "spec");
    Type declared;
    std::string modifiers;
    if (ret.kind == NodeKind::RetAnnot && !ret.kids.empty() &&
        ret.kids[0]->kind == NodeKind::Annot) {
      modifiers = ret.kids[0]->kids[0]->text;
      declared = types_.resolveAnnot(*ret.kids[0]);
      if (!declared) return std::nullopt;
      if (!contract_ && !ghost_ && !isSpecLet)
        if (specInBuffer(declared))
          return fail(*ret.kids[0], "'" + n.text + "' has " +
                                        specInBufferMessage(declared));
      if (ret.kids.size() > 1 && !ret.kids[1]->kids.empty())
        return fail(*ret.kids[1]->kids[0],
                    "attributes on a local 'let' are not supported yet");
    }
    const Node &valueNode = *n.kids[3];
    if (isSpecLet) {
      if (contract_ || ghost_)
        return fail(n, "'let spec' makes spec state in code; in a contract, "
                       "spec function or lemma everything is already spec, "
                       "so drop 'spec'");
      if (!declared)
        return fail(n, "a spec local needs its type, as in 'let spec " +
                           n.text + " : mutable [u8; 4096] = zeros'");
      if (!mlir::isa<ArrayType>(declared) && !isSpecScalar(declared))
        return fail(*ret.kids[0],
                    "a spec local is a fixed array, as in 'let spec " +
                        n.text + " : mutable [u8; 4096] = zeros', for now; "
                        "a spec number is an 'int' (ADR 0058)");
    }
    // A local array that is `mutable`, or whose literal computes its
    // elements, has storage of its own: a fresh array, filled from the
    // literal's elements or copied from the value. Arrays are values, so
    // a write through it reaches nothing else. So does a spec array, and
    // one made with `zeros`.
    auto localArray = mlir::dyn_cast_or_null<ArrayType>(declared);
    bool ownStorage = false;
    if (localArray && !contract_ && !ghost_) {
      bool isMut = sema::hasModifier(modifiers, "mutable");
      bool computed = valueNode.kind == NodeKind::ListLit &&
                      !constantElements(valueNode);
      ownStorage = isMut || computed || isSpecLet || isZeros(valueNode);
    }
    R v;
    if (ownStorage && isSpecLet) {
      // Its value is specification, which may read other spec state, and
      // its storage is marked for codegen to erase.
      contract_ = true;
      v = genLocalArray(valueNode, localArray);
      contract_ = false;
      if (v)
        v->value.getDefiningOp()->setAttr(PiaDialect::getSpecStateAttrName(),
                                          b_.getUnitAttr());
    } else if (ownStorage) {
      v = genLocalArray(valueNode, localArray);
    } else if (isSpecLet) {
      contract_ = true;
      v = genExpr(valueNode, declared);
      contract_ = false;
    } else {
      v = genExpr(valueNode, declared);
    }
    if (!v) return v;
    if (declared) {
      v = coerce(*v, declared, valueNode);
      if (!v) return v;
    }
    if (isUnit(v->type))
      return fail(valueNode, "'" + n.text + "' would have type unit");
    if (mlir::isa<AtomicType>(v->type) &&
        sema::hasModifier(modifiers, "mutable"))
      return fail(n, "'" + n.text +
                         "' is an atomic cell, which its "
                         "operations change in place; it is never reassigned, "
                         "so drop 'mutable'");
    if (!checkFresh(n.text, n.loc)) return std::nullopt;
    if (n.flags == "arena" && !mayBorrow(v->type))
      return fail(n, "'arena' must be a record holding the region, as in "
                     "'type { mem : [u8]; used : usize }'");
    if (const Node *l = sema::findLender(ret))
      return fail(*l, "'borrowed(" + l->text + ")' names the lender of a "
                      "function's result; a local's lenders come from its "
                      "value");
    pushScope();
    BindingPtr b =
        bind(n.text, v->value, v->type, sema::hasModifier(modifiers, "mutable"));
    b->lenders = lendersOf(valueNode);
    b->writable = writable(valueNode);
    b->closure = valueNode.kind == NodeKind::Lambda;
    // A closure that writes a capture is threaded through its calls.
    if (auto r = closureRefs_.find(&valueNode); r != closureRefs_.end() &&
                                                !r->second.empty()) {
      b->refs = r->second;
      b->isMutable = true;
    }
    b->scope = n.kids[4].get();
    b->spec = isSpecLet;
    // A local array's storage is on the stack, so it lends itself: it can
    // be read, written when `mutable`, and passed on, but nothing holding
    // it outlives the `let`.
    if (ownStorage) {
      b->lenders = {b};
      b->writable = sema::hasModifier(modifiers, "mutable");
    }
    // A `with_arena`'s arena lends its own memory: it is borrowed from
    // itself, so neither it nor anything allocated in it outlives the
    // `let` (#70).
    if (n.flags == "arena") {
      b->lenders = {b};
      b->writable = true;
      b->arena = true;
    }
    // A value with a `drop` is dropped at every exit from its scope that
    // has not consumed it (#85), as if by a `defer` registered here.
    const Node *bodyNode = n.kids[4].get();
    const Node *drop = nullptr;
    if (needsDrop(b)) {
      drop = &dropNode(n.text, n.loc);
      bodyNode = keep(withCleanup(*bodyNode, *drop));
      if (!frames_.empty()) {
        if (frames_.back().tails.count(&n)) addTails(*bodyNode);
        frames_.back().defers.push_back(drop);
      }
    }
    b->scope = bodyNode;  // with its drop, which uses it last
    R body = genExpr(*bodyNode, expected);
    if (drop && !frames_.empty()) frames_.back().defers.pop_back();
    if (body && !consumed(b, n.loc)) body = std::nullopt;
    if (body && !borrowsEnd(b, n, *bodyNode)) body = std::nullopt;
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
  // Exported function symbols (ADR 0039), each with its module's path, or
  // empty for a plain C name.
  std::map<std::string, std::string> exports_;
  // The module whose functions the code being generated may call by their
  // own names: the module of an imported generic function or concept.
  std::string adlModule_;
  // Each exported function's name for linking and its C entry point.
  std::map<std::string, std::string> linkNames_;
  // The exported functions whose C entry points keep their plain names.
  std::set<std::string> abiC_;
  // The program's top-level type items, by name.
  std::vector<std::pair<std::string, const Node *>> typeItems_;
  unsigned matchCounter_ = 0;
  std::vector<syntax::NodePtr> matchTrees_;
  std::deque<Frame> frames_;
  // The locals moved so far on the path being generated (`moved`), and the
  // loops open there.
  std::map<BindingPtr, Move> moved_;
  // Elements of buffers that own their slices read as values: moved out
  // of a writable buffer, with the store that empties the one left behind,
  // or copied out of one that cannot be written (ADR 0048, section 6).
  std::map<const Node *, mlir::Operation *> movedOut_;
  std::map<const Node *, syntax::SourceLoc> copiedOut_;
  unsigned loopDepth_ = 0;
  // What each expression generated so far is borrowed from (#70).
  std::map<const Node *, std::vector<BindingPtr>> lent_;
  std::map<std::string, BindingPtr> regionBindings_;  // per function
  std::set<const void *> lentTypes_;  // the types borrowed results borrow
  std::set<const Node *> writable_;    // borrowed buffers that may be written
  std::vector<Value> threadedResults_;  // the last call's threaded values
  std::set<const void *> linear_;  // the `@linear` types
  std::set<std::string> linearGenerics_;  // generic types marked `@linear`
  Type dropping_;                  // the type a `drop` being generated takes
  const Node *unsafeAt_ = nullptr; // the call an `unsafe` marks
  unsigned tryCounter_ = 0;
  // The prelude's types (`result`, `arena`), when the program does not
  // define them.
  syntax::NodePtr prelude_;
  syntax::NodePtr functionConcept_;
  bool usesArenas_ = false;  // the program has a `with_arena`
  std::vector<std::map<std::string, BindingPtr>> scopes_;
  bool contract_ = false;
  OverflowMode overflow_ = OverflowMode::proof;
  // The expression an `@wrap`-style mode was written on, and the mode: an
  // atomic add takes only a mode stated on itself (ADR 0052).
  const Node *statedNode_ = nullptr;
  std::optional<OverflowMode> statedMode_;
  unsigned fuel_ = 0;  // @fuel(n) on the function being generated
  // @variadic(n) on the foreign declaration being generated (ADR 0051).
  std::optional<unsigned> variadic_;
  const Node *variadicNode_ = nullptr;
  std::string solver_;  // @solver(...) on it (ADR 0036)
  bool ghost_ = false;  // generating a spec function or a lemma
  std::vector<const Node *> triggers_;  // an axiom's @trigger attributes
  TheoryInfo theoryInfo_;  // models and their obligations (ADR 0036)
  RegionInfo regionInfo_;  // fields that borrow from a region (ADR 0042)
  bool trusted_ = false;   // the file is marked @trusted (ADR 0023)
  std::deque<std::string> pendingInstances_;  // generic instances to generate
  // Lemmas queued and functions matched to requirements, in order, so a
  // concept check can tell which are its own (certify).
  std::vector<std::string> queuedLog_, matchedLog_;
  // Lemma symbol -> the module whose proof it is (ADR 0039, step 6).
  std::map<std::string, std::string> certified_;
  // Who requires a contract lemma's checks (`requirer_`, as "the interface
  // 'I'"), and the claim each lemma's assertions make (pia.assert_claim).
  std::string requirer_;
  std::map<std::string, std::string> assertClaims_;
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
  // Generics proved only at their instances (ADR 0043): where, which, why.
  struct NotParametric {
    std::string where, generic, why;
  };
  std::vector<NotParametric> notParametric_;
  std::set<std::string> promised_;
  // Each promised concept's name and arguments, for its laws (ADR 0043).
  std::map<std::string, std::pair<std::string, std::vector<Type>>> promisedArgs_;
  std::map<std::string, std::vector<sema::FuncSig *>> promisedFns_;
  std::deque<sema::FuncSig> promisedSigs_;
  // Each written function name and the symbols it may call (ADR 0034).
  std::map<std::string, std::vector<std::string>> overloads_;
  // The concepts and arguments being decided (unmet), and whether a
  // generic's constraints are being checked for meeting a requirement.
  std::set<std::string> deciding_;
  bool meetingGeneric_ = false;
  // Higher-order functions by their written name (ADR 0044): called only
  // through their specialisations.
  std::map<std::string, std::vector<sema::FuncSig>> hofs_;
  // The `apply`s of lambdas with referenced captures (ADR 0044).
  std::set<std::string> effectful_;
  std::string closureName_;  // the closure type liftLambda makes `apply` for
  // Higher-order functions proved once, by name, and the specialisations
  // each proof discharges (ADR 0044, step 6).
  std::map<std::string, std::string> hofProof_, provedBy_;
  std::map<const Node *, std::vector<std::pair<std::string, BindingPtr>>>
      closureRefs_;
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

namespace {
mlir::OwningOpRef<mlir::ModuleOp> generateOnce(const syntax::Node &program,
                                               std::string_view filename,
                                               mlir::MLIRContext &ctx,
                                               syntax::Diagnostics &diags,
                                               const Options &options);
}  // namespace

mlir::OwningOpRef<mlir::ModuleOp> generate(const syntax::Node &programIn,
                                           std::string_view filename,
                                           mlir::MLIRContext &ctx,
                                           syntax::Diagnostics &diags,
                                           const Options &options) {
  loadDialects(ctx);
  if (!hasErasedBoxes(programIn))
    return generateOnce(programIn, filename, ctx, diags, options);
  // A box over a concept (ADR 0046) becomes its own record and theory. A
  // first pass, with a stand-in for the box, finds the types the module
  // widens to each concept; the second makes `box C` their tagged union
  // (step 5), the module's closed world.
  syntax::NodePtr first = syntax::clone(programIn);
  expandErasedBoxes(*first, options.source, diags);
  if (diags.hasErrors()) return nullptr;
  std::map<std::string, std::vector<std::string>> widened;
  {
    syntax::Diagnostics scratch;
    auto module = generateOnce(*first, filename, ctx, scratch, options);
    if (scratch.hasErrors() || !module) {
      for (const syntax::Diagnostic &d : scratch.errors())
        diags.error(d.loc, d.message);
      return nullptr;
    }
    for (auto f : module->getOps<mlir::func::FuncOp>()) {
      llvm::StringRef name = f.getSymName();
      if (!name.starts_with("widen<") || !name.ends_with(">") ||
          f.getNumResults() != 1)
        continue;
      auto rt = mlir::dyn_cast<RecordType>(f.getFunctionType().getResult(0));
      if (!rt || !rt.getName().starts_with("box_")) continue;
      std::string t = name.drop_front(6).drop_back(1).str();
      if (t.find_first_of("<>, ") != std::string::npos) {
        diags.error(programIn.loc,
                    "a box over a concept holds named types for now, and '" +
                        t + "' is an instance of a generic one (ADR 0046)");
        return nullptr;
      }
      // box_C: the concept is the name after `box_`.
      std::string c = rt.getName().drop_front(4).str();
      auto &ts = widened[c];
      if (!llvm::is_contained(ts, t)) ts.push_back(t);
    }
  }
  std::map<std::string, std::vector<std::string>> byConcept;
  for (const syntax::NodePtr &item : programIn.kids)
    if (syntax::isConceptItem(*item)) {
      std::string m;
      for (char ch : item->text) m += (ch == '.' ? '_' : ch);
      if (auto w = widened.find(m); w != widened.end())
        byConcept[item->text] = w->second;
    }
  syntax::NodePtr second = syntax::clone(programIn);
  expandErasedBoxes(*second, options.source, diags, &byConcept);
  if (diags.hasErrors()) return nullptr;
  return generateOnce(*second, filename, ctx, diags, options);
}

namespace {
mlir::OwningOpRef<mlir::ModuleOp> generateOnce(const syntax::Node &program,
                                               std::string_view filename,
                                               mlir::MLIRContext &ctx,
                                               syntax::Diagnostics &diags,
                                               const Options &options) {
  // Region parameters (ADR 0042, step 2) are erased into marks first.
  syntax::NodePtr erased;
  RegionInfo regions;
  if (hasRegions(program)) {
    erased = syntax::clone(program);
    eraseRegions(*erased, diags, regions);
    if (diags.hasErrors()) return nullptr;
  }
  // A program that names `Target` gets the built-in theory and the model
  // of the target it is compiled for (ADR 0049).
  syntax::NodePtr targeted;
  std::map<std::string, std::string> targetOf;
  if (usesTargetTheory(erased ? *erased : program)) {
    targeted = syntax::clone(erased ? *erased : program);
    if (!addTargetTheory(*targeted, options.triple, diags, &targetOf))
      return nullptr;
  }
  // And one that names `Memory` gets RC11 (ADR 0052, section 4).
  if (usesMemoryTheory(targeted ? *targeted : erased ? *erased : program)) {
    if (!targeted)
      targeted = syntax::clone(erased ? *erased : program);
    if (!addMemoryTheory(*targeted, diags))
      return nullptr;
  }
  const syntax::Node &source = targeted ? *targeted
                               : erased ? *erased
                                        : program;
  // Theories (ADR 0036) become ordinary items with qualified names.
  if (hasTheories(source)) {
    syntax::NodePtr flat = syntax::clone(source);
    TheoryInfo info;
    flattenTheories(*flat, diags, &info);
    if (diags.hasErrors()) return nullptr;
    info.targetOf = std::move(targetOf);
    // Trust grants, `import T trusting`, for --trust-report.
    llvm::SmallVector<mlir::Attribute> grants;
    for (const auto &[theory, at] : info.trusting)
      grants.push_back(mlir::StringAttr::get(
          &ctx, theory + " " + std::string(filename) + ":" +
                    std::to_string(at.line) + ":" + std::to_string(at.column)));
    Gen gen(ctx, filename, diags, options);
    gen.setTheoryInfo(std::move(info));
    gen.setRegionInfo(regions);
    gen.setTrusted(isTrustedFile(program));
    auto module = gen.run(*flat);
    if (module && !grants.empty())
      (*module)->setAttr("pia.trusting", mlir::ArrayAttr::get(&ctx, grants));
    return module;
  }
  Gen gen(ctx, filename, diags, options);
  gen.setRegionInfo(std::move(regions));
  gen.setTrusted(isTrustedFile(program));
  return gen.run(source);
}
}  // namespace

}  // namespace pia::irgen
