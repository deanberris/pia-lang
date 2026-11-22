#include "verify/Verifier.h"

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <functional>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "dialect/PiaDialect.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/STLFunctionalExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SMT/IR/SMTDialect.h"
#include "mlir/Dialect/SMT/IR/SMTOps.h"
#include "mlir/Dialect/SMT/IR/SMTTypes.h"
#include "mlir/IR/Builders.h"
#include "mlir/Target/SMTLIB/ExportSMTLIB.h"
#include "sema/Sema.h"
#include "transforms/ScalarizeRecords.h"
#include "verify/Triggers.h"
#include "z3++.h"

namespace pia::verify {

using contract::ObligationKind;
using llvm::APInt;
using mlir::Location;
using mlir::OpBuilder;
using mlir::Operation;
using mlir::Type;
using mlir::Value;

std::string formatLoc(Location loc) {
  std::string out = "?";
  loc->walk([&](Location l) {
    if (auto f = mlir::dyn_cast<mlir::FileLineColLoc>(l)) {
      out = f.getFilename().str() + ":" + std::to_string(f.getLine()) + ":" +
            std::to_string(f.getColumn());
      return mlir::WalkResult::interrupt();
    }
    return mlir::WalkResult::advance();
  });
  return out;
}

namespace {

constexpr unsigned kBoundWidth = 128;

// The SMT-LIB sort of `real` (see Encoder::realType).
constexpr llvm::StringLiteral kRealSort = "Real";

// The SMT-LIB functions the encoder declares under their own names because
// the smt dialect has no op for them (Encoder::interpreted).
constexpr llvm::StringLiteral kInterpreted[] = {
    "+", "-", "*", "/", "<", "<=", ">", ">=", "to_real", "bv2int"};

// The exported query with the declarations of interpreted functions and of
// the Real sort removed, so that Z3 reads them as SMT-LIB's own.
std::string interpretedSMTLIB(const std::string &smtlib) {
  std::string out;
  size_t pos = 0;
  while (pos < smtlib.size()) {
    size_t end = smtlib.find('\n', pos);
    if (end == std::string::npos) end = smtlib.size();
    llvm::StringRef line(smtlib.data() + pos, end - pos);
    pos = end + 1;
    if (line == ("(declare-sort " + kRealSort + " 0)").str()) continue;
    bool drop = false;
    for (llvm::StringRef f : kInterpreted)
      if (line.starts_with(("(declare-fun " + f + " (").str())) drop = true;
    if (drop) continue;
    out.append(line.begin(), line.end()).push_back('\n');
  }
  return out;
}

APInt bound(const APInt &v, unsigned width) { return v.sextOrTrunc(width); }

// A proof goal, found by walking a function in order. The same walk runs
// once to list the goals and once per goal to build its query, so goals
// are identified by their position.
struct Goal {
  ObligationKind kind;
  Operation *op;
  std::string claim;
  bool skipped = false;
  std::string reason;          // why it was skipped
  bool byIntervals = false;    // the operand types already prove it
};

std::string opSpelling(Operation *op) {
  if (mlir::isa<AddOp>(op)) return "'+'";
  if (mlir::isa<SubOp>(op)) return "'-'";
  if (mlir::isa<MulOp>(op)) return "'*'";
  if (mlir::isa<DivOp>(op)) return "'/'";
  if (mlir::isa<RemOp>(op)) return "'%'";
  if (mlir::isa<BAndOp>(op)) return "'&'";
  if (mlir::isa<BOrOp>(op)) return "'|'";
  if (mlir::isa<BXorOp>(op)) return "'^'";
  if (mlir::isa<ShlOp>(op)) return "'<<'";
  if (mlir::isa<ShrOp>(op)) return "'>>'";
  return "'" + op->getName().getStringRef().str() + "'";
}

template <typename T>
std::optional<OverflowMode> overflowMode(Operation *op) {
  if (auto o = mlir::dyn_cast<T>(op)) return o.getOverflow();
  return std::nullopt;
}

std::optional<OverflowMode> arithMode(Operation *op) {
  if (auto m = overflowMode<AddOp>(op)) return m;
  if (auto m = overflowMode<SubOp>(op)) return m;
  if (auto m = overflowMode<MulOp>(op)) return m;
  if (auto m = overflowMode<DivOp>(op)) return m;
  if (auto m = overflowMode<RemOp>(op)) return m;
  if (auto m = overflowMode<BAndOp>(op)) return m;
  if (auto m = overflowMode<BOrOp>(op)) return m;
  if (auto m = overflowMode<BXorOp>(op)) return m;
  if (auto m = overflowMode<ShlOp>(op)) return m;
  if (auto m = overflowMode<ShrOp>(op)) return m;
  return std::nullopt;
}

// The storage width of a shift's left operand: the amount must be below it.
unsigned shiftWidth(Operation *op) {
  return mlir::cast<IntType>(op->getOperand(0).getType()).getStorageWidth();
}

// The buffer whose storage a value views: itself, unless it is a slice.
Value rootBuffer(Value buffer) {
  while (auto s = buffer.getDefiningOp<SliceOp>()) buffer = s.getBuffer();
  return buffer;
}

std::string shiftClaim(Operation *op) {
  return "the shift amount is less than " + std::to_string(shiftWidth(op));
}

bool isContractSink(Operation *op) {
  return mlir::isa<contract::RequiresOp, contract::EnsuresOp,
                   contract::InvariantOp, contract::DecreasesOp,
                   contract::AssertOp, contract::AssumeOp,
                   contract::ObligationOp, contract::OldOp,
                   contract::YieldOp, contract::TriggerOp>(op);
}

bool insideQuantifier(Operation *op) {
  return op->getParentOfType<contract::ForallOp>() ||
         op->getParentOfType<contract::ExistsOp>();
}

// Specification ops compute only what contracts read. They have exact
// semantics and no obligations of their own: `ensures result <= a + b`
// means the mathematical sum, and a guarded `xs.[i]` in a contract may
// read past the end without failing.
llvm::DenseSet<Operation *> specOps(mlir::func::FuncOp fn) {
  llvm::DenseSet<Operation *> spec;
  bool changed = true;
  while (changed) {
    changed = false;
    fn.walk([&](Operation *op) {
      if (spec.contains(op)) return;
      bool isSpec = false;
      if (insideQuantifier(op)) {
        isSpec = true;
      } else if (auto y = mlir::dyn_cast<mlir::scf::YieldOp>(op)) {
        isSpec = mlir::isa<mlir::scf::IfOp>(y->getParentOp()) &&
                 spec.contains(y->getParentOp());
      } else if (op->getNumResults() > 0 &&
                 !mlir::isa<mlir::func::CallOp, mlir::scf::ForOp,
                            mlir::scf::WhileOp>(op)) {
        isSpec = true;
        bool anyUser = false;
        for (Value r : op->getResults())
          for (Operation *u : r.getUsers()) {
            anyUser = true;
            if (!isContractSink(u) && !spec.contains(u)) isSpec = false;
          }
        if (!anyUser) isSpec = false;
        if (auto ifOp = mlir::dyn_cast<mlir::scf::IfOp>(op)) {
          // Only a pure `if` is a specification.
          ifOp.walk([&](Operation *inner) {
            if (mlir::isa<StoreOp, mlir::func::CallOp>(inner)) isSpec = false;
          });
        }
      }
      if (isSpec) {
        spec.insert(op);
        changed = true;
      }
    });
  }
  return spec;
}

// The function at the heart of the verifier: a symbolic walk of one
// function that encodes its ops in the smt dialect.
class Encoder {
 public:
  // Lists the goals when `target` is negative; otherwise stops at goal
  // `target` and asserts its negation.
  Encoder(mlir::ModuleOp module, mlir::func::FuncOp fn, unsigned width,
          int target, OpBuilder &builder, std::vector<Goal> &goals)
      : module_(module),
        fn_(fn),
        width_(width),
        target_(target),
        b_(builder),
        goals_(goals),
        ctx_(builder.getContext()),
        loc_(builder.getUnknownLoc()),
        spec_(specOps(fn)),
        solverBlock_(builder.getInsertionBlock()) {}

  // The sort of a declared constant, so its model value can be read.
  enum class Sort { BitVector, Bool, Int, Real, Uninterpreted };

  struct Decl {
    std::string exported;  // the SMT-LIB name
    std::string display;   // the name shown in a counterexample
    Sort sort;
  };

  void run() {
    declareSpecFunctions();
    mlir::Block &entry = fn_.getBody().front();
    for (unsigned i = 0; i < entry.getNumArguments(); ++i) declareParam(entry.getArgument(i), i);
    entryArrays_ = arrays_;
    walkBlock(entry, nullptr);
  }

  bool reachedTarget() const { return done_; }

  // The consistency check of a trusted theory (ADR 0036): every axiom of
  // `theory`, and, by the relevance closure, the axioms of the theories
  // they use, with nothing to prove. Satisfiable means consistent.
  void assertTheory(const std::string &theory) {
    declareSpecFunctions();
    goalAssert_ = create<mlir::smt::AssertOp>(boolConst(true));
    for (auto f : module_.getOps<mlir::func::FuncOp>())
      if (f->hasAttr(PiaDialect::getAxiomAttrName()) && theoryOf(f) == theory) {
        // Its functions count as used, so the closure sees them.
        f.walk([&](mlir::func::CallOp c) {
          if (auto callee = calleeOf(c)) noteTheoryUse(callee);
        });
        assertAxiom(f, axiomTriggers(module_, f));
      }
    addAxioms(false);
  }
  const std::vector<std::string> &sentAxioms() const { return sentAxioms_; }
  // The `assume`s the query asserts, as `assume file:line:col`.
  const std::vector<std::string> &sentAssumes() const { return sentAssumes_; }
  const std::set<std::string> &sorts() const { return sorts_; }
  bool usesTheories() const { return !theoryFuns_.empty(); }

  // The axioms a query gets (ADR 0036, "Build time"). With `all` unset,
  // the relevance closure: an axiom is added when every function of one of
  // its triggers is in the query, and the functions it brings can fire
  // more, to a fixed point. With `all`, every axiom of every theory the
  // query mentions, for the fallback. A query that applies no theory
  // function gets none, so it is exactly what it was without theories.
  void addAxioms(bool all) {
    if (theoryFuns_.empty() || !goalAssert_) return;
    std::vector<mlir::func::FuncOp> axioms;
    for (auto f : module_.getOps<mlir::func::FuncOp>())
      if (f->hasAttr(PiaDialect::getAxiomAttrName())) axioms.push_back(f);
    std::vector<AxiomTriggers> triggers;
    for (auto f : axioms) triggers.push_back(axiomTriggers(module_, f));
    std::vector<bool> sent(axioms.size(), false);
    for (size_t i = 0; i < axioms.size(); ++i)
      sent[i] = llvm::is_contained(sentAxioms_, axioms[i].getSymName().str());
    for (bool changed = true; changed;) {
      changed = false;
      std::set<std::string> theories;
      for (const std::string &f : theoryFuns_)
        theories.insert(llvm::StringRef(f).split('.').first.str());
      for (size_t i = 0; i < axioms.size(); ++i) {
        if (sent[i]) continue;
        bool fire = false;
        if (all) {
          fire = theories.count(theoryOf(axioms[i])) > 0;
        } else if (triggers[i].triggers.empty()) {
          // No parameters: it is a plain fact about its functions.
          fire = true;
          axioms[i].walk([&](mlir::func::CallOp c) {
            if (!theoryFuns_.count(c.getCallee().str())) fire = false;
          });
        } else {
          for (const Trigger &t : triggers[i].triggers) {
            bool covered = true;
            for (const std::string &f : t.functions)
              covered &= theoryFuns_.count(f) > 0;
            fire |= covered;
          }
        }
        if (!fire) continue;
        sent[i] = true;
        changed = true;
        assertAxiom(axioms[i], triggers[i]);
      }
    }
  }
  const std::vector<Decl> &decls() const { return decls_; }
  const std::vector<Decl> &witnesses() const { return witnesses_; }

 private:
  // --- SMT construction -------------------------------------------------

  template <typename OpTy, typename... Args>
  OpTy create(Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
    return OpTy::create(b_, loc_, std::forward<Args>(args)...);
#else
    return b_.create<OpTy>(loc_, std::forward<Args>(args)...);
#endif
  }

  Type bvType() { return mlir::smt::BitVectorType::get(ctx_, width_); }
  Type boolType() { return mlir::smt::BoolType::get(ctx_); }
  Type intType() { return mlir::smt::IntType::get(ctx_); }
  // The upstream smt dialect has no Real sort at our LLVM pin, so `Real`
  // is written as a sort the export would declare, and that declaration is
  // dropped from the SMT-LIB text (interpretedSMTLIB).
  Type realType() {
    return mlir::smt::SortType::get(ctx_, kRealSort);
  }

  static Sort sortKind(Type sort) {
    if (mlir::isa<mlir::smt::BoolType>(sort)) return Sort::Bool;
    if (mlir::isa<mlir::smt::IntType>(sort)) return Sort::Int;
    if (auto s = mlir::dyn_cast<mlir::smt::SortType>(sort))
      return s.getIdentifier().getValue() == kRealSort ? Sort::Real
                                                       : Sort::Uninterpreted;
    return Sort::BitVector;
  }

  Type sortOf(Type t) {
    if (mlir::isa<IntType, mlir::IndexType>(t)) return bvType();
    if (t.isInteger(1)) return boolType();
    if (mlir::isa<UnboundedIntType>(t)) return intType();
    if (mlir::isa<RealType>(t)) return realType();
    // A theory's sort is an uninterpreted SMT sort of the same name.
    if (auto so = mlir::dyn_cast<SortType>(t)) {
      sorts_.insert(so.getName().str());
      return mlir::smt::SortType::get(ctx_, so.getName());
    }
    if (auto a = mlir::dyn_cast<ArrayType>(t)) {
      Type e = sortOf(a.getElementType());
      return e ? mlir::smt::ArrayType::get(ctx_, bvType(), e) : Type();
    }
    if (auto s = mlir::dyn_cast<SliceType>(t)) {
      Type e = sortOf(s.getElementType());
      return e ? mlir::smt::ArrayType::get(ctx_, bvType(), e) : Type();
    }
    return {};
  }

  Value bv(const APInt &v) {
    return create<mlir::smt::BVConstantOp>(bound(v, width_));
  }
  Value bv(int64_t v) { return bv(APInt(64, v, /*isSigned=*/true)); }
  Value boolConst(bool v) {
    return create<mlir::smt::BoolConstantOp>(boolType(), b_.getBoolAttr(v));
  }
  Value bvBin(mlir::StringRef which, Value a, Value c) {
    Type t = bvType();
    if (which == "add") return create<mlir::smt::BVAddOp>(t, a, c);
    if (which == "mul") return create<mlir::smt::BVMulOp>(t, a, c);
    if (which == "sdiv") return create<mlir::smt::BVSDivOp>(t, a, c);
    if (which == "srem") return create<mlir::smt::BVSRemOp>(t, a, c);
    if (which == "smod") return create<mlir::smt::BVSModOp>(t, a, c);
    // On sign-extended operands these are exact: the encoding is wide
    // enough for every shifted value (encodingWidth).
    if (which == "and") return create<mlir::smt::BVAndOp>(t, a, c);
    if (which == "or") return create<mlir::smt::BVOrOp>(t, a, c);
    if (which == "xor") return create<mlir::smt::BVXOrOp>(t, a, c);
    if (which == "shl") return create<mlir::smt::BVShlOp>(t, a, c);
    if (which == "ashr") return create<mlir::smt::BVAShrOp>(t, a, c);
    Value neg = create<mlir::smt::BVNegOp>(t, c);  // "sub"
    return create<mlir::smt::BVAddOp>(t, a, neg);
  }
  Value cmp(mlir::smt::BVCmpPredicate p, Value a, Value c) {
    return create<mlir::smt::BVCmpOp>(boolType(), p, a, c);
  }
  Value andOf(Value a, Value c) {
    return create<mlir::smt::AndOp>(boolType(), mlir::ValueRange{a, c});
  }
  Value orOf(Value a, Value c) {
    return create<mlir::smt::OrOp>(boolType(), mlir::ValueRange{a, c});
  }
  Value notOf(Value a) { return create<mlir::smt::NotOp>(boolType(), a); }
  Value implies(Value a, Value c) {
    return create<mlir::smt::ImpliesOp>(boolType(), a, c);
  }
  Value eq(Value a, Value c) {
    return create<mlir::smt::EqOp>(boolType(), mlir::ValueRange{a, c});
  }
  Value ite(Value c, Value t, Value e) {
    return create<mlir::smt::IteOp>(t.getType(), c, t, e);
  }
  Operation *assertTerm(Value t) { return create<mlir::smt::AssertOp>(t); }

  Value inRange(Value t, IntType ty) {
    using P = mlir::smt::BVCmpPredicate;
    return andOf(cmp(P::sle, bv(ty.getLo()), t), cmp(P::sle, t, bv(ty.getHi())));
  }

  Value declare(Type sort, const std::string &display, bool record = true) {
    std::string name = "pia_" + std::to_string(nextName_++);
    Value v = create<mlir::smt::DeclareFunOp>(sort, b_.getStringAttr(name));
    if (record && !display.empty())
      decls_.push_back({name, display, sortKind(sort)});
    return v;
  }

  // --- int and real (ADR 0036) -------------------------------------------

  // An SMT-LIB function that the smt dialect has no op for, such as Real
  // addition: declared under its SMT-LIB name, once per query, at the top
  // of the solver block. interpretedSMTLIB drops the declaration from the
  // exported text, so Z3 reads each use as the interpreted function.
  Value interpreted(llvm::StringRef name, llvm::ArrayRef<Type> domain,
                    Type range) {
    auto it = interpreted_.find(name);
    if (it != interpreted_.end()) return it->second;
    OpBuilder::InsertionGuard guard(b_);
    b_.setInsertionPointToStart(solverBlock_);
    Value f = create<mlir::smt::DeclareFunOp>(
        mlir::smt::SMTFuncType::get(ctx_, domain, range),
        b_.getStringAttr(name));
    interpreted_[name] = f;
    return f;
  }
  Value apply(llvm::StringRef name, llvm::ArrayRef<Value> args, Type range) {
    llvm::SmallVector<Type> domain;
    for (Value a : args) domain.push_back(a.getType());
    return create<mlir::smt::ApplyFuncOp>(range, interpreted(name, domain, range),
                                          mlir::ValueRange(args));
  }

  Value intConst(const APInt &v) {
    unsigned bits = std::max(64u, v.getBitWidth() + 1);
    APInt w = v.sext(bits);
    // SMT-LIB numerals are never negative: -n is (- 0 n).
    APInt mag = w.isNegative() ? -w : w;
    Value c = create<mlir::smt::IntConstantOp>(
        intType(), b_.getIntegerAttr(b_.getIntegerType(bits), mag));
    if (!w.isNegative()) return c;
    Value zero = create<mlir::smt::IntConstantOp>(
        intType(), b_.getIntegerAttr(b_.getIntegerType(bits), 0));
    return create<mlir::smt::IntSubOp>(intType(), zero, c);
  }
  Value toReal(Value i) { return apply("to_real", {i}, realType()); }

  // `n` or `n/d` (pia.exact.constant) as an Int or Real term.
  Value exactConst(llvm::StringRef text, bool real) {
    auto [num, den] = text.split('/');
    unsigned bits = 8 + 4 * static_cast<unsigned>(text.size());
    APInt n(bits, num, 10);
    if (!real) return intConst(n);
    Value r = toReal(intConst(n));
    if (den.empty()) return r;
    return apply("/", {r, toReal(intConst(APInt(bits, den, 10)))}, realType());
  }

  // A signed bit-vector as the Int it stands for: Z3's bv2int reads it
  // unsigned, so 2^w is taken off a negative value.
  Value bvToInt(Value x) {
    using P = mlir::smt::BVCmpPredicate;
    Value u = apply("bv2int", {x}, intType());
    Value neg = cmp(P::slt, x, bv(0));
    Value two = intConst(APInt::getOneBitSet(width_ + 2, width_));
    Value zero = intConst(APInt(64, 0));
    return create<mlir::smt::IntSubOp>(intType(), u, ite(neg, two, zero));
  }

  Value exactArith(Operation *op, Value a, Value c, bool real) {
    if (real) {
      llvm::StringRef name = mlir::isa<ExactAddOp>(op)   ? "+"
                             : mlir::isa<ExactSubOp>(op) ? "-"
                             : mlir::isa<ExactMulOp>(op) ? "*"
                                                         : "/";
      return apply(name, {a, c}, realType());
    }
    if (mlir::isa<ExactAddOp>(op))
      return create<mlir::smt::IntAddOp>(intType(), mlir::ValueRange{a, c});
    if (mlir::isa<ExactMulOp>(op))
      return create<mlir::smt::IntMulOp>(intType(), mlir::ValueRange{a, c});
    return create<mlir::smt::IntSubOp>(intType(), a, c);
  }

  Value exactCmp(CmpPredicate p, Value a, Value c, bool real) {
    if (p == CmpPredicate::eq) return eq(a, c);
    if (p == CmpPredicate::ne) return notOf(eq(a, c));
    if (real) {
      llvm::StringRef name = p == CmpPredicate::lt   ? "<"
                             : p == CmpPredicate::le ? "<="
                             : p == CmpPredicate::gt ? ">"
                                                     : ">=";
      return apply(name, {a, c}, boolType());
    }
    using IP = mlir::smt::IntPredicate;
    IP ip = p == CmpPredicate::lt   ? IP::lt
            : p == CmpPredicate::le ? IP::le
            : p == CmpPredicate::gt ? IP::gt
                                    : IP::ge;
    return create<mlir::smt::IntCmpOp>(boolType(), ip, a, c);
  }

  // A fresh value of a Pia type, with its range assumed.
  std::optional<Value> havoc(Type t, const std::string &display = "") {
    Type sort = sortOf(t);
    if (!sort) return std::nullopt;
    Value v = declare(sort, display, !display.empty());
    if (auto it = mlir::dyn_cast<IntType>(t)) assertTerm(inRange(v, it));
    if (mlir::isa<mlir::IndexType>(t)) assertTerm(inRange(v, indexRange()));
    return v;
  }

  IntType indexRange() {
    return IntType::get(ctx_, APInt(kBoundWidth, 0),
                        APInt::getMaxValue(64).zext(kBoundWidth));
  }

  // --- parameters and buffers ------------------------------------------

  void declareParam(mlir::BlockArgument arg, unsigned index) {
    std::string name = "arg" + std::to_string(index);
    if (auto n = mlir::dyn_cast<mlir::NameLoc>(arg.getLoc()))
      name = n.getName().str();
    Type t = arg.getType();
    if (mlir::isa<ArrayType, SliceType>(t)) {
      Type sort = sortOf(t);
      if (!sort) return;
      arrays_[arg] = declare(sort, "");
      auto shared = fn_.getArgAttrOfType<mlir::IntegerAttr>(
          index, PiaDialect::getLengthOfAttrName());
      if (auto a = mlir::dyn_cast<ArrayType>(t)) {
        lengths_[arg] = bv(APInt(64, a.getLength()));
      } else if (shared) {
        // A field buffer of a slice of records: the record slice has one
        // length, which every field shares.
        lengths_[arg] = lengths_[fn_.getArgument(shared.getInt())];
      } else {
        Value len = declare(bvType(), "len " + name);
        assertTerm(inRange(len, indexRange()));
        lengths_[arg] = len;
      }
      return;
    }
    if (auto v = havoc(t, name)) env_[arg] = *v;
  }

  bool isWritable(Value buffer) {
    auto arg = mlir::dyn_cast<mlir::BlockArgument>(buffer);
    if (!arg || arg.getOwner() != &fn_.getBody().front()) return false;
    auto mods = fn_.getArgAttrOfType<mlir::StringAttr>(
        arg.getArgNumber(), PiaDialect::getModifiersAttrName());
    return mods && (sema::hasModifier(mods.getValue(), "out") ||
                    sema::hasModifier(mods.getValue(), "inout"));
  }

  // --- path conditions and goals ---------------------------------------

  Value pathCondition() {
    Value pc = boolConst(true);
    for (Value c : pc_) pc = andOf(pc, c);
    return pc;
  }

  Operation *assume(Value t) {
    if (pc_.empty()) return assertTerm(t);
    return assertTerm(implies(pathCondition(), t));
  }

  // Registers goal number `counter_`. In the listing walk it records the
  // goal; in a query it asserts the negation at the target and assumes
  // the goal everywhere before it.
  void goal(ObligationKind kind, Operation *op, std::string claim,
            Value term, bool byIntervals,
            std::vector<std::pair<std::string, Value>> witnesses = {}) {
    int index = counter_++;
    if (target_ < 0) {
      Goal g{kind, op, std::move(claim)};
      g.byIntervals = byIntervals;
      goals_.push_back(std::move(g));
      assume(term);
      return;
    }
    if (index != target_) {
      assume(term);
      return;
    }
    for (auto &[label, value] : witnesses) {
      Value w = declare(value.getType(), "", false);
      witnesses_.push_back({mlir::cast<mlir::smt::DeclareFunOp>(
                                w.getDefiningOp()).getNamePrefix()->str(),
                            label, sortKind(value.getType())});
      assertTerm(eq(w, value));
    }
    goalAssert_ = create<mlir::smt::AssertOp>(andOf(pathCondition(), notOf(term)));
    done_ = true;
  }

  // A field buffer's copy of a load, store or slice whose bound the first
  // field's copy carries (transforms/ScalarizeRecords.cpp).
  static bool boundsShared(Operation *op) {
    return op->hasAttr(PiaDialect::getBoundsSharedAttrName());
  }

  // A bounds goal, or only its assumption on an op whose bound is shared.
  void boundsGoal(Operation *op, std::string claim, Value term,
                  bool byIntervals,
                  std::vector<std::pair<std::string, Value>> witnesses) {
    if (boundsShared(op)) {
      assume(term);
      return;
    }
    goal(ObligationKind::inbounds, op, std::move(claim), term, byIntervals,
         std::move(witnesses));
  }

  void skipped(ObligationKind kind, Operation *op, std::string claim,
               std::string reason) {
    counter_++;
    if (target_ < 0) {
      Goal g{kind, op, std::move(claim)};
      g.skipped = true;
      g.reason = std::move(reason);
      goals_.push_back(std::move(g));
    }
  }

  // A loop the encoding cannot follow, such as one whose bounds it cannot
  // encode: every goal inside is skipped, and what the loop computes or
  // writes is unknown afterwards.
  bool skipLoop(Operation *loop) {
    loop->walk([&](Operation *op) {
      if (op == loop) return;
      for (auto &[kind, claim] : describe(op))
        skipped(kind, op, claim, "the loop could not be encoded");
    });
    for (Value r : loop->getResults())
      if (auto v = havoc(r.getType())) env_[r] = *v;
    for (Value buffer : writtenBuffers(loop))
      arrays_[buffer] = declare(arrays_[buffer].getType(), "", false);
    return true;
  }

  // The goals an op raises, without their terms.
  std::vector<std::pair<ObligationKind, std::string>> describe(Operation *op) {
    std::vector<std::pair<ObligationKind, std::string>> out;
    if (mlir::isa<contract::InvariantOp>(op)) {
      out.push_back({ObligationKind::invariant,
                     "the loop invariant holds on entry"});
      out.push_back({ObligationKind::invariant,
                     "the loop invariant holds after each iteration"});
    }
    if (mlir::isa<contract::DecreasesOp>(op) &&
        !mlir::isa<mlir::func::FuncOp>(op->getParentOp()))
      out.push_back({ObligationKind::decreases, "the measure decreases"});
    if (spec_.contains(op) || insideQuantifier(op)) return out;
    if (auto m = arithMode(op)) {
      if (mlir::isa<DivOp, RemOp>(op))
        out.push_back({ObligationKind::nonzero, "the divisor is not zero"});
      if (mlir::isa<ShlOp, ShrOp>(op))
        out.push_back({ObligationKind::shift, shiftClaim(op)});
      if (*m == OverflowMode::proof && !mlir::isa<RemOp>(op))
        out.push_back({ObligationKind::nooverflow,
                       opSpelling(op) + " does not overflow " +
                           sema::typeName(op->getResult(0).getType())});
    }
    if (auto c = mlir::dyn_cast<ConvertOp>(op))
      if (c.getOverflow() == OverflowMode::proof && !c.isWidening())
        out.push_back({ObligationKind::nooverflow,
                       "the value fits in " + sema::typeName(c.getType())});
    if (auto t = mlir::dyn_cast<ToIndexOp>(op))
      if (t.getInput().getType().isSigned())
        out.push_back({ObligationKind::nooverflow, "the index is not negative"});
    if (auto f = mlir::dyn_cast<FromIndexOp>(op))
      if (!f.getType().contains(APInt::getMaxValue(64).zext(kBoundWidth)))
        out.push_back({ObligationKind::nooverflow,
                       "the index fits in " + sema::typeName(f.getType())});
    if (mlir::isa<LoadOp, StoreOp>(op) && !boundsShared(op))
      out.push_back({ObligationKind::inbounds, "the index is within bounds"});
    if (mlir::isa<SliceOp>(op) && !boundsShared(op))
      out.push_back({ObligationKind::inbounds, "the slice is within bounds"});
    if (mlir::isa<AbortOp>(op))
      out.push_back({ObligationKind::assert_, "'abort' is never reached"});
    if (mlir::isa<contract::AssertOp>(op))
      out.push_back({ObligationKind::assert_, "the assertion holds"});
    if (mlir::isa<contract::EnsuresOp>(op))
      out.push_back({ObligationKind::ensures, "the postcondition holds"});
    if (auto o = mlir::dyn_cast<contract::ObligationOp>(op))
      out.push_back({o.getKind(), "the obligation holds"});
    if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
      if (auto callee = module_.lookupSymbol<mlir::func::FuncOp>(call.getCallee()))
        if (!callee.isExternal())
          for (auto r : callee.getBody().front().getOps<contract::RequiresOp>()) {
            (void)r;
            out.push_back({ObligationKind::requires_,
                           "the precondition of '" + call.getCallee().str() +
                               "' holds"});
          }
    return out;
  }

  // --- intervals ---------------------------------------------------------

  using Interval = std::pair<APInt, APInt>;  // 192-bit signed

  static Interval rangeOf(IntType t) {
    return {t.getLo().sextOrTrunc(192), t.getHi().sextOrTrunc(192)};
  }
  static bool within(const Interval &i, IntType t) {
    Interval r = rangeOf(t);
    return r.first.sle(i.first) && i.second.sle(r.second);
  }

  // The values `v` can take, from its type, looking through widening
  // conversions and constants: `a + b` on u8 values widened to u16 adds
  // ranges [0, 255], not [0, 65535].
  static Interval valueRange(Value v) {
    Interval type = rangeOf(mlir::cast<IntType>(v.getType()));
    if (auto c = v.getDefiningOp<ConvertOp>())
      if (c.isWidening()) return valueRange(c.getInput());
    if (auto k = v.getDefiningOp<ConstantOp>()) {
      APInt x = k.getValue().sextOrTrunc(192);
      return {x, x};
    }
    // A proof-mode result is exact, and its own goal keeps it in its type,
    // so its range is the exact range clipped to the type.
    Operation *op = v.getDefiningOp();
    if (op && arithMode(op) == OverflowMode::proof)
      if (auto exact = exactRange(op)) return clip(*exact, type);
    return type;
  }

  static Interval clip(const Interval &i, const Interval &to) {
    return {i.first.slt(to.first) ? to.first : i.first,
            i.second.sgt(to.second) ? to.second : i.second};
  }

  // The exact result range of an arithmetic op on its operand ranges.
  static std::optional<Interval> exactRange(Operation *op) {
    if (!mlir::isa<IntType>(op->getOperand(0).getType()) ||
        !mlir::isa<IntType>(op->getOperand(1).getType()))
      return std::nullopt;
    Interval a = valueRange(op->getOperand(0));
    Interval c = valueRange(op->getOperand(1));
    if (mlir::isa<AddOp>(op))
      return Interval{a.first + c.first, a.second + c.second};
    if (mlir::isa<SubOp>(op))
      return Interval{a.first - c.second, a.second - c.first};
    if (mlir::isa<MulOp>(op)) {
      APInt ps[] = {a.first * c.first, a.first * c.second, a.second * c.first,
                    a.second * c.second};
      APInt lo = ps[0], hi = ps[0];
      for (const APInt &p : ps) {
        if (p.slt(lo)) lo = p;
        if (p.sgt(hi)) hi = p;
      }
      return Interval{lo, hi};
    }
    // Non-negative operands: the quotient lies in [0, a]. Division by zero
    // is its own goal.
    if (mlir::isa<DivOp>(op) && !a.first.isNegative() && !c.first.isNegative())
      return Interval{APInt(192, 0), a.second};
    if (mlir::isa<BAndOp, BOrOp, BXorOp>(op)) {
      bool nonneg = !a.first.isNegative() && !c.first.isNegative();
      if (nonneg && mlir::isa<BAndOp>(op))
        return Interval{APInt(192, 0), a.second.slt(c.second) ? a.second
                                                               : c.second};
      // Both operands fit k signed bits, so the result does too; with no
      // sign bit set on either side, it is not negative.
      unsigned k = std::max({a.first.getSignificantBits(),
                             a.second.getSignificantBits(),
                             c.first.getSignificantBits(),
                             c.second.getSignificantBits()});
      APInt hi = APInt::getSignedMaxValue(k).sext(192);
      APInt lo = nonneg ? APInt(192, 0) : APInt::getSignedMinValue(k).sext(192);
      return Interval{lo, hi};
    }
    // a >> b lies between a and 0, whatever b is.
    if (mlir::isa<ShrOp>(op)) {
      APInt zero(192, 0);
      return Interval{a.first.slt(zero) ? a.first : zero,
                      a.second.sgt(zero) ? a.second : zero};
    }
    // a << b is a * 2^b, for the amounts its own goal allows.
    if (mlir::isa<ShlOp>(op)) {
      if (c.first.isNegative()) return std::nullopt;
      uint64_t lo = c.first.getZExtValue();
      uint64_t hi = std::min<uint64_t>(
          c.second.getActiveBits() > 16 ? 1u << 16 : c.second.getZExtValue(),
          shiftWidth(op) - 1);
      if (lo > hi) return std::nullopt;
      APInt ps[] = {a.first.shl(lo), a.first.shl(hi), a.second.shl(lo),
                    a.second.shl(hi)};
      APInt rlo = ps[0], rhi = ps[0];
      for (const APInt &p : ps) {
        if (p.slt(rlo)) rlo = p;
        if (p.sgt(rhi)) rhi = p;
      }
      return Interval{rlo, rhi};
    }
    return std::nullopt;
  }

  // Whether the operand ranges alone prove that `op` does not overflow.
  bool arithByIntervals(Operation *op) {
    auto res = mlir::cast<IntType>(op->getResult(0).getType());
    auto exact = exactRange(op);
    return exact && within(*exact, res);
  }

  bool indexByIntervals(Value buffer, Value index) {
    auto arr = mlir::dyn_cast<ArrayType>(buffer.getType());
    if (!arr || arr.getLength() == 0) return false;
    IntType valid = IntType::get(ctx_, APInt(kBoundWidth, 0),
                                 APInt(kBoundWidth, arr.getLength() - 1));
    if (auto t = index.getDefiningOp<ToIndexOp>())
      return within(valueRange(t.getInput()), valid);
    if (auto c = index.getDefiningOp<mlir::arith::ConstantIndexOp>())
      return c.value() >= 0 &&
             static_cast<uint64_t>(c.value()) < arr.getLength();
    return false;
  }

  // --- the walk ----------------------------------------------------------

  Value term(Value v) { return env_.lookup(v); }

  // Encodes the ops of `block` in order. Returns false once the target
  // goal has been reached. `yields` receives an scf.yield's operands.
  bool walkBlock(mlir::Block &block, llvm::SmallVectorImpl<Value> *yields) {
    for (Operation &op : block) {
      if (auto y = mlir::dyn_cast<mlir::scf::YieldOp>(op)) {
        if (yields)
          for (Value v : y.getOperands()) yields->push_back(term(v));
        continue;
      }
      // A while loop's condition, then the values it passes on.
      if (auto c = mlir::dyn_cast<mlir::scf::ConditionOp>(op)) {
        if (yields) {
          yields->push_back(term(c.getCondition()));
          for (Value v : c.getArgs()) yields->push_back(term(v));
        }
        continue;
      }
      if (!step(&op)) return false;
      if (done_) return false;
    }
    return true;
  }

  bool step(Operation *op) {
    using P = mlir::smt::BVCmpPredicate;
    bool spec = spec_.contains(op);

    if (mlir::isa<mlir::func::ReturnOp>(op)) return true;

    if (auto r = mlir::dyn_cast<contract::RequiresOp>(op)) {
      assume(term(r.getPredicate()));
      return true;
    }
    if (auto a = mlir::dyn_cast<contract::AssumeOp>(op)) {
      // An `assume` is trusted (ADR 0023). Its assertion is tracked like
      // an axiom's, `assume file:line:col`, so that the unsat core says
      // which goals rest on it; `#k` keeps two encodings of it apart.
      Operation *as = assume(term(a.getPredicate()));
      std::string label = "assume " + formatLoc(op->getLoc());
      sentAssumes_.push_back(label);
      label += "#" + std::to_string(sentAssumes_.size());
      as->setAttr("pia.axiom", b_.getStringAttr(label));
      return true;
    }
    if (auto e = mlir::dyn_cast<contract::EnsuresOp>(op)) {
      // A lemma of a model check says which axiom it proves (ADR 0036).
      auto claim = fn_->getAttrOfType<mlir::StringAttr>("pia.obligation");
      goal(ObligationKind::ensures, op,
           claim ? claim.getValue().str() : "the postcondition holds",
           term(e.getPredicate()), false);
      return true;
    }
    if (auto a = mlir::dyn_cast<contract::AssertOp>(op)) {
      goal(ObligationKind::assert_, op, "the assertion holds",
           term(a.getPredicate()), false);
      return true;
    }
    if (auto o = mlir::dyn_cast<contract::ObligationOp>(op)) {
      goal(o.getKind(), op, "the obligation holds", term(o.getGoal()), false);
      return true;
    }
    // A measure is checked by the loop or the recursive call it belongs to.
    if (mlir::isa<contract::DecreasesOp>(op)) return true;
    // Inside an iteration, the invariant is assumed. The loop proves it on
    // entry and after each iteration.
    if (auto inv = mlir::dyn_cast<contract::InvariantOp>(op)) {
      if (Value p = term(inv.getPredicate())) assume(p);
      return true;
    }

    if (auto ifOp = mlir::dyn_cast<mlir::scf::IfOp>(op)) return stepIf(ifOp);
    if (auto forOp = mlir::dyn_cast<mlir::scf::ForOp>(op)) return stepFor(forOp);
    if (auto w = mlir::dyn_cast<mlir::scf::WhileOp>(op)) return stepWhile(w);
    if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
      return stepCall(call);

    if (auto store = mlir::dyn_cast<StoreOp>(op)) {
      Value idx = term(store.getIndex());
      Value len = lengths_.lookup(store.getBuffer());
      Value root = rootBuffer(store.getBuffer());
      if (chosen_.contains(root)) {
        refuseChosenWrite(op);
        return true;
      }
      Value arr = arrays_.lookup(root);
      Value at = elementIndex(store.getBuffer(), idx, views_);
      if (!idx || !len || !arr || !at) return true;
      boundsGoal(op, "the index is within bounds",
           andOf(cmp(P::sge, idx, bv(0)), cmp(P::slt, idx, len)),
           indexByIntervals(store.getBuffer(), store.getIndex()),
           {{"index", idx}, {"length", len}});
      Value v = term(store.getValue());
      if (v)
        arrays_[root] = create<mlir::smt::ArrayStoreOp>(arr.getType(), arr,
                                                        at, v);
      return true;
    }

    // Goals raised by value-producing code ops, checked on their operands.
    if (!spec && !insideQuantifier(op)) {
      if (auto m = arithMode(op)) {
        Value a = term(op->getOperand(0)), c = term(op->getOperand(1));
        if (a && c) {
          if (mlir::isa<DivOp, RemOp>(op)) {
            Interval d = valueRange(op->getOperand(1));
            APInt zero(192, 0);
            bool nonzero = zero.slt(d.first) || d.second.slt(zero);
            goal(ObligationKind::nonzero, op, "the divisor is not zero",
                 notOf(eq(c, bv(0))), nonzero);
          }
          if (mlir::isa<ShlOp, ShrOp>(op)) {
            Interval d = valueRange(op->getOperand(1));
            APInt w(192, shiftWidth(op));
            bool inWidth = !d.first.isNegative() && d.second.slt(w);
            goal(ObligationKind::shift, op, shiftClaim(op),
                 andOf(cmp(P::sge, c, bv(0)),
                       cmp(P::slt, c, bv(static_cast<int64_t>(shiftWidth(op))))),
                 inWidth, {{"amount", c}});
          }
          if (*m == OverflowMode::proof && !mlir::isa<RemOp>(op)) {
            Value exact = exactArith(op, a, c);
            auto rt = mlir::cast<IntType>(op->getResult(0).getType());
            goal(ObligationKind::nooverflow, op,
                 opSpelling(op) + " does not overflow " + sema::typeName(rt),
                 inRange(exact, rt), arithByIntervals(op),
                 {{"result", exact}});
          }
        }
      }
      if (auto d = mlir::dyn_cast<ExactDivOp>(op)) {
        if (Value c = term(d.getRhs())) {
          auto k = d.getRhs().getDefiningOp<ExactConstantOp>();
          bool constant = k && k.getValue() != "0";
          goal(ObligationKind::nonzero, op, "the divisor is not zero",
               notOf(eq(c, exactConst("0", true))), constant);
        }
      }
      if (auto cv = mlir::dyn_cast<ConvertOp>(op)) {
        if (cv.getOverflow() == OverflowMode::proof && !cv.isWidening())
          if (Value x = term(cv.getInput()))
            goal(ObligationKind::nooverflow, op,
                 "the value fits in " + sema::typeName(cv.getType()),
                 inRange(x, cv.getType()), false, {{"value", x}});
      }
      if (auto ti = mlir::dyn_cast<ToIndexOp>(op)) {
        if (ti.getInput().getType().isSigned())
          if (Value x = term(ti.getInput()))
            goal(ObligationKind::nooverflow, op, "the index is not negative",
                 cmp(P::sge, x, bv(0)), false, {{"index", x}});
      }
      if (auto fi = mlir::dyn_cast<FromIndexOp>(op)) {
        if (!fi.getType().contains(APInt::getMaxValue(64).zext(kBoundWidth)))
          if (Value x = term(fi.getInput()))
            goal(ObligationKind::nooverflow, op,
                 "the index fits in " + sema::typeName(fi.getType()),
                 inRange(x, fi.getType()), false, {{"index", x}});
      }
      if (auto ld = mlir::dyn_cast<LoadOp>(op)) {
        Value idx = term(ld.getIndex());
        Value len = lengths_.lookup(ld.getBuffer());
        if (idx && len)
          boundsGoal(op, "the index is within bounds",
               andOf(cmp(P::sge, idx, bv(0)), cmp(P::slt, idx, len)),
               indexByIntervals(ld.getBuffer(), ld.getIndex()),
               {{"index", idx}, {"length", len}});
      }
      if (auto sl = mlir::dyn_cast<SliceOp>(op)) {
        Value lo = term(sl.getLo()), hi = term(sl.getHi());
        Value len = lengths_.lookup(sl.getBuffer());
        if (lo && hi && len)
          boundsGoal(op, "the slice is within bounds",
               andOf(andOf(cmp(P::sge, lo, bv(0)), cmp(P::sle, lo, hi)),
                     cmp(P::sle, hi, len)),
               false, {{"start", lo}, {"end", hi}, {"length", len}});
      }
      if (mlir::isa<AbortOp>(op))
        goal(ObligationKind::assert_, op, "'abort' is never reached",
             boolConst(false), false);
    }

    if (auto old = mlir::dyn_cast<contract::OldOp>(op)) {
      Demand d;
      d.arrays = entryArrays_;
      d.lengths = lengths_;
      d.envForBlockArgs = true;
      if (Value v = demand(old.getValue(), d)) env_[old.getResult()] = v;
      return true;
    }
    if (mlir::isa<contract::ForallOp, contract::ExistsOp>(op)) {
      Demand d;
      d.arrays = arrays_;
      d.lengths = lengths_;
      // `old` inside reads the memory on entry, as it does outside.
      d.oldArrays = entryArrays_;
      d.envOutside = op;
      if (Value v = quantifier(op, d))
        env_[op->getResult(0)] = v;
      else if (auto h = havoc(op->getResult(0).getType()))
        env_[op->getResult(0)] = *h;
      return true;
    }

    // Everything else: compute the results from the operands.
    llvm::SmallVector<Value> operands;
    for (Value v : op->getOperands()) operands.push_back(term(v));
    llvm::SmallVector<Value> results;
    if (semantics(op, operands, arrays_, lengths_, views_, results)) {
      for (auto [r, t] : llvm::zip(op->getResults(), results)) env_[r] = t;
      if (auto ld = mlir::dyn_cast<LoadOp>(op))
        if (auto it = mlir::dyn_cast<IntType>(ld.getType()))
          assertTerm(inRange(results[0], it));
    } else {
      for (Value r : op->getResults())
        if (auto v = havoc(r.getType())) env_[r] = *v;
    }
    return true;
  }

  Value exactArith(Operation *op, Value a, Value c) {
    if (mlir::isa<AddOp>(op)) return bvBin("add", a, c);
    if (mlir::isa<SubOp>(op)) return bvBin("sub", a, c);
    if (mlir::isa<MulOp>(op)) return bvBin("mul", a, c);
    if (mlir::isa<DivOp>(op)) return bvBin("sdiv", a, c);
    if (mlir::isa<BAndOp>(op)) return bvBin("and", a, c);
    if (mlir::isa<BOrOp>(op)) return bvBin("or", a, c);
    if (mlir::isa<BXorOp>(op)) return bvBin("xor", a, c);
    if (mlir::isa<ShlOp>(op)) return bvBin("shl", a, c);
    if (mlir::isa<ShrOp>(op)) return bvBin("ashr", a, c);
    return bvBin("srem", a, c);
  }

  // Bit-blasting a division is slow: Z3 cannot show `a mod b < b` for
  // 68-bit values within its timeout. So for non-negative operands the
  // bounds of the quotient and remainder are stated as facts beside it.
  // Inside a quantifier the operands may be bound variables, which a
  // top-level fact cannot mention, so none is stated there.
  void divisionLemma(Operation *op, Value a, Value c, Value r) {
    using P = mlir::smt::BVCmpPredicate;
    if (quantifierDepth_ > 0 || !mlir::isa<DivOp, RemOp>(op)) return;
    for (Value operand : op->getOperands()) {
      auto t = mlir::dyn_cast<IntType>(operand.getType());
      if (!t || t.getLo().isNegative()) return;
    }
    Value bounds = andOf(cmp(P::sge, r, bv(0)), cmp(P::sle, r, a));
    if (mlir::isa<RemOp>(op)) bounds = andOf(bounds, cmp(P::slt, r, c));
    assertTerm(implies(notOf(eq(c, bv(0))), bounds));
  }

  // `x` reduced into `t` by the overflow mode.
  Value applyMode(Value x, IntType t, OverflowMode mode) {
    using P = mlir::smt::BVCmpPredicate;
    switch (mode) {
      case OverflowMode::proof:
      case OverflowMode::trap:
        return x;
      case OverflowMode::saturate: {
        Value lo = bv(t.getLo()), hi = bv(t.getHi());
        return ite(cmp(P::slt, x, lo), lo, ite(cmp(P::sgt, x, hi), hi, x));
      }
      case OverflowMode::wrap: {
        APInt size = bound(t.getHi(), 192) - bound(t.getLo(), 192) + 1;
        Value lo = bv(t.getLo());
        return bvBin("add", lo, bvBin("smod", bvBin("sub", x, lo), bv(size)));
      }
    }
    return x;
  }

  // Where element `i` of `buffer` lives in its root buffer: `i` itself, or
  // the slice's offset plus `i`. Null when a slice's offset is unknown.
  Value elementIndex(Value buffer, Value i, llvm::DenseMap<Value, Value> &views) {
    if (!i) return Value();
    if (!buffer.getDefiningOp<SliceOp>()) return i;
    Value off = views.lookup(buffer);
    if (!off) off = views_.lookup(buffer);
    if (!off) return Value();
    return bvBin("add", off, i);
  }

  // `forall i. 0 <= i < len ==> f(i)`.
  Value forallIndex(llvm::function_ref<Value(Value)> body) {
    auto build = [&](OpBuilder &ob, Location, mlir::ValueRange vars) -> Value {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
      return body(vars[0]);
    };
    return create<mlir::smt::ForallOp>(mlir::TypeRange{bvType()}, build)
        .getResult();
  }

  // A write through a buffer that an `if` or `match` chose: the verifier
  // does not know which buffer it reaches, so it is a goal that fails.
  void refuseChosenWrite(Operation *op) {
    goal(ObligationKind::assert_, op,
         "the write reaches a known buffer (writing through a slice chosen "
         "by an 'if' or 'match' is not supported yet; write before choosing)",
         boolConst(false), false);
  }

  // A fresh array that holds a slice's elements, read from `root` at
  // `off`: what a callee sees as its parameter.
  Value viewArray(Value root, Value off, Value len) {
    using P = mlir::smt::BVCmpPredicate;
    Value v = declare(root.getType(), "", false);
    Type elem = mlir::cast<mlir::smt::ArrayType>(root.getType()).getRangeType();
    assertTerm(forallIndex([&](Value i) {
      Value inside = andOf(cmp(P::sge, i, bv(0)), cmp(P::slt, i, len));
      Value same = eq(create<mlir::smt::ArraySelectOp>(elem, v, i),
                      create<mlir::smt::ArraySelectOp>(
                          elem, root, bvBin("add", off, i)));
      return implies(inside, same);
    }));
    return v;
  }

  // The root after a call wrote the slice [off, off + len) of it: fresh,
  // and equal to `root` everywhere else.
  Value writtenThrough(Value root, Value off, Value len) {
    using P = mlir::smt::BVCmpPredicate;
    Value r = declare(root.getType(), "", false);
    Type elem = mlir::cast<mlir::smt::ArrayType>(root.getType()).getRangeType();
    Value end = bvBin("add", off, len);
    assertTerm(forallIndex([&](Value j) {
      Value outside = orOf(cmp(P::slt, j, off), cmp(P::sge, j, end));
      Value same = eq(create<mlir::smt::ArraySelectOp>(elem, r, j),
                      create<mlir::smt::ArraySelectOp>(elem, root, j));
      return implies(outside, same);
    }));
    return r;
  }

  // The value semantics shared by the forward walk and demand encoding.
  // Returns false for ops it does not model.
  bool semantics(Operation *op, llvm::ArrayRef<Value> in,
                 llvm::DenseMap<Value, Value> &arrays,
                 llvm::DenseMap<Value, Value> &lengths,
                 llvm::DenseMap<Value, Value> &views,
                 llvm::SmallVectorImpl<Value> &out) {
    using P = mlir::smt::BVCmpPredicate;
    // Buffers are tracked in `arrays` and `lengths`, not as operand terms.
    for (auto [v, operand] : llvm::zip(in, op->getOperands()))
      if (!v && !mlir::isa<ArrayType, SliceType>(operand.getType()))
        return false;
    if (auto c = mlir::dyn_cast<ConstantOp>(op)) {
      out.push_back(bv(c.getValue()));
      return true;
    }
    if (auto m = arithMode(op)) {
      Value exact = exactArith(op, in[0], in[1]);
      divisionLemma(op, in[0], in[1], exact);
      // Specification arithmetic is exact whatever the function's overflow
      // mode: in an @overflow(wrap) function, `ensures result = a * b`
      // means the mathematical product, so a wrapped result fails it.
      if (spec_.contains(op) || insideQuantifier(op)) {
        out.push_back(exact);
        return true;
      }
      out.push_back(applyMode(exact,
                              mlir::cast<IntType>(op->getResult(0).getType()),
                              *m));
      return true;
    }
    if (auto c = mlir::dyn_cast<CmpOp>(op)) {
      Value r;
      switch (c.getPredicate()) {
        case CmpPredicate::eq: r = eq(in[0], in[1]); break;
        case CmpPredicate::ne: r = notOf(eq(in[0], in[1])); break;
        case CmpPredicate::lt: r = cmp(P::slt, in[0], in[1]); break;
        case CmpPredicate::le: r = cmp(P::sle, in[0], in[1]); break;
        case CmpPredicate::gt: r = cmp(P::sgt, in[0], in[1]); break;
        case CmpPredicate::ge: r = cmp(P::sge, in[0], in[1]); break;
      }
      out.push_back(r);
      return true;
    }
    if (auto c = mlir::dyn_cast<ConvertOp>(op)) {
      out.push_back(applyMode(in[0], c.getType(), c.getOverflow()));
      return true;
    }
    if (auto c = mlir::dyn_cast<ExactConstantOp>(op)) {
      out.push_back(exactConst(c.getValue(), mlir::isa<RealType>(c.getType())));
      return true;
    }
    if (mlir::isa<ExactAddOp, ExactSubOp, ExactMulOp, ExactDivOp>(op)) {
      out.push_back(exactArith(op, in[0], in[1],
                               mlir::isa<RealType>(op->getResult(0).getType())));
      return true;
    }
    if (auto c = mlir::dyn_cast<ExactCmpOp>(op)) {
      out.push_back(exactCmp(c.getPredicate(), in[0], in[1],
                             mlir::isa<RealType>(c.getLhs().getType())));
      return true;
    }
    if (auto c = mlir::dyn_cast<ExactConvertOp>(op)) {
      Value x = in[0];
      if (mlir::isa<IntType>(c.getInput().getType())) x = bvToInt(x);
      if (mlir::isa<RealType>(c.getType())) x = toReal(x);
      out.push_back(x);
      return true;
    }
    if (mlir::isa<ToIndexOp, FromIndexOp>(op)) {
      out.push_back(in[0]);
      return true;
    }
    if (auto l = mlir::dyn_cast<LenOp>(op)) {
      Value len = lengths.lookup(l.getBuffer());
      if (!len) return false;
      out.push_back(len);
      return true;
    }
    if (auto ld = mlir::dyn_cast<LoadOp>(op)) {
      Value arr = arrays.lookup(rootBuffer(ld.getBuffer()));
      Value at = elementIndex(ld.getBuffer(), in[1], views);
      Type sort = sortOf(ld.getType());
      if (!arr || !at || !sort) return false;
      out.push_back(create<mlir::smt::ArraySelectOp>(sort, arr, at));
      return true;
    }
    // An empty slice: no element can be read or written.
    if (auto e = mlir::dyn_cast<EmptyOp>(op)) {
      Type sort = sortOf(e.getType());
      if (!sort) return false;
      arrays[e.getResult()] = declare(sort, "", false);
      lengths[e.getResult()] = bv(0);
      out.push_back(bv(0));  // a placeholder: buffers are not terms
      return true;
    }
    // `unsafe view addr n`: foreign memory, trusted to be there and to
    // overlap no other buffer; its contents are unknown.
    if (auto v = mlir::dyn_cast<ViewOp>(op)) {
      Type sort = sortOf(v.getType());
      if (!sort || !in[1]) return false;
      arrays[v.getResult()] = declare(sort, "", false);
      lengths[v.getResult()] = in[1];
      out.push_back(bv(0));  // a placeholder: buffers are not terms
      return true;
    }
    // A `with_arena`'s memory: a new array, every element zero.
    if (auto r = mlir::dyn_cast<RegionOp>(op)) {
      auto sort = mlir::dyn_cast_or_null<mlir::smt::ArrayType>(
          sortOf(r.getType()));
      if (!sort) return false;
      arrays[r.getResult()] =
          create<mlir::smt::ArrayBroadcastOp>(sort, bv(0));
      lengths[r.getResult()] =
          bv(static_cast<int64_t>(r.getType().getLength()));
      out.push_back(bv(0));  // a placeholder: buffers are not terms
      return true;
    }
    // Constant data: an array of its values, all known.
    if (auto k = mlir::dyn_cast<ConstArrayOp>(op)) {
      auto sort = mlir::dyn_cast_or_null<mlir::smt::ArrayType>(
          sortOf(k.getType()));
      if (!sort) return false;
      Value arr = create<mlir::smt::ArrayBroadcastOp>(sort, bv(0));
      for (auto [i, v] : llvm::enumerate(k.getValues()))
        arr = create<mlir::smt::ArrayStoreOp>(
            sort, arr, bv(static_cast<int64_t>(i)),
            bv(mlir::cast<mlir::IntegerAttr>(v).getValue()));
      arrays[k.getResult()] = arr;
      lengths[k.getResult()] =
          bv(static_cast<int64_t>(k.getType().getLength()));
      out.push_back(bv(0));  // a placeholder: buffers are not terms
      return true;
    }
    // A slice is its buffer's storage from an offset: its length and that
    // offset are tracked, and its elements are read and written in the
    // root buffer. The result term is a placeholder; buffers are not terms.
    if (auto sl = mlir::dyn_cast<SliceOp>(op)) {
      Value lo = in[1], hi = in[2];
      if (!lo || !hi) return false;
      Value base = elementIndex(sl.getBuffer(), lo, views);
      if (!base) return false;
      views[sl.getResult()] = base;
      lengths[sl.getResult()] = bvBin("sub", hi, lo);
      out.push_back(lo);
      return true;
    }
    if (auto c = mlir::dyn_cast<mlir::arith::ConstantOp>(op)) {
      if (auto b = mlir::dyn_cast<mlir::BoolAttr>(c.getValue())) {
        out.push_back(boolConst(b.getValue()));
        return true;
      }
      if (auto i = mlir::dyn_cast<mlir::IntegerAttr>(c.getValue())) {
        if (i.getType().isInteger(1)) {
          out.push_back(boolConst(i.getValue().getBoolValue()));
          return true;
        }
        if (mlir::isa<mlir::IndexType>(i.getType())) {
          out.push_back(bv(i.getValue()));
          return true;
        }
      }
      return false;
    }
    if (op->getNumResults() == 1 && op->getResult(0).getType().isInteger(1)) {
      if (mlir::isa<mlir::arith::AndIOp>(op)) {
        out.push_back(andOf(in[0], in[1]));
        return true;
      }
      if (mlir::isa<mlir::arith::OrIOp>(op)) {
        out.push_back(orOf(in[0], in[1]));
        return true;
      }
      if (mlir::isa<mlir::arith::XOrIOp>(op)) {
        out.push_back(notOf(eq(in[0], in[1])));
        return true;
      }
      if (auto c = mlir::dyn_cast<mlir::arith::CmpIOp>(op)) {
        if (!c.getLhs().getType().isInteger(1)) return false;
        if (c.getPredicate() == mlir::arith::CmpIPredicate::eq) {
          out.push_back(eq(in[0], in[1]));
          return true;
        }
        if (c.getPredicate() == mlir::arith::CmpIPredicate::ne) {
          out.push_back(notOf(eq(in[0], in[1])));
          return true;
        }
      }
    }
    return false;
  }

  bool stepIf(mlir::scf::IfOp ifOp) {
    Value c = term(ifOp.getCondition());
    if (!c) {
      for (Value r : ifOp.getResults())
        if (auto v = havoc(r.getType())) env_[r] = *v;
      return true;
    }
    auto before = arrays_;
    llvm::SmallVector<Value> thenYields, elseYields;
    // A buffer result: each branch's elements and length.
    llvm::SmallVector<std::pair<Value, Value>> thenBufs, elseBufs;
    auto buffers = [&](mlir::Region &r,
                       llvm::SmallVectorImpl<std::pair<Value, Value>> &out) {
      if (r.empty()) return;
      auto y = mlir::cast<mlir::scf::YieldOp>(r.front().getTerminator());
      for (Value v : y.getOperands())
        out.push_back(mlir::isa<ArrayType, SliceType>(v.getType())
                          ? std::pair{calleeArray(v), lengths_.lookup(v)}
                          : std::pair{Value(), Value()});
    };
    pc_.push_back(c);
    bool ok = walkBlock(ifOp.getThenRegion().front(), &thenYields);
    pc_.pop_back();
    if (!ok) return false;
    buffers(ifOp.getThenRegion(), thenBufs);
    auto thenArrays = arrays_;
    arrays_ = before;
    if (!ifOp.getElseRegion().empty()) {
      pc_.push_back(notOf(c));
      ok = walkBlock(ifOp.getElseRegion().front(), &elseYields);
      pc_.pop_back();
      if (!ok) return false;
      buffers(ifOp.getElseRegion(), elseBufs);
    }
    for (auto &[buffer, array] : arrays_) {
      Value t = thenArrays.lookup(buffer);
      if (t && t != array) array = ite(c, t, array);
    }
    for (unsigned i = 0; i < ifOp.getNumResults(); ++i) {
      Value r = ifOp.getResult(i);
      if (mlir::isa<ArrayType, SliceType>(r.getType())) {
        // Either branch's buffer: its own root, whose elements are those of
        // the branch taken. A write through it would not reach the buffer
        // it views, so writes are refused (`chosen_`).
        auto [ta, tl] = i < thenBufs.size() ? thenBufs[i] : std::pair<Value, Value>{};
        auto [ea, el] = i < elseBufs.size() ? elseBufs[i] : std::pair<Value, Value>{};
        Type sort = sortOf(r.getType());
        if (ta && tl && ea && el) {
          arrays_[r] = ite(c, ta, ea);
          lengths_[r] = ite(c, tl, el);
        } else if (sort) {
          arrays_[r] = declare(sort, "", false);
          Value len = declare(bvType(), "", false);
          assertTerm(inRange(len, indexRange()));
          lengths_[r] = len;
        }
        chosen_.insert(r);
        env_[r] = bv(0);  // a placeholder: buffers are not terms
        continue;
      }
      Value t = i < thenYields.size() ? thenYields[i] : Value();
      Value e = i < elseYields.size() ? elseYields[i] : Value();
      if (t && e)
        env_[ifOp.getResult(i)] = ite(c, t, e);
      else if (auto v = havoc(ifOp.getResult(i).getType()))
        env_[ifOp.getResult(i)] = *v;
    }
    return true;
  }

  // Encodes a value from its definition, under substitutions. Used for a
  // callee's contract at a call, for `old`, and for quantifier bodies.
  struct Demand {
    llvm::DenseMap<Value, Value> values;
    llvm::DenseMap<Value, Value> arrays;
    llvm::DenseMap<Value, Value> lengths;
    llvm::DenseMap<Value, Value> views;  // a slice's offset in its root
    std::optional<llvm::DenseMap<Value, Value>> oldArrays;
    llvm::DenseMap<Value, Value> memo;
    bool envForBlockArgs = false;
    Operation *envOutside = nullptr;  // values defined outside it use env_
  };

  // --- loops -------------------------------------------------------------
  //
  // A loop is cut at its invariants (docs/verifier.md, "Loops"). The
  // invariant is proved on entry. One arbitrary iteration is then walked
  // from any state where the invariant holds, so the goals inside are
  // proved for every iteration, and the invariant is proved again at its
  // end. After the loop, what it computes and writes is unknown except for
  // the invariant, and for a while loop the negated condition.

  template <typename OpTy>
  static llvm::SmallVector<OpTy> loopOps(mlir::Block &block) {
    llvm::SmallVector<OpTy> out;
    for (OpTy op : block.getOps<OpTy>()) out.push_back(op);
    return out;
  }

  static std::optional<contract::DecreasesOp> measureOf(mlir::func::FuncOp f) {
    for (auto m : f.getBody().front().getOps<contract::DecreasesOp>()) return m;
    return std::nullopt;
  }

  // A measure that is not negative now and smaller next time.
  Value decreasesTerm(Value now, Value next) {
    using P = mlir::smt::BVCmpPredicate;
    if (!now || !next) return declare(boolType(), "", false);
    return andOf(cmp(P::sge, now, bv(0)), cmp(P::slt, next, now));
  }

  // Whether a call may write the buffer it passes as operand `i`.
  bool callWrites(mlir::func::CallOp call, unsigned i) {
    if (!mlir::isa<ArrayType, SliceType>(call.getOperand(i).getType()))
      return false;
    auto callee = module_.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    if (!callee || callee.isExternal()) return true;
    // An `unsafe` call may have written any buffer it was given (#55).
    if (call->hasAttr("pia.unsafe")) return true;
    auto mods = callee.getArgAttrOfType<mlir::StringAttr>(
        i, PiaDialect::getModifiersAttrName());
    return mods && (sema::hasModifier(mods.getValue(), "out") ||
                    sema::hasModifier(mods.getValue(), "inout"));
  }

  // The tracked buffers that the ops inside `loop` store to or pass to a
  // call that may write them.
  llvm::SmallVector<Value> writtenBuffers(Operation *loop) {
    llvm::SetVector<Value> out;
    loop->walk([&](Operation *op) {
      if (auto st = mlir::dyn_cast<StoreOp>(op))
        out.insert(rootBuffer(st.getBuffer()));
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        for (unsigned i = 0; i < call.getNumOperands(); ++i)
          if (callWrites(call, i)) out.insert(rootBuffer(call.getOperand(i)));
    });
    llvm::SmallVector<Value> tracked;
    for (Value b : out)
      if (arrays_.count(b)) tracked.push_back(b);
    return tracked;
  }

  void havocBuffers(llvm::ArrayRef<Value> buffers) {
    for (Value b : buffers)
      arrays_[b] = declare(arrays_[b].getType(), "", false);
  }

  // A predicate that cannot be encoded is an unknown bool, so a goal on it
  // fails and assuming it assumes nothing.
  Value demandPredicate(Value p, Demand &d) {
    if (Value t = demand(p, d)) return t;
    return declare(boolType(), "", false);
  }

  bool stepFor(mlir::scf::ForOp forOp) {
    using P = mlir::smt::BVCmpPredicate;
    Value lb = term(forOp.getLowerBound()), ub = term(forOp.getUpperBound());
    Value st = term(forOp.getStep());
    llvm::SmallVector<Value> inits;
    for (Value v : forOp.getInitArgs()) inits.push_back(term(v));
    if (!lb || !ub || !st || llvm::is_contained(inits, Value()))
      return skipLoop(forOp);
    mlir::Block &body = *forOp.getBody();
    auto invariants = loopOps<contract::InvariantOp>(body);
    auto measures = loopOps<contract::DecreasesOp>(body);
    auto stepConst = forOp.getStep().getDefiningOp<mlir::arith::ConstantIndexOp>();
    if (!stepConst) {
      bool nonzero = false;
      if (auto t = forOp.getStep().getDefiningOp<ToIndexOp>()) {
        Interval r = valueRange(t.getInput());
        nonzero = r.first.sgt(APInt(192, 0)) || r.second.slt(APInt(192, 0));
      }
      goal(ObligationKind::nonzero, forOp, "the step is not zero",
           notOf(eq(st, bv(0))), nonzero);
      if (done_) return false;
    }
    // The values the body's arguments take at iteration `i`.
    auto at = [&](Value i, llvm::ArrayRef<Value> carried) {
      Demand d;
      d.values[forOp.getInductionVar()] = i;
      for (auto [arg, v] : llvm::zip(forOp.getRegionIterArgs(), carried))
        if (v) d.values[arg] = v;
      d.arrays = arrays_;
      d.lengths = lengths_;
      // `old` inside reads the memory on entry, as it does outside.
      d.oldArrays = entryArrays_;
      d.envOutside = forOp;
      return d;
    };

    for (auto inv : invariants) {
      Demand d = at(lb, inits);
      goal(ObligationKind::invariant, inv, "the loop invariant holds on entry",
           demandPredicate(inv.getPredicate(), d), false);
      if (done_) return false;
    }

    // One arbitrary iteration. Its assumptions hold under a fresh guard, so
    // they say nothing about the code after the loop.
    auto beforeArrays = arrays_;
    auto written = writtenBuffers(forOp);
    Value i = declare(bvType(), "", false);
    Value iteration = andOf(declare(boolType(), "", false),
                            andOf(cmp(P::sle, lb, i), cmp(P::slt, i, ub)));
    if (!stepConst || stepConst.value() != 1)
      iteration = andOf(iteration,
                        eq(bvBin("srem", bvBin("sub", i, lb), st), bv(0)));
    pc_.push_back(iteration);
    env_[forOp.getInductionVar()] = i;
    for (Value arg : forOp.getRegionIterArgs())
      if (auto v = havoc(arg.getType())) env_[arg] = *v;
    havocBuffers(written);
    llvm::SmallVector<Value> yields;
    bool ok = walkBlock(body, &yields);
    if (ok) {
      Value next = bvBin("add", i, st);
      for (auto inv : invariants) {
        Demand d = at(next, yields);
        goal(ObligationKind::invariant, inv,
             "the loop invariant holds after each iteration",
             demandPredicate(inv.getPredicate(), d), false);
        if (done_) break;
      }
      for (auto m : measures) {
        if (done_) break;
        Demand d = at(next, yields);
        goal(ObligationKind::decreases, m, "the measure decreases",
             decreasesTerm(term(m.getMeasure()), demand(m.getMeasure(), d)),
             false);
      }
    }
    pc_.pop_back();
    if (!ok || done_) return false;

    // After the loop: `i` has passed `ub` by less than one step, or the
    // loop never ran.
    arrays_ = beforeArrays;
    havocBuffers(written);
    llvm::SmallVector<Value> results;
    for (Value r : forOp.getResults()) {
      auto v = havoc(r.getType());
      if (v) env_[r] = *v;
      results.push_back(v ? *v : Value());
    }
    Value exit = declare(bvType(), "", false);
    Value ran = cmp(P::slt, lb, ub);
    assume(implies(notOf(ran), eq(exit, lb)));
    assume(implies(ran, andOf(andOf(cmp(P::sge, exit, ub),
                                    cmp(P::slt, bvBin("sub", exit, ub), st)),
                              eq(bvBin("srem", bvBin("sub", exit, lb), st),
                                 bv(0)))));
    for (auto inv : invariants) {
      Demand d = at(exit, results);
      if (Value p = demand(inv.getPredicate(), d)) assume(p);
    }
    return true;
  }

  bool stepWhile(mlir::scf::WhileOp w) {
    llvm::SmallVector<Value> inits;
    for (Value v : w.getInits()) inits.push_back(term(v));
    if (llvm::is_contained(inits, Value())) return skipLoop(w);
    mlir::Block &before = w.getBefore().front();
    mlir::Block &after = w.getAfter().front();
    auto cond = mlir::cast<mlir::scf::ConditionOp>(before.getTerminator());
    auto invariants = loopOps<contract::InvariantOp>(before);
    auto measures = loopOps<contract::DecreasesOp>(before);
    // The values of the condition region's arguments.
    auto at = [&](llvm::ArrayRef<Value> args) {
      Demand d;
      for (auto [arg, v] : llvm::zip(before.getArguments(), args))
        if (v) d.values[arg] = v;
      d.arrays = arrays_;
      d.lengths = lengths_;
      // `old` inside reads the memory on entry, as it does outside.
      d.oldArrays = entryArrays_;
      d.envOutside = w;
      return d;
    };

    for (auto inv : invariants) {
      Demand d = at(inits);
      goal(ObligationKind::invariant, inv, "the loop invariant holds on entry",
           demandPredicate(inv.getPredicate(), d), false);
      if (done_) return false;
    }

    // One arbitrary iteration: the condition from any state where the
    // invariant holds, then the body when the condition is true.
    auto beforeArrays = arrays_;
    auto written = writtenBuffers(w);
    pc_.push_back(declare(boolType(), "", false));
    for (Value arg : before.getArguments())
      if (auto v = havoc(arg.getType())) env_[arg] = *v;
    havocBuffers(written);
    llvm::SmallVector<Value> passed;
    bool ok = walkBlock(before, &passed);
    if (ok) {
      Value c = passed.empty() || !passed[0] ? declare(boolType(), "", false)
                                             : passed[0];
      llvm::SmallVector<Value> nows;
      for (auto m : measures) nows.push_back(term(m.getMeasure()));
      pc_.push_back(c);
      for (auto [k, arg] : llvm::enumerate(after.getArguments())) {
        Value v = k + 1 < passed.size() ? passed[k + 1] : Value();
        if (v)
          env_[arg] = v;
        else if (auto h = havoc(arg.getType()))
          env_[arg] = *h;
      }
      llvm::SmallVector<Value> yields;
      ok = walkBlock(after, &yields);
      if (ok) {
        for (auto inv : invariants) {
          Demand d = at(yields);
          goal(ObligationKind::invariant, inv,
               "the loop invariant holds after each iteration",
               demandPredicate(inv.getPredicate(), d), false);
          if (done_) break;
        }
        for (auto [m, now] : llvm::zip(measures, nows)) {
          if (done_) break;
          Demand d = at(yields);
          goal(ObligationKind::decreases, m, "the measure decreases",
               decreasesTerm(now, demand(m.getMeasure(), d)), false);
        }
        // Without a measure, nothing shows that the loop ends.
        if (measures.empty() && !done_)
          skipped(ObligationKind::decreases, w, "the loop terminates",
                  "it has no 'decreases' measure");
      }
      pc_.pop_back();
    }
    pc_.pop_back();
    if (!ok || done_) return false;

    // After the loop: the invariant holds and the condition is false, for
    // some final state.
    arrays_ = beforeArrays;
    havocBuffers(written);
    llvm::SmallVector<Value> finals;
    for (Value arg : before.getArguments()) {
      auto v = havoc(arg.getType());
      finals.push_back(v ? *v : Value());
    }
    Demand d = at(finals);
    for (auto inv : invariants)
      if (Value p = demand(inv.getPredicate(), d)) assume(p);
    if (Value c = demand(cond.getCondition(), d)) assume(notOf(c));
    for (auto [r, v] : llvm::zip(w.getResults(), cond.getArgs())) {
      if (Value t = demand(v, d))
        env_[r] = t;
      else if (auto h = havoc(r.getType()))
        env_[r] = *h;
    }
    return true;
  }

  // The array a callee sees for a buffer argument: the root's own array, or
  // for a slice a fresh array of its elements.
  Value calleeArray(Value actual) {
    Value root = rootBuffer(actual);
    Value arr = arrays_.lookup(root);
    if (!arr || actual == root) return arr;
    Value off = views_.lookup(actual), len = lengths_.lookup(actual);
    if (!off || !len) return declare(arr.getType(), "", false);
    return viewArray(arr, off, len);
  }

  // A call is checked against the callee's contract, not its body: its
  // preconditions are goals, and its postconditions are assumed about a
  // fresh result.
  bool stepCall(mlir::func::CallOp call) {
    auto callee = module_.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    bool hasBody = callee && !callee.isExternal();
    Demand pre;
    if (hasBody) {
      mlir::Block &entry = callee.getBody().front();
      for (unsigned i = 0; i < call.getNumOperands(); ++i) {
        Value formal = entry.getArgument(i), actual = call.getOperand(i);
        if (mlir::isa<ArrayType, SliceType>(actual.getType())) {
          pre.arrays[formal] = calleeArray(actual);
          pre.lengths[formal] = lengths_.lookup(actual);
        } else {
          pre.values[formal] = term(actual);
        }
      }
      for (auto r : entry.getOps<contract::RequiresOp>()) {
        // A precondition the verifier cannot encode is an unknown bool:
        // the goal fails, and assuming it later assumes nothing.
        Value p = demand(r.getPredicate(), pre);
        if (!p) p = declare(boolType(), "", false);
        goal(ObligationKind::requires_, call,
             "the precondition of '" + call.getCallee().str() + "' holds", p,
             false);
        if (done_) return false;
      }
    }
    if (hasBody && callee == fn_ && !measureOf(fn_))
      skipped(ObligationKind::decreases, call, "the recursion terminates",
              "'" + call.getCallee().str() + "' has no 'decreases' measure");
    if (hasBody && callee == fn_)
      if (auto m = measureOf(fn_)) {
        // Recursion terminates when each recursive call makes the measure
        // smaller, and it never goes below zero.
        Value now = term(m->getMeasure());
        Value next = demand(m->getMeasure(), pre);
        goal(ObligationKind::decreases, call,
             "the measure of '" + call.getCallee().str() + "' decreases",
             decreasesTerm(now, next), false);
        if (done_) return false;
      }
    for (Value r : call.getResults()) {
      // A buffer returned by value is a fresh array, with its length.
      if (mlir::isa<ArrayType, SliceType>(r.getType())) {
        Type sort = sortOf(r.getType());
        if (!sort) continue;
        arrays_[r] = declare(sort, "", false);
        if (auto a = mlir::dyn_cast<ArrayType>(r.getType())) {
          lengths_[r] = bv(APInt(64, a.getLength()));
        } else {
          Value len = declare(bvType(), "", false);
          assertTerm(inRange(len, indexRange()));
          lengths_[r] = len;
        }
        continue;
      }
      if (auto v = havoc(r.getType())) env_[r] = *v;
    }
    // A theory's abstract function is uninterpreted.
    if (isAbstract(callee) && call.getNumResults() == 1) {
      llvm::SmallVector<Value> args;
      for (Value a : call.getOperands()) args.push_back(term(a));
      Value app = abstractCall(callee, args);
      Value r = env_.lookup(call.getResult(0));
      if (app && r) assume(eq(r, app));
    }
    // A spec function's result is its definition applied to the arguments.
    if (hasBody && isSpecFunction(callee))
      for (unsigned k = 0; k < call.getNumResults(); ++k) {
        Demand args = pre;
        Value app = specCall(callee, k, args);
        Value r = env_.lookup(call.getResult(k));
        if (app && r) assume(eq(r, app));
      }
    for (unsigned i = 0; i < call.getNumOperands(); ++i) {
      Value actual = call.getOperand(i), root = rootBuffer(actual);
      if (callWrites(call, i) && chosen_.contains(root)) refuseChosenWrite(call);
      if (!callWrites(call, i) || !arrays_.count(root)) continue;
      Value off = views_.lookup(actual), len = lengths_.lookup(actual);
      if (actual != root && off && len)
        arrays_[root] = writtenThrough(arrays_[root], off, len);
      else
        arrays_[root] = declare(arrays_[root].getType(), "", false);
    }
    if (!hasBody) return true;
    Demand post = pre;
    post.memo.clear();
    post.oldArrays = pre.arrays;
    mlir::Block &entry = callee.getBody().front();
    for (unsigned i = 0; i < call.getNumOperands(); ++i)
      if (mlir::isa<ArrayType, SliceType>(call.getOperand(i).getType()))
        post.arrays[entry.getArgument(i)] = calleeArray(call.getOperand(i));
    callee.walk([&](mlir::func::ReturnOp ret) {
      for (auto [formal, actual] : llvm::zip(ret.getOperands(), call.getResults())) {
        if (mlir::isa<ArrayType, SliceType>(formal.getType())) {
          // A buffer parameter returned as it is: the result is the
          // argument's array. Otherwise the callee's `result` is the
          // fresh array.
          auto arg = mlir::dyn_cast<mlir::BlockArgument>(formal);
          if (arg && arg.getOwner() == &entry && post.arrays.lookup(formal)) {
            arrays_[actual] = post.arrays.lookup(formal);
            if (Value len = lengths_.lookup(call.getOperand(arg.getArgNumber())))
              lengths_[actual] = len;
          } else {
            post.arrays[formal] = arrays_.lookup(actual);
            post.lengths[formal] = lengths_.lookup(actual);
            // Known, so the callee's body is not encoded for it: `result`
            // is the call's array, not what the body built. Buffers are
            // not terms, so the term is a placeholder.
            post.values[formal] = bv(0);
          }
          continue;
        }
        Value result = env_.lookup(actual);
        // A parameter returned as it is already stands for the argument,
        // which the result then equals.
        if (auto known = pre.values.find(formal); known != pre.values.end()) {
          if (result && known->second) assume(eq(result, known->second));
          continue;
        }
        post.values[formal] = result;
      }
    });
    callee.walk([&](contract::EnsuresOp e) {
      if (Value p = demand(e.getPredicate(), post)) assume(p);
    });
    return true;
  }

  // --- spec functions ----------------------------------------------------
  //
  // A spec function `f` is an uninterpreted function `F` with one argument
  // per scalar parameter and two (the array and its length) per buffer. Each
  // call `f a` is `F a`, with its definition as a fact:
  // `pre(a) ==> F a = body(a)`, where a recursive call in the body is `F`
  // again, unfolded no further. `@fuel(n)` unfolds n levels. The
  // precondition guards the definition because termination is proved only
  // where it holds (docs/verifier.md, "Spec functions and lemmas").

  mlir::func::FuncOp calleeOf(mlir::func::CallOp call) {
    return module_.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
  }

  static bool isSpecFunction(mlir::func::FuncOp f) {
    return f && !f.isExternal() && f->hasAttr(PiaDialect::getSpecAttrName());
  }
  // A theory's spec function with no body (ADR 0036).
  static bool isAbstract(mlir::func::FuncOp f) {
    return f && f->hasAttr(PiaDialect::getAbstractAttrName());
  }
  bool hasSpecDecl(mlir::func::FuncOp f) {
    return isSpecFunction(f) || isAbstract(f);
  }

  // `f a` for an abstract `f`: the uninterpreted function applied, with
  // its result type's range, and nothing else.
  Value abstractCall(mlir::func::FuncOp callee, llvm::ArrayRef<Value> args) {
    auto it = specFuns_.find(callee.getOperation());
    if (it == specFuns_.end() || callee.getNumResults() != 1) return Value();
    for (Value a : args)
      if (!a) return Value();
    noteTheoryUse(callee);
    Type rt = callee.getFunctionType().getResult(0);
    Value fun = it->second[0];
    Value app = args.empty() ? fun
                             : create<mlir::smt::ApplyFuncOp>(
                                   sortOf(rt), fun, mlir::ValueRange(args));
    if (auto it2 = mlir::dyn_cast<IntType>(rt)) define(inRange(app, it2));
    return app;
  }

  void noteTheoryUse(mlir::func::FuncOp f) {
    if (!theoryOf(f).empty()) theoryFuns_.insert(f.getSymName().str());
  }

  static unsigned fuelOf(mlir::func::FuncOp f) {
    if (auto a = f->getAttrOfType<mlir::IntegerAttr>(PiaDialect::getFuelAttrName()))
      return static_cast<unsigned>(a.getInt());
    return 1;
  }

  void declareSpecFunctions() {
    auto here = fn_->getAttrOfType<mlir::StringAttr>("pia.model");
    for (auto f : module_.getOps<mlir::func::FuncOp>()) {
      if (!hasSpecDecl(f)) continue;
      // A model is sealed: outside it, a query never sees its functions.
      if (auto m = f->getAttrOfType<mlir::StringAttr>("pia.model"))
        if (!here || here != m) continue;
      llvm::SmallVector<Type> domain;
      bool ok = true;
      for (Type t : f.getFunctionType().getInputs()) {
        Type sort = sortOf(t);
        if (!sort) ok = false;
        domain.push_back(sort);
        if (mlir::isa<ArrayType, SliceType>(t)) domain.push_back(bvType());
      }
      llvm::SmallVector<Value> funs;
      for (Type r : f.getFunctionType().getResults()) {
        Type sort = sortOf(r);
        if (!sort) ok = false;
        if (!ok) break;
        Type ft = domain.empty()
                      ? sort
                      : mlir::smt::SMTFuncType::get(ctx_, domain, sort);
        // A theory's functions keep their names, `Lip.lip`, so queries
        // that combine theories never confuse them (ADR 0036).
        if (!theoryOf(f).empty())
          funs.push_back(create<mlir::smt::DeclareFunOp>(
              ft, b_.getStringAttr(f.getSymName())));
        else
          funs.push_back(declare(ft, "", false));
      }
      if (ok && !funs.empty()) specFuns_[f.getOperation()] = std::move(funs);
    }
  }

  // A definition: asserted, or a hypothesis of the enclosing quantifier.
  void define(Value fact) {
    if (quantifierDepth_ > 0) pendingDefs_.push_back(fact);
    else assertTerm(fact);
  }

  // `f a`, result `k`, where `args` maps f's parameters to the arguments.
  Value specCall(mlir::func::FuncOp callee, unsigned k, Demand &args) {
    auto it = specFuns_.find(callee.getOperation());
    if (it == specFuns_.end()) return Value();
    noteTheoryUse(callee);
    mlir::Block &entry = callee.getBody().front();
    llvm::SmallVector<Value> flat;
    for (mlir::BlockArgument a : entry.getArguments()) {
      if (mlir::isa<ArrayType, SliceType>(a.getType())) {
        Value arr = args.arrays.lookup(a), len = args.lengths.lookup(a);
        if (!arr || !len) return Value();
        flat.append({arr, len});
      } else {
        Value v = args.values.lookup(a);
        if (!v) return Value();
        flat.push_back(v);
      }
    }
    Type rt = callee.getFunctionType().getResult(k);
    Value fun = it->second[k];
    Value app = flat.empty() ? fun
                             : create<mlir::smt::ApplyFuncOp>(sortOf(rt), fun,
                                                              mlir::ValueRange(flat));
    // The body was proved to return a value of the result type, and to
    // meet the postconditions where the precondition holds.
    if (auto it2 = mlir::dyn_cast<IntType>(rt)) define(inRange(app, it2));
    if (!llvm::is_contained(ensuresStack_, callee.getOperation())) {
      ensuresStack_.push_back(callee.getOperation());
      unsigned before = unknowns_;
      Demand post;
      post.values = args.values;
      post.arrays = args.arrays;
      post.lengths = args.lengths;
      callee.walk([&](mlir::func::ReturnOp ret) {
        if (k < ret.getNumOperands()) post.values[ret.getOperand(k)] = app;
      });
      Value pre = boolConst(true), facts = boolConst(true);
      bool ok = callee.getNumResults() == 1;
      for (auto r : entry.getOps<contract::RequiresOp>()) {
        Value p = demand(r.getPredicate(), post);
        if (!p) ok = false;
        else pre = andOf(pre, p);
      }
      callee.walk([&](contract::EnsuresOp e) {
        Value p = demand(e.getPredicate(), post);
        if (!p) ok = false;
        else facts = andOf(facts, p);
      });
      ensuresStack_.pop_back();
      if (ok && unknowns_ == before) define(implies(pre, facts));
    }
    if (static_cast<unsigned>(llvm::count(specStack_, callee.getOperation())) >=
        fuelOf(callee))
      return app;

    specStack_.push_back(callee.getOperation());
    unsigned before = unknowns_;
    Demand body;
    body.values = args.values;
    body.arrays = args.arrays;
    body.lengths = args.lengths;
    Value def;
    callee.walk([&](mlir::func::ReturnOp ret) {
      if (k < ret.getNumOperands()) def = demand(ret.getOperand(k), body);
    });
    Value pre = boolConst(true);
    for (auto r : entry.getOps<contract::RequiresOp>()) {
      Value p = demand(r.getPredicate(), body);
      if (!p) def = Value();
      else pre = andOf(pre, p);
    }
    specStack_.pop_back();
    // A definition with a value the encoding could not model would claim
    // too much inside a quantifier; leave the call uninterpreted.
    if (def && unknowns_ == before) define(implies(pre, eq(app, def)));
    return app;
  }

  // A spec call met while demanding a contract.
  Value demandSpecCall(mlir::func::CallOp call, unsigned k, Demand &d) {
    mlir::func::FuncOp callee = calleeOf(call);
    mlir::Block &entry = callee.getBody().front();
    Demand args;
    for (unsigned i = 0; i < call.getNumOperands(); ++i) {
      Value formal = entry.getArgument(i), actual = call.getOperand(i);
      if (mlir::isa<ArrayType, SliceType>(actual.getType())) {
        (void)demand(actual, d);  // a view records its offset and length
        Value root = rootBuffer(actual);
        Value arr = d.arrays.lookup(root);
        Value len = d.lengths.lookup(actual);
        if (!len) len = lengths_.lookup(actual);
        if (!arr || !len) return Value();
        if (actual != root) {
          Value off = d.views.lookup(actual);
          if (!off) off = views_.lookup(actual);
          // A view needs a fact about a fresh array, which a quantifier
          // cannot hold.
          if (!off || quantifierDepth_ > 0) return Value();
          arr = viewArray(arr, off, len);
        }
        args.arrays[formal] = arr;
        args.lengths[formal] = len;
      } else {
        Value t = demand(actual, d);
        if (!t) return Value();
        args.values[formal] = t;
      }
    }
    return specCall(callee, k, args);
  }

  // --- demand encoding ---------------------------------------------------

  Value demand(Value v, Demand &d) {
    if (Value t = d.values.lookup(v)) return t;
    if (Value t = d.memo.lookup(v)) return t;
    if (d.envOutside) {
      Operation *def = v.getDefiningOp();
      mlir::Region *r = v.getParentRegion();
      bool inside = def ? d.envOutside->isAncestor(def)
                        : d.envOutside->isProperAncestor(r->getParentOp()) ||
                              r->getParentOp() == d.envOutside;
      if (!inside) return env_.lookup(v);
    }
    Operation *op = v.getDefiningOp();
    if (!op) return d.envForBlockArgs ? env_.lookup(v) : Value();
    Value result;
    if (auto old = mlir::dyn_cast<contract::OldOp>(op)) {
      Demand inner = d;
      inner.memo.clear();
      if (d.oldArrays) inner.arrays = *d.oldArrays;
      result = demand(old.getValue(), inner);
    } else if (mlir::isa<contract::ForallOp, contract::ExistsOp>(op)) {
      result = quantifier(op, d);
    } else if (auto ifOp = mlir::dyn_cast<mlir::scf::IfOp>(op)) {
      Value c = demand(ifOp.getCondition(), d);
      auto thenY = mlir::cast<mlir::scf::YieldOp>(
          ifOp.getThenRegion().front().getTerminator());
      auto elseY = mlir::cast<mlir::scf::YieldOp>(
          ifOp.getElseRegion().front().getTerminator());
      unsigned i = mlir::cast<mlir::OpResult>(v).getResultNumber();
      Value t = demand(thenY.getOperand(i), d);
      Value e = demand(elseY.getOperand(i), d);
      if (c && t && e) result = ite(c, t, e);
    } else if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op);
               call && isAbstract(calleeOf(call))) {
      llvm::SmallVector<Value> args;
      for (Value a : call.getOperands()) args.push_back(demand(a, d));
      result = abstractCall(calleeOf(call), args);
    } else if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op);
               call && isSpecFunction(calleeOf(call))) {
      result = demandSpecCall(call, mlir::cast<mlir::OpResult>(v).getResultNumber(), d);
    } else {
      llvm::SmallVector<Value> operands;
      for (Value o : op->getOperands()) operands.push_back(demand(o, d));
      llvm::SmallVector<Value> results;
      if (semantics(op, operands, d.arrays, d.lengths, d.views, results))
        result = results[mlir::cast<mlir::OpResult>(v).getResultNumber()];
    }
    if (!result) {
      // A call or an op the verifier does not model: any value of its type.
      ++unknowns_;
      auto h = havoc(v.getType());
      if (!h) return Value();
      result = *h;
    }
    d.memo[v] = result;
    return result;
  }

  // `forall (x in lo..hi). p` and `exists`, as SMT quantifiers over the
  // bound variable's type.
  Value quantifier(Operation *op, Demand &outer) {
    bool isForall = mlir::isa<contract::ForallOp>(op);
    mlir::Block &body = op->getRegion(0).front();
    llvm::SmallVector<Type> sorts;
    for (mlir::BlockArgument a : body.getArguments()) {
      Type s = sortOf(a.getType());
      if (!s) return Value();
      sorts.push_back(s);
    }
    bool failed = false;
    auto build = [&](OpBuilder &ob, Location, mlir::ValueRange vars) -> Value {
      OpBuilder::InsertionGuard guard(b_);
      b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
      ++quantifierDepth_;
      // Values outside the quantifier come from where the outer encoding
      // takes them: env_ in the walk, or a substitution in a loop's or a
      // callee's contract.
      Demand d = outer;
      d.memo.clear();
      Value range = boolConst(true);
      for (auto [arg, var] : llvm::zip(body.getArguments(), vars)) {
        d.values[arg] = var;
        if (auto it = mlir::dyn_cast<IntType>(arg.getType()))
          range = andOf(range, inRange(var, it));
      }
      auto yield = mlir::cast<contract::YieldOp>(body.getTerminator());
      size_t mark = pendingDefs_.size();
      Value p = demand(yield.getPredicate(), d);
      if (!p) {
        failed = true;
        p = boolConst(true);
      }
      // Spec definitions instantiated at the bound variables hold for every
      // value of them, so they join the range as hypotheses.
      for (size_t k = mark; k < pendingDefs_.size(); ++k)
        range = andOf(range, pendingDefs_[k]);
      pendingDefs_.resize(mark);
      --quantifierDepth_;
      return isForall ? implies(range, p) : andOf(range, p);
    };
    Operation *q =
        isForall
            ? create<mlir::smt::ForallOp>(mlir::TypeRange(sorts), build)
                  .getOperation()
            : create<mlir::smt::ExistsOp>(mlir::TypeRange(sorts), build)
                  .getOperation();
    if (failed) {
      // The caller treats the quantifier as an unknown bool.
      q->erase();
      return Value();
    }
    return q->getResult(0);
  }

  // An axiom, `forall params. requires ==> ensures`, asserted before the
  // negated goal under its name, once per trigger, each with its pattern.
  void assertAxiom(mlir::func::FuncOp axiom, const AxiomTriggers &triggers) {
    OpBuilder::InsertionGuard guard(b_);
    b_.setInsertionPoint(goalAssert_);
    mlir::Block &entry = axiom.getBody().front();
    std::string name = axiom.getSymName().str();
    sentAxioms_.push_back(name);
    auto fact = [&](Demand &d) -> Value {
      Value pre = boolConst(true), post = boolConst(true);
      for (auto r : entry.getOps<contract::RequiresOp>()) {
        Value p = demand(r.getPredicate(), d);
        if (!p) return Value();
        pre = andOf(pre, p);
      }
      for (auto e : entry.getOps<contract::EnsuresOp>()) {
        Value p = demand(e.getPredicate(), d);
        if (!p) return Value();
        post = andOf(post, p);
      }
      return implies(pre, post);
    };
    auto named = [&](Value t, unsigned k) {
      auto a = create<mlir::smt::AssertOp>(t);
      std::string label = name;
      if (k > 0) label += "#" + std::to_string(k + 1);
      a->setAttr("pia.axiom", b_.getStringAttr(label));
    };
    if (entry.getNumArguments() == 0) {
      Demand d;
      unsigned before = unknowns_;
      if (Value t = fact(d); t && unknowns_ == before) named(t, 0);
      return;
    }
    llvm::SmallVector<Type> sorts;
    llvm::SmallVector<std::string> names;
    for (mlir::BlockArgument a : entry.getArguments()) {
      Type so = sortOf(a.getType());
      if (!so) return;
      sorts.push_back(so);
      auto n = mlir::dyn_cast<mlir::NameLoc>(a.getLoc());
      // A name a quote made fresh, `c#3`, or a primed one, `x'`, is not an
      // SMT-LIB symbol: such characters become `_`.
      std::string name = n ? n.getName().str() : "x";
      for (char &ch : name)
        if (!std::isalnum(static_cast<unsigned char>(ch)) && ch != '_') ch = '_';
      names.push_back(name);
    }
    llvm::SmallVector<llvm::StringRef> nameRefs(names.begin(), names.end());
    for (size_t k = 0; k < triggers.triggers.size(); ++k) {
      const Trigger &trigger = triggers.triggers[k];
      bool failed = false;
      unsigned before = unknowns_;
      auto body = [&](OpBuilder &ob, Location, mlir::ValueRange vars) -> Value {
        OpBuilder::InsertionGuard g(b_);
        b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
        ++quantifierDepth_;
        Demand d;
        Value range = boolConst(true);
        for (auto [arg, var] : llvm::zip(entry.getArguments(), vars)) {
          d.values[arg] = var;
          if (auto it = mlir::dyn_cast<IntType>(arg.getType()))
            range = andOf(range, inRange(var, it));
        }
        size_t mark = pendingDefs_.size();
        Value p = fact(d);
        if (!p) {
          failed = true;
          p = boolConst(true);
        }
        // Facts about the terms in the axiom, such as the range of
        // `in_w f`, hold for every value, so they join the conclusion. As
        // hypotheses they would weaken the axiom for terms whose range the
        // query never states, such as `out_w (residual a)`.
        Value facts = boolConst(true);
        for (size_t i = mark; i < pendingDefs_.size(); ++i)
          facts = andOf(facts, pendingDefs_[i]);
        pendingDefs_.resize(mark);
        --quantifierDepth_;
        return implies(range, andOf(facts, p));
      };
      llvm::SmallVector<Value> patternTerms;
      auto patterns = [&](OpBuilder &ob, Location,
                          mlir::ValueRange vars) -> mlir::ValueRange {
        OpBuilder::InsertionGuard g(b_);
        b_.setInsertionPoint(ob.getInsertionBlock(), ob.getInsertionPoint());
        ++quantifierDepth_;
        Demand d;
        for (auto [arg, var] : llvm::zip(entry.getArguments(), vars))
          d.values[arg] = var;
        size_t mark = pendingDefs_.size();
        for (Value t : trigger.terms) {
          Value v = demand(t, d);
          if (!v) failed = true;
          else patternTerms.push_back(v);
        }
        pendingDefs_.resize(mark);  // facts made while building the terms
        --quantifierDepth_;
        return mlir::ValueRange(patternTerms);
      };
      auto q = create<mlir::smt::ForallOp>(mlir::TypeRange(sorts), body,
                                           llvm::ArrayRef<llvm::StringRef>(nameRefs),
                                           patterns);
      if (failed || unknowns_ != before) {
        q->erase();
        continue;
      }
      named(q.getResult(), static_cast<unsigned>(k));
    }
  }

  mlir::ModuleOp module_;
  mlir::func::FuncOp fn_;
  unsigned width_;
  int target_;
  OpBuilder &b_;
  std::vector<Goal> &goals_;
  mlir::MLIRContext *ctx_;
  Location loc_;
  llvm::DenseSet<Operation *> spec_;
  mlir::Block *solverBlock_;  // where interpreted functions are declared
  llvm::StringMap<Value> interpreted_;

  llvm::DenseMap<Value, Value> env_;
  llvm::DenseMap<Value, Value> arrays_, lengths_, entryArrays_;
  llvm::DenseMap<Value, Value> views_;  // a slice's offset in its root buffer
  llvm::DenseSet<Value> chosen_;  // buffers an `if` chose between branches
  std::vector<Value> pc_;
  std::vector<Decl> decls_, witnesses_;
  int counter_ = 0;
  int nextName_ = 0;
  int quantifierDepth_ = 0;
  // Spec functions (ADR 0023, group 5): one uninterpreted function per
  // result, the definitions being unfolded, and definitions made inside a
  // quantifier, which it takes as hypotheses.
  llvm::DenseMap<Operation *, llvm::SmallVector<Value>> specFuns_;
  llvm::SmallVector<Operation *> specStack_, ensuresStack_;
  std::vector<Value> pendingDefs_;
  unsigned unknowns_ = 0;  // values demand() could not encode
  bool done_ = false;
  // Theories (ADR 0036): the theory functions the query applies, the
  // negated goal (axioms are asserted before it, so it stays last for
  // slicing), and the axioms sent.
  std::set<std::string> theoryFuns_;
  std::set<std::string> sorts_;  // the theory sorts the query uses
  mlir::smt::AssertOp goalAssert_;
  std::vector<std::string> sentAxioms_;
  std::vector<std::string> sentAssumes_;
};

// Values in the bit-vector encoding are signed and wide enough for every
// exact intermediate. Sums and differences of 64-bit values need 66 bits,
// so the floor is 68. A product needs the bits of its exact range, which
// the operands' types bound: `u8 * u8` fits in 17 bits, while `u64 * u64`
// needs 130. So the width is chosen per function, from the products the
// function and its callees (whose contracts it encodes) can compute, rather than once
// for the whole module (docs/verifier.md, "Encoding").
constexpr unsigned kBaseWidth = 68;
constexpr unsigned kWideWidth = 132;

// The signed bits an exact product of values of these types can need.
unsigned productBits(Type lhs, Type rhs) {
  auto a = mlir::dyn_cast<IntType>(lhs), c = mlir::dyn_cast<IntType>(rhs);
  if (!a || !c) return kWideWidth;  // index operands: up to 2^64 - 1
  constexpr unsigned w = 2 * kBoundWidth + 2;
  APInt corners[2][2] = {{a.getLo().sextOrTrunc(w), a.getHi().sextOrTrunc(w)},
                         {c.getLo().sextOrTrunc(w), c.getHi().sextOrTrunc(w)}};
  unsigned bits = 0;
  for (const APInt &x : corners[0])
    for (const APInt &y : corners[1])
      bits = std::max(bits, (x * y).getSignificantBits());
  return bits;
}

unsigned encodingWidth(mlir::ModuleOp module, mlir::func::FuncOp fn) {
  unsigned need = 0;
  llvm::SmallPtrSet<Operation *, 8> seen;
  llvm::SmallVector<mlir::func::FuncOp> work{fn};
  while (!work.empty()) {
    mlir::func::FuncOp f = work.pop_back_val();
    if (!seen.insert(f.getOperation()).second) continue;
    f.walk([&](Operation *op) {
      if (auto m = mlir::dyn_cast<MulOp>(op))
        need = std::max(need, productBits(m.getLhs().getType(),
                                          m.getRhs().getType()));
      // `a << b` is a product with 2^b, b below a's storage width.
      if (auto s = mlir::dyn_cast<ShlOp>(op)) {
        auto a = mlir::cast<IntType>(s.getLhs().getType());
        unsigned shift = a.getStorageWidth() - 1;
        if (auto b = mlir::dyn_cast<IntType>(s.getRhs().getType()))
          if (!b.getHi().isNegative() && b.getHi().ult(shift))
            shift = b.getHi().getZExtValue();
        unsigned bits = std::max(a.getLo().getSignificantBits(),
                                 a.getHi().getSignificantBits());
        need = std::max(need, bits + shift);
      }
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        if (auto callee =
                module.lookupSymbol<mlir::func::FuncOp>(call.getCallee()))
          work.push_back(callee);
    });
  }
  // Two bits of headroom, as for sums: the exact result, then one more
  // operation on it before an overflow goal reduces it.
  return need + 2 <= kBaseWidth ? kBaseWidth : kWideWidth;
}

std::string signedDecimal(const std::string &unsignedDecimal, unsigned width) {
  APInt v(width, unsignedDecimal, 10);
  return llvm::toString(v, 10, /*Signed=*/true);
}

struct Query {
  std::string smtlib;
  std::vector<Encoder::Decl> decls, witnesses;
  bool reached = false;
  bool theories = false;            // it applies a theory function
  std::vector<std::string> axioms;  // the axioms it was given
  std::vector<std::string> assumes;  // the `assume`s it asserts
  // The axiom assertions, by their index among the query's assertions,
  // and how many assertions there are: for tracking unsat cores.
  std::map<unsigned, std::string> axiomAsserts;
  unsigned asserts = 0;
  // The query without assertion names, whose assertions Z3 lists in the
  // order they are written (named ones it may not), for tracking.
  std::string plain;
};

// The theory axioms an assertion stands for: `Lip.residual_lip#2` is
// Lip.residual_lip with its second trigger.
std::string axiomOf(llvm::StringRef label) {
  return label.split('#').first.str();
}

// The solver for a query with axioms: its assertions again, each axiom
// tracked by a literal named after it, so that an unsat core names the
// axioms the proof used. Null when the parsed assertions do not line up
// with the query's (then the query is solved untracked).
std::string scriptOf(const std::string &smtlib);

std::unique_ptr<z3::solver> tracked(z3::context &ctx, z3::solver &parsed,
                                    const Query &q, const z3::params &p) {
  (void)parsed;
  if (q.axiomAsserts.empty() || q.plain.empty()) return nullptr;
  z3::solver reread(ctx);
  try {
    reread.from_string(scriptOf(q.plain).c_str());
  } catch (const z3::exception &) {
    return nullptr;
  }
  z3::expr_vector as = reread.assertions();
  if (as.size() != q.asserts) return nullptr;
  auto s = std::make_unique<z3::solver>(ctx);
  s->set(p);
  for (unsigned i = 0; i < as.size(); ++i) {
    auto it = q.axiomAsserts.find(i);
    if (it == q.axiomAsserts.end())
      s->add(as[i]);
    else
      s->add(as[i], ctx.bool_const(("axiom!" + it->second).c_str()));
  }
  return s;
}

// The distinct axioms an unsat core names, in a stable order.
std::vector<std::string> coreAxioms(z3::solver &s) {
  std::set<std::string> names;
  z3::expr_vector core = s.unsat_core();
  for (unsigned i = 0; i < core.size(); ++i) {
    std::string text = core[i].to_string();
    llvm::StringRef n(text);
    n.consume_front("|");
    n.consume_back("|");
    if (n.consume_front("axiom!")) names.insert(axiomOf(n));
  }
  return {names.begin(), names.end()};
}

// The export declares a sort only where an op produces a value of it, so
// a sort that appears only in a function's signature, such as `tag` in
// `label : tag -> u8`, is declared here, at the top of the query.
std::string declareSorts(const std::string &smtlib,
                         const std::set<std::string> &sorts) {
  std::string missing;
  for (const std::string &so : sorts)
    if (smtlib.find("(declare-sort " + so + " 0)") == std::string::npos)
      missing += "(declare-sort " + so + " 0)\n";
  if (missing.empty()) return smtlib;
  size_t at = 0;
  if (llvm::StringRef(smtlib).starts_with(";")) at = smtlib.find('\n') + 1;
  return smtlib.substr(0, at) + missing + smtlib.substr(at);
}

// Each axiom's assertion as `(assert (! <fact> :named |T.a|))`: the
// export cannot name an assertion, so the k-th top-level assert, counted
// as the export prints them, gets the name its AssertOp carries.
std::string nameAxioms(const std::string &smtlib,
                       const std::map<unsigned, std::string> &names) {
  if (names.empty()) return smtlib;
  std::string out;
  size_t pos = 0;
  unsigned k = 0;
  // A statement starts with `(` or a `;` comment at column 0; the lines of
  // one statement after its first start otherwise.
  while (pos < smtlib.size()) {
    size_t end = smtlib.find('\n', pos);
    if (end == std::string::npos) end = smtlib.size();
    size_t stmtEnd = end;
    while (stmtEnd + 1 < smtlib.size() && smtlib[stmtEnd + 1] != '(' &&
           smtlib[stmtEnd + 1] != ';') {
      size_t next = smtlib.find('\n', stmtEnd + 1);
      stmtEnd = next == std::string::npos ? smtlib.size() : next;
    }
    llvm::StringRef stmt(smtlib.data() + pos, stmtEnd - pos);
    pos = stmtEnd + 1;
    if (stmt.starts_with("(assert ")) {
      auto it = names.find(k++);
      if (it != names.end() && stmt.ends_with(")")) {
        out += "(assert (! ";
        out += stmt.drop_front(8).drop_back(1).str();
        out += " :named |" + it->second + "|))\n";
        continue;
      }
    }
    out.append(stmt.begin(), stmt.end()).push_back('\n');
  }
  return out;
}

Query buildQuery(mlir::ModuleOp module, mlir::func::FuncOp fn, unsigned width,
                 int target, std::vector<Goal> &goals, bool allAxioms = false) {
  mlir::MLIRContext *ctx = module.getContext();
  OpBuilder b(ctx);
  mlir::OwningOpRef<mlir::ModuleOp> scratch =
      mlir::ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToEnd(scratch->getBody());
#if LLVM_VERSION_MAJOR >= 21
  auto solver = mlir::smt::SolverOp::create(b, b.getUnknownLoc(),
                                            mlir::TypeRange{}, mlir::ValueRange{});
#else
  auto solver = b.create<mlir::smt::SolverOp>(b.getUnknownLoc(),
                                              mlir::TypeRange{}, mlir::ValueRange{});
#endif
  mlir::Block *block = b.createBlock(&solver.getBodyRegion());
  b.setInsertionPointToEnd(block);
  Encoder enc(module, fn, width, target, b, goals);
  enc.run();
  if (target >= 0) enc.addAxioms(allAxioms);
  b.setInsertionPointToEnd(block);
#if LLVM_VERSION_MAJOR >= 21
  mlir::smt::YieldOp::create(b, b.getUnknownLoc());
#else
  b.create<mlir::smt::YieldOp>(b.getUnknownLoc());
#endif
  Query q;
  q.decls = enc.decls();
  q.witnesses = enc.witnesses();
  q.reached = enc.reachedTarget();
  q.theories = enc.usesTheories();
  q.axioms = enc.sentAxioms();
  q.assumes = enc.sentAssumes();
  if (target < 0) return q;
  std::map<unsigned, std::string> axiomNames;
  unsigned k = 0;
  for (Operation &op : *block)
    if (auto a = mlir::dyn_cast<mlir::smt::AssertOp>(op)) {
      if (auto n = a->getAttrOfType<mlir::StringAttr>("pia.axiom"))
        axiomNames[k] = n.getValue().str();
      ++k;
    }
  q.axiomAsserts = axiomNames;
  q.asserts = k;
  llvm::raw_string_ostream os(q.smtlib);
  mlir::smt::SMTEmissionOptions options;
  options.emitReset = false;
  if (mlir::failed(mlir::smt::exportSMTLIB(*scratch, os, options)))
    q.smtlib.clear();
  else {
    std::string text = interpretedSMTLIB(q.smtlib);
    if (!axiomNames.empty()) q.plain = declareSorts(text, enc.sorts());
    q.smtlib = declareSorts(nameAxioms(text, axiomNames), enc.sorts());
  }
  return q;
}

// The consistency check's query for a trusted theory: its axioms and those
// they bring, encoded as a goal's axioms are.
Query buildTheoryQuery(mlir::ModuleOp module, mlir::func::FuncOp axiom,
                       const std::string &theory) {
  mlir::MLIRContext *ctx = module.getContext();
  OpBuilder b(ctx);
  mlir::OwningOpRef<mlir::ModuleOp> scratch =
      mlir::ModuleOp::create(b.getUnknownLoc());
  b.setInsertionPointToEnd(scratch->getBody());
#if LLVM_VERSION_MAJOR >= 21
  auto solver = mlir::smt::SolverOp::create(b, b.getUnknownLoc(),
                                            mlir::TypeRange{}, mlir::ValueRange{});
#else
  auto solver = b.create<mlir::smt::SolverOp>(b.getUnknownLoc(),
                                              mlir::TypeRange{}, mlir::ValueRange{});
#endif
  mlir::Block *block = b.createBlock(&solver.getBodyRegion());
  b.setInsertionPointToEnd(block);
  std::vector<Goal> goals;
  Encoder enc(module, axiom, encodingWidth(module, axiom), -1, b, goals);
  enc.assertTheory(theory);
  b.setInsertionPointToEnd(block);
#if LLVM_VERSION_MAJOR >= 21
  mlir::smt::YieldOp::create(b, b.getUnknownLoc());
#else
  b.create<mlir::smt::YieldOp>(b.getUnknownLoc());
#endif
  Query q;
  q.reached = true;
  q.axioms = enc.sentAxioms();
  std::map<unsigned, std::string> axiomNames;
  unsigned k = 0;
  for (Operation &op : *block)
    if (auto a = mlir::dyn_cast<mlir::smt::AssertOp>(op)) {
      if (auto n = a->getAttrOfType<mlir::StringAttr>("pia.axiom"))
        axiomNames[k] = n.getValue().str();
      ++k;
    }
  q.axiomAsserts = axiomNames;
  q.asserts = k;
  llvm::raw_string_ostream os(q.smtlib);
  mlir::smt::SMTEmissionOptions options;
  options.emitReset = false;
  if (mlir::failed(mlir::smt::exportSMTLIB(*scratch, os, options)))
    q.smtlib.clear();
  else {
    std::string text = interpretedSMTLIB(q.smtlib);
    if (!axiomNames.empty()) q.plain = declareSorts(text, enc.sorts());
    q.smtlib = declareSorts(nameAxioms(text, axiomNames), enc.sorts());
  }
  return q;
}

// --- solving ---------------------------------------------------------------

// One SMT goal, encoded and waiting for a solver thread.
struct Job {
  size_t outcome;  // its index in the outcomes
  Query query;
  unsigned width;
  std::string script;  // the query's declarations and assertions
  bool autoSlice = false;  // in a function with a buffer of records
  // With theories: the query with every axiom of the theories it uses,
  // solved when the relevance closure's query is not proved (ADR 0036).
  std::optional<Query> fallback;
  std::string fallbackScript;
  // The goal in the model's witness copy of its function: a counterexample
  // there is a real one, since the model meets the axioms.
  std::optional<Query> witness;
  std::string witnessScript, witnessModel;
  unsigned witnessWidth = 0;
};

// What one job did, summed into Stats once every thread has finished.
struct JobStats {
  bool solved = false, cached = false, sliced = false, unsliced = false;
  unsigned long long cost = 0;
};

// The declarations and assertions of a query; the solver is asked for the
// result separately.
std::string scriptOf(const std::string &smtlib) {
  std::string script;
  size_t pos = 0;
  while (pos < smtlib.size()) {
    size_t end = smtlib.find('\n', pos);
    if (end == std::string::npos) end = smtlib.size();
    llvm::StringRef line(smtlib.data() + pos, end - pos);
    if (!line.contains("(check-sat)") && !line.contains("(reset)"))
      script.append(line.begin(), line.end()).push_back('\n');
    pos = end + 1;
  }
  return script;
}

// The ids of the uninterpreted constants and functions `e` mentions.
std::vector<unsigned> symbolsOf(const z3::expr &e) {
  std::vector<unsigned> out;
  std::unordered_set<unsigned> seen;
  std::vector<z3::expr> work{e};
  while (!work.empty()) {
    z3::expr x = work.back();
    work.pop_back();
    if (!seen.insert(x.id()).second) continue;
    if (x.is_app()) {
      z3::func_decl d = x.decl();
      if (d.decl_kind() == Z3_OP_UNINTERPRETED) out.push_back(d.id());
      for (unsigned i = 0; i < x.num_args(); ++i) work.push_back(x.arg(i));
    } else if (x.is_quantifier() || x.is_lambda()) {
      work.push_back(x.body());
    }
  }
  return out;
}

// Goal slicing: the assertions the goal can depend on. The encoder asserts
// the goal's negation last. Kept are that assertion and, transitively, every
// assertion that shares a symbol with one already kept. Dropping the rest
// only weakens the hypotheses, so an unsat slice proves the goal.
// `dropsDecl`, when given, is set when some symbol occurs only in dropped
// assertions: the slice leaves out a whole declaration, not just facts
// about symbols the goal can reach.
std::vector<unsigned> sliceOf(const z3::expr_vector &assertions,
                              bool *dropsDecl = nullptr) {
  if (dropsDecl) *dropsDecl = false;
  unsigned n = assertions.size();
  std::vector<unsigned> all(n);
  for (unsigned i = 0; i < n; ++i) all[i] = i;
  if (n < 2) return all;
  std::vector<std::vector<unsigned>> symbols(n);
  std::unordered_map<unsigned, std::vector<unsigned>> users;
  for (unsigned i = 0; i < n; ++i) {
    symbols[i] = symbolsOf(assertions[i]);
    for (unsigned s : symbols[i]) users[s].push_back(i);
  }
  std::vector<bool> kept(n, false);
  std::unordered_set<unsigned> done;
  std::vector<unsigned> work{n - 1};
  kept[n - 1] = true;
  while (!work.empty()) {
    unsigned a = work.back();
    work.pop_back();
    for (unsigned s : symbols[a]) {
      if (!done.insert(s).second) continue;
      for (unsigned b : users[s])
        if (!kept[b]) {
          kept[b] = true;
          work.push_back(b);
        }
    }
  }
  std::vector<unsigned> out;
  for (unsigned i = 0; i < n; ++i)
    if (kept[i]) out.push_back(i);
  if (dropsDecl)
    for (const auto &entry : users)
      if (!done.count(entry.first)) {
        *dropsDecl = true;
        break;
      }
  return out;
}

// The proof cache's key for a query: everything that decides whether Z3
// proves it within the limit.
std::string goalHash(const std::string &query, const Options &options) {
  llvm::SHA256 h;
  h.update("pia-proof-cache v1\n");
  h.update(Z3_get_full_version());
  h.update("\nrlimit " + std::to_string(options.rlimit) + "\n");
  h.update(query);
  std::array<uint8_t, 32> digest = h.final();
  return llvm::toHex(digest, /*LowerCase=*/true);
}

std::string cachePath(const Options &options, const std::string &key) {
  llvm::SmallString<256> path(options.cacheDir);
  llvm::sys::path::append(path, key.substr(0, 2), key);
  return std::string(path);
}

// An entry is `proved <cost>`, and for a goal proved with theory axioms a
// second line `axioms <name>,...`: the unsat core (ADR 0036).
bool cacheLookup(const Options &options, const std::string &key,
                 unsigned long long &cost,
                 std::vector<std::string> *core = nullptr) {
  auto buf = llvm::MemoryBuffer::getFile(cachePath(options, key));
  if (!buf) return false;
  llvm::StringRef text = (*buf)->getBuffer().trim();
  if (!text.consume_front("proved ")) return false;
  auto [first, rest] = text.split('\n');
  if (first.trim().getAsInteger(10, cost)) return false;
  if (core && rest.consume_front("axioms ")) {
    llvm::SmallVector<llvm::StringRef> names;
    rest.trim().split(names, ',', -1, false);
    for (llvm::StringRef n : names) core->push_back(n.str());
  }
  return true;
}

// Written to a unique file and renamed into place, so concurrent builds
// sharing a cache never see a partial entry.
void cacheStore(const Options &options, const std::string &key,
                unsigned long long cost,
                const std::vector<std::string> *core = nullptr) {
  std::string path = cachePath(options, key);
  if (llvm::sys::fs::create_directories(llvm::sys::path::parent_path(path)))
    return;
  llvm::SmallString<256> tmp;
  int fd;
  if (llvm::sys::fs::createUniqueFile(path + ".%%%%%%%%.tmp", fd, tmp))
    return;
  {
    llvm::raw_fd_ostream os(fd, /*shouldClose=*/true);
    os << "proved " << cost << "\n";
    if (core && !core->empty()) {
      os << "axioms ";
      for (size_t i = 0; i < core->size(); ++i)
        os << (i ? "," : "") << (*core)[i];
      os << "\n";
    }
  }
  if (llvm::sys::fs::rename(tmp, path)) llvm::sys::fs::remove(tmp);
}

// Z3's resource count so far in the solver's context.
unsigned long long rlimitCount(z3::solver &solver) {
  z3::stats st = solver.statistics();
  for (unsigned i = 0; i < st.size(); ++i)
    if (st.key(i) == "rlimit count")
      return st.is_uint(i) ? st.uint_value(i)
                           : static_cast<unsigned long long>(st.double_value(i));
  return 0;
}

// Decides one goal in a Z3 context of its own, so jobs can run on any
// thread. The rlimit makes the result independent of which thread, and of
// how busy the machine is.
void solve(const Job &job, const Options &options, Outcome &out,
           JobStats &js) {
  const Query &q = job.query;
  if (q.smtlib.empty() || !q.reached) {
    out.status = Status::Failed;
    out.method = "the goal could not be encoded";
    return;
  }
  z3::context ctx;
  z3::params p(ctx);
  p.set("timeout", options.timeoutMs);
  if (options.rlimit) p.set("rlimit", options.rlimit);
  z3::solver full(ctx);
  full.set(p);
  try {
    full.from_string(job.script.c_str());
  } catch (const z3::exception &e) {
    out.status = Status::Failed;
    out.method = std::string("the solver rejected the query: ") + e.msg();
    return;
  }
  z3::solver sliced(ctx);
  sliced.set(p);
  z3::solver *first = &full;
  // A query with theory axioms is solved with each axiom tracked, so the
  // proof's unsat core says which axioms it used (ADR 0036). Only those
  // queries: every other one is solved exactly as before.
  // The query is solved as it is first, since tracking slows the search
  // for a counterexample; only a proof is solved again, tracked, for its
  // core. That second run is the cost of knowing which axioms a goal used.
  auto used = [&](z3::solver &solved, const Query &query) {
    if (std::unique_ptr<z3::solver> t = tracked(ctx, solved, query, p)) {
      unsigned long long before = rlimitCount(*t);
      z3::check_result r = t->check();
      js.cost += rlimitCount(*t) - before;
      if (r == z3::unsat) return coreAxioms(*t);
    }
    std::set<std::string> all(query.axioms.begin(), query.axioms.end());
    all.insert(query.assumes.begin(), query.assumes.end());
    return std::vector<std::string>(all.begin(), all.end());
  };
  if (q.axioms.empty() && (options.slice == Options::Slice::On ||
      (options.slice == Options::Slice::Auto && job.autoSlice))) {
    z3::expr_vector as = full.assertions();
    bool dropsDecl = false;
    std::vector<unsigned> keep = sliceOf(as, &dropsDecl);
    bool use = options.slice == Options::Slice::On ||
               (job.autoSlice && dropsDecl);
    if (use && keep.size() < as.size()) {
      for (unsigned i : keep) sliced.add(as[i]);
      first = &sliced;
      js.sliced = true;
    }
  }
  // Keyed by the whole query, so a goal proved either way is cached.
  std::string key;
  if (!options.cacheDir.empty()) {
    key = goalHash(job.script, options);
    unsigned long long cost = 0;
    std::vector<std::string> core;
    if (cacheLookup(options, key, cost, &core)) {
      js.cached = true;
      out.status = Status::Proved;
      out.method = "smt";
      if (options.reportCost) out.cost = cost;
      out.axiomsUsed = core;
      return;
    }
  }
  js.solved = true;
  z3::check_result result = z3::unknown;
  // With a model, the goal is first tried in the model's witness copy of
  // its function (ADR 0036). There everything is concrete, so the solver
  // decides it quickly, and a counterexample there is one to the axioms
  // too, since the model meets them: the goal fails without the queries
  // over the axioms, whose quantifiers can keep a solver looking for a
  // model for a long time. If the witness holds, the axioms decide.
  const Query *answer = &q;
  z3::solver witness(ctx);
  z3::solver *last = &full;
  unsigned width = job.width;
  if (job.witness) {
    witness.set(p);
    try {
      witness.from_string(job.witnessScript.c_str());
      unsigned long long before = rlimitCount(witness);
      z3::check_result w = witness.check();
      js.cost += rlimitCount(witness) - before;
      if (w == z3::sat) {
        answer = &*job.witness;
        last = &witness;
        result = z3::sat;
        width = job.witnessWidth;
        out.model = job.witnessModel;
      }
    } catch (const z3::exception &) {
    }
  }
  if (last != &witness) try {
    unsigned long long before = rlimitCount(*first);
    result = first->check();
    unsigned long long now = rlimitCount(*first);
    js.cost += now - before;
    if (result == z3::unsat) {
      out.status = Status::Proved;
      out.method = "smt";
      if (options.reportCost) out.cost = now - before;
      if (!q.axioms.empty() || !q.assumes.empty())
        out.axiomsUsed = used(full, q);
      if (!key.empty()) cacheStore(options, key, now - before, &out.axiomsUsed);
      return;
    }
    if (first != &full) {
      // The slice may have dropped an assumption the proof needs, such as
      // a contradictory path condition: decide the whole query.
      js.unsliced = true;
      before = now;
      result = full.check();
      now = rlimitCount(full);
      js.cost += now - before;
      if (result == z3::unsat) {
        out.status = Status::Proved;
        out.method = "smt";
        if (options.reportCost) out.cost = now - before;
        if (!q.assumes.empty()) out.axiomsUsed = used(full, q);
        if (!key.empty()) cacheStore(options, key, now - before, &out.axiomsUsed);
        return;
      }
    }
  } catch (const z3::exception &e) {
    out.status = Status::Failed;
    out.method = std::string("the solver failed: ") + e.msg();
    return;
  }
  // Not proved with the axioms the relevance closure chose: solve again
  // with every axiom of the theories the goal mentions, and take the
  // counterexample from that run, so a missing axiom never makes one up
  // (ADR 0036, "Fallback on failure").
  z3::solver fallback(ctx);
  if (job.fallback && last != &witness) {
    out.fallback = true;
    out.axioms = job.fallback->axioms;
    std::string fkey;
    if (!options.cacheDir.empty()) {
      fkey = goalHash(job.fallbackScript, options);
      unsigned long long cost = 0;
      std::vector<std::string> core;
      if (cacheLookup(options, fkey, cost, &core)) {
        js.cached = true;
        out.status = Status::Proved;
        out.method = "smt";
        if (options.reportCost) out.cost = cost;
        out.axiomsUsed = core;
        return;
      }
    }
    fallback.set(p);
    try {
      fallback.from_string(job.fallbackScript.c_str());
      unsigned long long before = rlimitCount(fallback);
      result = fallback.check();
      unsigned long long now = rlimitCount(fallback);
      js.cost += now - before;
      if (result == z3::unsat) {
        out.status = Status::Proved;
        out.method = "smt";
        if (options.reportCost) out.cost = now - before;
        out.axiomsUsed = used(fallback, *job.fallback);
        if (!fkey.empty()) cacheStore(options, fkey, now - before, &out.axiomsUsed);
        return;
      }
    } catch (const z3::exception &e) {
      out.status = Status::Failed;
      out.method = std::string("the solver failed: ") + e.msg();
      return;
    }
    answer = &*job.fallback;
    last = &fallback;
  }
  if (result == z3::unknown) {
    out.status = Status::Failed;
    out.method = "the solver gave up: " + last->reason_unknown();
    return;
  }
  out.status = Status::Failed;
  out.method = "counterexample";
  z3::model m = last->get_model();
  using Sort = Encoder::Sort;
  auto value = [&](const Encoder::Decl &d) -> std::string {
    const char *name = d.exported.c_str();
    if (d.sort == Sort::Uninterpreted) {
      // A value of a theory's sort: Z3 names the model's elements, such as
      // `Lip.layer!val!0`; two names that differ are different values.
      for (unsigned i = 0; i < m.num_consts(); ++i)
        if (m.get_const_decl(i).name().str() == d.exported)
          return m.get_const_interp(m.get_const_decl(i)).to_string();
      return "any";
    }
    z3::expr c = d.sort == Sort::Bool  ? ctx.bool_const(name)
                 : d.sort == Sort::Int  ? ctx.int_const(name)
                 : d.sort == Sort::Real ? ctx.real_const(name)
                                        : ctx.bv_const(name, width);
    z3::expr v = m.eval(c, /*model_completion=*/true);
    if (d.sort == Sort::Bool) return v.is_true() ? "true" : "false";
    if (d.sort == Sort::Int) return v.get_decimal_string(0);
    if (d.sort == Sort::Real) {
      // A rational as n/d; an irrational root of a nonlinear model as a
      // decimal approximation.
      if (v.is_numeral()) return Z3_get_numeral_string(ctx, v);
      if (v.is_algebraic()) return "~" + v.get_decimal_string(6);
      return v.to_string();
    }
    return signedDecimal(v.get_decimal_string(0), width);
  };
  for (const Encoder::Decl &d : answer->decls)
    out.counterexample.push_back({d.display, value(d)});
  for (const Encoder::Decl &d : answer->witnesses)
    out.counterexample.push_back({d.display, value(d)});
}

// Solves every job on a pool of threads. Each job writes only its own
// outcome, so the outcomes keep the walk order whatever the schedule.
unsigned solveAll(std::vector<Job> &jobs, std::vector<Outcome> &outcomes,
                  const Options &options, Stats &st) {
  if (jobs.empty()) return 0;
  unsigned threads = options.jobs ? options.jobs
                                  : std::max(1u, std::thread::hardware_concurrency());
  threads = std::min<size_t>(threads, jobs.size());
  // The largest queries first, so a big one does not start last.
  std::vector<size_t> order(jobs.size());
  for (size_t i = 0; i < order.size(); ++i) order[i] = i;
  std::stable_sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return jobs[a].script.size() > jobs[b].script.size();
  });
  std::vector<JobStats> js(jobs.size());
  std::atomic<size_t> next{0};
  auto worker = [&] {
    for (size_t k; (k = next.fetch_add(1)) < order.size();) {
      size_t i = order[k];
      solve(jobs[i], options, outcomes[jobs[i].outcome], js[i]);
    }
  };
  std::vector<std::thread> pool;
  for (unsigned t = 1; t < threads; ++t) pool.emplace_back(worker);
  worker();
  for (std::thread &t : pool) t.join();
  for (const JobStats &j : js) {
    st.solved += j.solved;
    st.cached += j.cached;
    st.sliced += j.sliced;
    st.unsliced += j.unsliced;
    st.cost += j.cost;
  }
  return threads;
}

double msSince(std::chrono::steady_clock::time_point t) {
  return std::chrono::duration<double, std::milli>(
             std::chrono::steady_clock::now() - t)
      .count();
}

}  // namespace

bool selects(const std::string &spec, const std::string &where,
             const std::string &function) {
  llvm::StringRef s(spec);
  if (s.ends_with(".pia") || s.ends_with(".pia.md")) {
    // A module: the file part of "file:line:col".
    llvm::StringRef w(where);
    llvm::StringRef file = w.rsplit(':').first.rsplit(':').first;
    return llvm::sys::path::filename(file) == llvm::sys::path::filename(s);
  }
  if (s.contains(':'))
    return where == spec || llvm::StringRef(where).starts_with(spec + ":");
  return function == spec;
}

bool isContractGoal(contract::ObligationKind kind) {
  using K = contract::ObligationKind;
  switch (kind) {
    case K::requires_:
    case K::ensures:
    case K::invariant:
    case K::decreases:
    case K::assert_:
    case K::law:
      return true;
    default:
      return false;
  }
}

mlir::LogicalResult resolveOverloads(mlir::ModuleOp module,
                                     const Options &options) {
  struct Site {
    std::string fn;
    unsigned index;  // among the function's calls, in walk order
    mlir::func::CallOp call;
    std::vector<std::string> candidates;
  };
  std::vector<Site> sites;
  for (auto fn : module.getOps<mlir::func::FuncOp>()) {
    unsigned i = 0;
    fn.walk([&](mlir::func::CallOp c) {
      if (auto a = c->getAttrOfType<mlir::ArrayAttr>("pia.overload_candidates")) {
        Site s{fn.getSymName().str(), i, c, {}};
        for (auto ref : a.getAsRange<mlir::FlatSymbolRefAttr>())
          s.candidates.push_back(ref.getValue().str());
        sites.push_back(std::move(s));
      }
      ++i;
    });
  }
  if (sites.empty()) return mlir::success();
  module.getContext()->loadDialect<mlir::smt::SMTDialect>();
  // Encoding needs a module without records; the choices are copied back.
  mlir::OwningOpRef<mlir::ModuleOp> copy = module.clone();
  if (mlir::failed(transforms::scalarizeRecords(*copy))) return mlir::failure();
  Options o = options;
  o.only.clear();
  for (Site &s : sites) {
    auto fn = copy->lookupSymbol<mlir::func::FuncOp>(s.fn);
    if (!fn) return mlir::failure();
    mlir::func::CallOp target;
    unsigned i = 0;
    fn.walk([&](mlir::func::CallOp c) {
      if (i++ == s.index) target = c;
    });
    if (!target) return mlir::failure();
    unsigned width = encodingWidth(*copy, fn);
    std::string chosen;
    for (size_t k = 0; k + 1 < s.candidates.size() && chosen.empty(); ++k) {
      target.setCallee(s.candidates[k]);
      std::vector<Goal> goals;
      buildQuery(*copy, fn, width, -1, goals);
      bool all = true;
      for (size_t g = 0; g < goals.size() && all; ++g) {
        if (goals[g].op != target.getOperation() ||
            goals[g].kind != ObligationKind::requires_)
          continue;
        if (goals[g].byIntervals) continue;
        if (goals[g].skipped) {
          all = false;
          continue;
        }
        std::vector<Goal> unused;
        Job job{0, buildQuery(*copy, fn, width, static_cast<int>(g), unused),
                width, ""};
        job.script = scriptOf(job.query.smtlib);
        Outcome out;
        JobStats js;
        solve(job, o, out, js);
        all = out.status == Status::Proved;
      }
      if (all) chosen = s.candidates[k];
    }
    if (chosen.empty()) chosen = s.candidates.back();
    target.setCallee(chosen);
    target->removeAttr("pia.overload_candidates");
    s.call.setCallee(chosen);
    s.call->removeAttr("pia.overload_candidates");
  }
  return mlir::success();
}

std::vector<Outcome> verifyModule(mlir::ModuleOp module,
                                  const Options &options, Stats *stats) {
  auto start = std::chrono::steady_clock::now();
  Stats st;
  module.getContext()->loadDialect<mlir::smt::SMTDialect>();
  // The encoding has no records: each record value becomes its fields.
  (void)transforms::scalarizeRecords(module);
  // Encoding uses the module's MLIR context, so it runs on this thread;
  // only solving is parallel.
  std::vector<Outcome> outcomes;
  std::vector<Operation *> opOf;  // the op that raised each outcome
  llvm::DenseSet<Operation *> partial;  // ops with an unselected goal
  std::vector<Job> jobs;
  // Each function's witness copy in a model (ADR 0036), and its goals.
  std::map<std::string, mlir::func::FuncOp> witnessOf;
  for (auto fn : module.getOps<mlir::func::FuncOp>())
    if (auto w = fn->getAttrOfType<mlir::StringAttr>("pia.witness_of"))
      witnessOf[w.getValue().str()] = fn;
  std::map<Operation *, std::vector<Goal>> witnessGoals;
  // A trusted theory, one with axioms and no model, is checked for
  // consistency once (ADR 0036): are its axioms satisfiable?
  if (options.only.empty()) {
    std::map<std::string, mlir::func::FuncOp> trusted;
    for (auto fn : module.getOps<mlir::func::FuncOp>())
      if (fn->hasAttr(PiaDialect::getAxiomAttrName()) &&
          !fn->hasAttr("pia.modelled") && !theoryOf(fn).empty())
        trusted.emplace(theoryOf(fn), fn);
    for (auto &[theory, first] : trusted) {
      TheoryCheck c;
      c.theory = theory;
      c.where = formatLoc(first.getLoc());
      Query q = buildTheoryQuery(module, first, theory);
      std::string script = scriptOf(q.smtlib);
      z3::context ctx;
      z3::params p(ctx);
      p.set("timeout", options.timeoutMs);
      if (options.rlimit) p.set("rlimit", options.rlimit);
      z3::solver solver(ctx);
      solver.set(p);
      try {
        solver.from_string(script.c_str());
        unsigned long long before = rlimitCount(solver);
        z3::check_result r = solver.check();
        st.cost += rlimitCount(solver) - before;
        if (r == z3::sat) {
          c.status = "consistent";
        } else if (r == z3::unknown) {
          c.status = "unchecked";
          c.reason = solver.reason_unknown();
        } else {
          c.status = "inconsistent";
          if (auto t = tracked(ctx, solver, q, p); t && t->check() == z3::unsat)
            c.core = coreAxioms(*t);
          else
            c.core.assign(q.axioms.begin(), q.axioms.end());
        }
      } catch (const z3::exception &e) {
        c.status = "unchecked";
        c.reason = e.msg();
      }
      if (c.status == "inconsistent") {
        Outcome out;
        out.kind = ObligationKind::assert_;
        out.where = c.where;
        out.function = first.getSymName().str();
        out.claim = "the axioms of the theory '" + theory + "' are consistent";
        out.status = Status::Failed;
        out.method = "they contradict each other:";
        for (size_t i = 0; i < c.core.size(); ++i)
          out.method += (i ? ", " : " ") + c.core[i];
        ++st.goals;
        opOf.push_back(first.getOperation());
        outcomes.push_back(std::move(out));
      }
      st.theories.push_back(std::move(c));
    }
  }
  for (auto fn : module.getOps<mlir::func::FuncOp>()) {
    // An imported function is proved by its own module (ADR 0039).
    if (fn.isExternal() || fn->hasAttr(PiaDialect::getImportAttrName()))
      continue;
    // A foreign function's contract is trusted, not proved (#55).
    if (fn->hasAttr("pia.extern")) continue;
    // A witness copy only explains another function's failures.
    if (fn->hasAttr("pia.witness_of")) continue;
    // An axiom is not proved: without a model it is trusted (ADR 0036).
    if (fn->hasAttr(PiaDialect::getAxiomAttrName())) {
      std::vector<std::string> texts;
      for (const Trigger &t : axiomTriggers(module, fn).triggers)
        texts.push_back(t.text);
      st.triggers.emplace_back(fn.getSymName().str(), std::move(texts));
      continue;
    }
    unsigned width = encodingWidth(module, fn);
    std::vector<Goal> goals;
    buildQuery(module, fn, width, -1, goals);
    for (size_t i = 0; i < goals.size(); ++i) {
      Goal &g = goals[i];
      Outcome out;
      out.kind = g.kind;
      out.where = formatLoc(g.op->getLoc());
      out.function = fn.getSymName().str();
      out.claim = g.claim;
      if (!options.only.empty() &&
          std::none_of(options.only.begin(), options.only.end(),
                       [&](const std::string &spec) {
                         return selects(spec, out.where, out.function);
                       })) {
        ++st.unselected;
        partial.insert(g.op);
        continue;
      }
      ++st.goals;
      if (g.skipped) {
        ++st.skipped;
        out.status = Status::Skipped;
        out.method = g.reason;
      } else if (g.byIntervals) {
        ++st.intervals;
        out.status = Status::Proved;
        out.method = "intervals";
      } else {
        std::vector<Goal> unused;
        Job job{outcomes.size(),
                buildQuery(module, fn, width, static_cast<int>(i), unused),
                width, ""};
        job.script = scriptOf(job.query.smtlib);
        job.autoSlice = fn->hasAttr(PiaDialect::getRecordBuffersAttrName());
        if (options.dumpSmt && !job.query.smtlib.empty())
          llvm::errs() << "; " << out.where << ": " << out.claim << "\n"
                       << job.query.smtlib << "\n";
        out.axioms = job.query.axioms;
        if (job.query.theories)
          if (auto w = witnessOf.find(fn.getSymName().str());
              w != witnessOf.end()) {
            mlir::func::FuncOp wf = w->second;
            auto &wgoals = witnessGoals[wf.getOperation()];
            unsigned wwidth = encodingWidth(module, wf);
            if (wgoals.empty()) buildQuery(module, wf, wwidth, -1, wgoals);
            for (size_t k = 0; k < wgoals.size(); ++k)
              if (wgoals[k].kind == g.kind && !wgoals[k].skipped &&
                  wgoals[k].op->getLoc() == g.op->getLoc()) {
                std::vector<Goal> unused3;
                Query wq = buildQuery(module, wf, wwidth, static_cast<int>(k),
                                      unused3);
                if (wq.smtlib.empty() || !wq.reached) break;
                job.witnessScript = scriptOf(wq.smtlib);
                job.witnessWidth = wwidth;
                job.witnessModel =
                    wf->getAttrOfType<mlir::StringAttr>("pia.model").getValue().str();
                if (options.dumpSmt)
                  llvm::errs() << "; " << out.where << ": " << out.claim
                               << " (in the model '" << job.witnessModel
                               << "')\n" << wq.smtlib << "\n";
                job.witness = std::move(wq);
                break;
              }
          }
        if (job.query.theories) {
          std::vector<Goal> unused2;
          Query all = buildQuery(module, fn, width, static_cast<int>(i),
                                 unused2, /*allAxioms=*/true);
          if (all.axioms.size() > job.query.axioms.size()) {
            job.fallbackScript = scriptOf(all.smtlib);
            if (options.dumpSmt && !all.smtlib.empty())
              llvm::errs() << "; " << out.where << ": " << out.claim
                           << " (fallback, every axiom)\n"
                           << all.smtlib << "\n";
            job.fallback = std::move(all);
          }
        }
        jobs.push_back(std::move(job));
      }
      opOf.push_back(g.op);
      outcomes.push_back(std::move(out));
    }
  }
  st.encodeMs = msSince(start);
  auto solving = std::chrono::steady_clock::now();
  st.threads = solveAll(jobs, outcomes, options, st);
  st.solveMs = msSince(solving);
  for (const Outcome &o : outcomes) {
    bool smt = o.method != "intervals" && o.status != Status::Skipped;
    if (isContractGoal(o.kind)) {
      ++st.contractGoals;
      st.contractSmt += smt;
      st.contractCost += o.cost;
    } else {
      ++st.typeGoals;
      st.typeSmt += smt;
      st.typeCost += o.cost;
    }
  }
  // Per op: whether every goal it raises holds, and how.
  llvm::DenseMap<Operation *, std::pair<bool, bool>> proved;  // all, smt
  llvm::SmallVector<Operation *> order;
  for (size_t i = 0; i < outcomes.size(); ++i) {
    auto [it, fresh] =
        proved.try_emplace(opOf[i], std::make_pair(true, false));
    if (fresh) order.push_back(opOf[i]);
    if (outcomes[i].status != Status::Proved) it->second.first = false;
    if (outcomes[i].method == "smt") it->second.second = true;
  }
  for (Operation *op : order) {
    auto state = proved.lookup(op);
    if (state.first && !partial.contains(op))
      op->setAttr("pia.proved",
                  mlir::StringAttr::get(module.getContext(),
                                        state.second ? "smt" : "intervals"));
  }
  if (stats) *stats = st;
  return outcomes;
}

}  // namespace pia::verify
