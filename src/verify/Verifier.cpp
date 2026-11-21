#include "verify/Verifier.h"

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>

#include "dialect/PiaDialect.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
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
  return std::nullopt;
}

bool isContractSink(Operation *op) {
  return mlir::isa<contract::RequiresOp, contract::EnsuresOp,
                   contract::InvariantOp, contract::DecreasesOp,
                   contract::AssertOp, contract::AssumeOp,
                   contract::ObligationOp, contract::OldOp,
                   contract::YieldOp>(op);
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
        spec_(specOps(fn)) {}

  struct Decl {
    std::string exported;  // the SMT-LIB name
    std::string display;   // the name shown in a counterexample
    bool isBool;
  };

  void run() {
    mlir::Block &entry = fn_.getBody().front();
    for (unsigned i = 0; i < entry.getNumArguments(); ++i) declareParam(entry.getArgument(i), i);
    entryArrays_ = arrays_;
    walkBlock(entry, nullptr);
  }

  bool reachedTarget() const { return done_; }
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

  Type sortOf(Type t) {
    if (mlir::isa<IntType, mlir::IndexType>(t)) return bvType();
    if (t.isInteger(1)) return boolType();
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
  void assertTerm(Value t) { create<mlir::smt::AssertOp>(t); }

  Value inRange(Value t, IntType ty) {
    using P = mlir::smt::BVCmpPredicate;
    return andOf(cmp(P::sle, bv(ty.getLo()), t), cmp(P::sle, t, bv(ty.getHi())));
  }

  Value declare(Type sort, const std::string &display, bool record = true) {
    std::string name = "pia_" + std::to_string(nextName_++);
    Value v = create<mlir::smt::DeclareFunOp>(sort, b_.getStringAttr(name));
    if (record && !display.empty())
      decls_.push_back({name, display, mlir::isa<mlir::smt::BoolType>(sort)});
    return v;
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
      if (auto a = mlir::dyn_cast<ArrayType>(t)) {
        lengths_[arg] = bv(APInt(64, a.getLength()));
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

  void assume(Value t) {
    if (pc_.empty())
      assertTerm(t);
    else
      assertTerm(implies(pathCondition(), t));
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
                            label, mlir::isa<mlir::smt::BoolType>(value.getType())});
      assertTerm(eq(w, value));
    }
    assertTerm(andOf(pathCondition(), notOf(term)));
    done_ = true;
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
    if (mlir::isa<LoadOp, StoreOp>(op))
      out.push_back({ObligationKind::inbounds, "the index is within bounds"});
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
      assume(term(a.getPredicate()));
      return true;
    }
    if (auto e = mlir::dyn_cast<contract::EnsuresOp>(op)) {
      goal(ObligationKind::ensures, op, "the postcondition holds",
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
      Value arr = arrays_.lookup(store.getBuffer());
      if (!idx || !len || !arr) return true;
      goal(ObligationKind::inbounds, op, "the index is within bounds",
           andOf(cmp(P::sge, idx, bv(0)), cmp(P::slt, idx, len)),
           indexByIntervals(store.getBuffer(), store.getIndex()),
           {{"index", idx}, {"length", len}});
      Value v = term(store.getValue());
      if (v)
        arrays_[store.getBuffer()] = create<mlir::smt::ArrayStoreOp>(
            arr.getType(), arr, idx, v);
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
          goal(ObligationKind::inbounds, op, "the index is within bounds",
               andOf(cmp(P::sge, idx, bv(0)), cmp(P::slt, idx, len)),
               indexByIntervals(ld.getBuffer(), ld.getIndex()),
               {{"index", idx}, {"length", len}});
      }
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
    if (semantics(op, operands, arrays_, lengths_, results)) {
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

  // The value semantics shared by the forward walk and demand encoding.
  // Returns false for ops it does not model.
  bool semantics(Operation *op, llvm::ArrayRef<Value> in,
                 llvm::DenseMap<Value, Value> &arrays,
                 llvm::DenseMap<Value, Value> &lengths,
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
      Value arr = arrays.lookup(ld.getBuffer());
      Type sort = sortOf(ld.getType());
      if (!arr || !sort) return false;
      out.push_back(
          create<mlir::smt::ArraySelectOp>(sort, arr, in[1]));
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
    pc_.push_back(c);
    bool ok = walkBlock(ifOp.getThenRegion().front(), &thenYields);
    pc_.pop_back();
    if (!ok) return false;
    auto thenArrays = arrays_;
    arrays_ = before;
    if (!ifOp.getElseRegion().empty()) {
      pc_.push_back(notOf(c));
      ok = walkBlock(ifOp.getElseRegion().front(), &elseYields);
      pc_.pop_back();
      if (!ok) return false;
    }
    for (auto &[buffer, array] : arrays_) {
      Value t = thenArrays.lookup(buffer);
      if (t && t != array) array = ite(c, t, array);
    }
    for (unsigned i = 0; i < ifOp.getNumResults(); ++i) {
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
      if (auto st = mlir::dyn_cast<StoreOp>(op)) out.insert(st.getBuffer());
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        for (unsigned i = 0; i < call.getNumOperands(); ++i)
          if (callWrites(call, i)) out.insert(call.getOperand(i));
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
          pre.arrays[formal] = arrays_.lookup(actual);
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
    for (Value r : call.getResults())
      if (auto v = havoc(r.getType())) env_[r] = *v;
    for (unsigned i = 0; i < call.getNumOperands(); ++i) {
      Value actual = call.getOperand(i);
      if (callWrites(call, i) && arrays_.count(actual))
        arrays_[actual] = declare(arrays_[actual].getType(), "", false);
    }
    if (!hasBody) return true;
    Demand post = pre;
    post.memo.clear();
    post.oldArrays = pre.arrays;
    mlir::Block &entry = callee.getBody().front();
    for (unsigned i = 0; i < call.getNumOperands(); ++i)
      if (mlir::isa<ArrayType, SliceType>(call.getOperand(i).getType()))
        post.arrays[entry.getArgument(i)] = arrays_.lookup(call.getOperand(i));
    callee.walk([&](mlir::func::ReturnOp ret) {
      for (auto [formal, actual] : llvm::zip(ret.getOperands(), call.getResults())) {
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
    } else {
      llvm::SmallVector<Value> operands;
      for (Value o : op->getOperands()) operands.push_back(demand(o, d));
      llvm::SmallVector<Value> results;
      if (semantics(op, operands, d.arrays, d.lengths, results))
        result = results[mlir::cast<mlir::OpResult>(v).getResultNumber()];
    }
    if (!result) {
      // A call or an op the verifier does not model: any value of its type.
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
      Value p = demand(yield.getPredicate(), d);
      if (!p) {
        failed = true;
        p = boolConst(true);
      }
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

  mlir::ModuleOp module_;
  mlir::func::FuncOp fn_;
  unsigned width_;
  int target_;
  OpBuilder &b_;
  std::vector<Goal> &goals_;
  mlir::MLIRContext *ctx_;
  Location loc_;
  llvm::DenseSet<Operation *> spec_;

  llvm::DenseMap<Value, Value> env_;
  llvm::DenseMap<Value, Value> arrays_, lengths_, entryArrays_;
  std::vector<Value> pc_;
  std::vector<Decl> decls_, witnesses_;
  int counter_ = 0;
  int nextName_ = 0;
  int quantifierDepth_ = 0;
  bool done_ = false;
};

// Values in the bit-vector encoding are signed and wide enough for every
// exact intermediate: 64-bit operands need 66 bits for a sum and 130 for
// a product.
unsigned encodingWidth(mlir::ModuleOp module) {
  bool mul = false;
  module.walk([&](MulOp) { mul = true; });
  return mul ? 132 : 68;
}

std::string signedDecimal(const std::string &unsignedDecimal, unsigned width) {
  APInt v(width, unsignedDecimal, 10);
  return llvm::toString(v, 10, /*Signed=*/true);
}

struct Query {
  std::string smtlib;
  std::vector<Encoder::Decl> decls, witnesses;
  bool reached = false;
};

Query buildQuery(mlir::ModuleOp module, mlir::func::FuncOp fn, unsigned width,
                 int target, std::vector<Goal> &goals) {
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
  if (target < 0) return q;
  llvm::raw_string_ostream os(q.smtlib);
  mlir::smt::SMTEmissionOptions options;
  options.emitReset = false;
  if (mlir::failed(mlir::smt::exportSMTLIB(*scratch, os, options)))
    q.smtlib.clear();
  return q;
}

void solve(const Query &q, unsigned width, const Options &options,
           Outcome &out) {
  if (q.smtlib.empty() || !q.reached) {
    out.status = Status::Failed;
    out.method = "the goal could not be encoded";
    return;
  }
  if (options.dumpSmt) llvm::errs() << "; " << out.where << ": " << out.claim
                                    << "\n" << q.smtlib << "\n";
  // Keep the declarations and assertions; this code asks for the result.
  std::string script;
  size_t pos = 0;
  while (pos < q.smtlib.size()) {
    size_t end = q.smtlib.find('\n', pos);
    if (end == std::string::npos) end = q.smtlib.size();
    std::string line = q.smtlib.substr(pos, end - pos);
    if (line.find("(check-sat)") == std::string::npos &&
        line.find("(reset)") == std::string::npos)
      script += line + "\n";
    pos = end + 1;
  }
  z3::context ctx;
  z3::solver solver(ctx);
  z3::params p(ctx);
  p.set("timeout", options.timeoutMs);
  solver.set(p);
  try {
    solver.from_string(script.c_str());
  } catch (const z3::exception &e) {
    out.status = Status::Failed;
    out.method = std::string("the solver rejected the query: ") + e.msg();
    return;
  }
  switch (solver.check()) {
    case z3::unsat:
      out.status = Status::Proved;
      out.method = "smt";
      return;
    case z3::unknown:
      out.status = Status::Failed;
      out.method = "the solver gave up: " + solver.reason_unknown();
      return;
    case z3::sat:
      break;
  }
  out.status = Status::Failed;
  out.method = "counterexample";
  z3::model m = solver.get_model();
  auto value = [&](const Encoder::Decl &d) -> std::string {
    z3::expr c = d.isBool ? ctx.bool_const(d.exported.c_str())
                          : ctx.bv_const(d.exported.c_str(), width);
    z3::expr v = m.eval(c, /*model_completion=*/true);
    if (d.isBool) return v.is_true() ? "true" : "false";
    return signedDecimal(v.get_decimal_string(0), width);
  };
  for (const Encoder::Decl &d : q.decls)
    out.counterexample.push_back({d.display, value(d)});
  for (const Encoder::Decl &d : q.witnesses)
    out.counterexample.push_back({d.display, value(d)});
}

}  // namespace

std::vector<Outcome> verifyModule(mlir::ModuleOp module,
                                  const Options &options) {
  module.getContext()->loadDialect<mlir::smt::SMTDialect>();
  // The encoding has no records: each record value becomes its fields.
  (void)transforms::scalarizeRecords(module);
  unsigned width = encodingWidth(module);
  std::vector<Outcome> outcomes;
  for (auto fn : module.getOps<mlir::func::FuncOp>()) {
    if (fn.isExternal()) continue;
    std::vector<Goal> goals;
    buildQuery(module, fn, width, -1, goals);
    // Per op: whether every goal it raises holds, and how.
    llvm::DenseMap<Operation *, std::pair<bool, bool>> proved;  // all, smt
    for (size_t i = 0; i < goals.size(); ++i) {
      Goal &g = goals[i];
      Outcome out;
      out.kind = g.kind;
      out.where = formatLoc(g.op->getLoc());
      out.function = fn.getSymName().str();
      out.claim = g.claim;
      if (g.skipped) {
        out.status = Status::Skipped;
        out.method = g.reason;
      } else if (g.byIntervals) {
        out.status = Status::Proved;
        out.method = "intervals";
      } else {
        std::vector<Goal> unused;
        Query q = buildQuery(module, fn, width, static_cast<int>(i), unused);
        solve(q, width, options, out);
      }
      auto &entry = proved.try_emplace(g.op, std::make_pair(true, false))
                        .first->second;
      if (out.status != Status::Proved) entry.first = false;
      if (out.method == "smt") entry.second = true;
      outcomes.push_back(std::move(out));
    }
    for (auto &[op, state] : proved)
      if (state.first)
        op->setAttr("pia.proved", mlir::StringAttr::get(
                                      module.getContext(),
                                      state.second ? "smt" : "intervals"));
  }
  return outcomes;
}

}  // namespace pia::verify
