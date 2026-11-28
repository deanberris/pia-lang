#include "codegen/Phases.h"

#include <utility>

#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Interfaces/ViewLikeInterface.h"
#include "mlir/Transforms/RegionUtils.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Config/llvm-config.h"

namespace pia::codegen {

using mlir::Location;
using mlir::LogicalResult;
using mlir::Operation;
using mlir::Type;
using mlir::Value;
namespace scf = mlir::scf;
namespace arith = mlir::arith;
namespace memref = mlir::memref;

namespace {

// Ops are created with the builder API of the LLVM in use.
template <typename Op, typename... Args>
Op make(mlir::OpBuilder &b, Location loc, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
  return Op::create(b, loc, std::forward<Args>(args)...);
#else
  return b.create<Op>(loc, std::forward<Args>(args)...);
#endif
}

// A gathered slice (ADR 0086): a call of one of the declarations that
// Codegen.cpp's declareGathers made.
mlir::func::CallOp gatherCall(Operation *op) {
  auto c = mlir::dyn_cast<mlir::func::CallOp>(op);
  if (c && c.getCallee().starts_with(kGatherPrefix))
    return c;
  return nullptr;
}

// A call of a function marked `pia.collective`, which IRGen checked.
mlir::func::CallOp collectiveCall(Operation *op) {
  auto c = mlir::dyn_cast<mlir::func::CallOp>(op);
  if (!c)
    return nullptr;
  auto f = mlir::SymbolTable::lookupNearestSymbolFrom<mlir::func::FuncOp>(
      c, c.getCalleeAttr());
  if (f && f->hasAttr("pia.collective"))
    return c;
  return nullptr;
}

bool holdsCollective(Operation *op) {
  bool found = false;
  op->walk([&](mlir::func::CallOp c) {
    if (collectiveCall(c))
      found = true;
  });
  return found;
}

// The buffer a view looks into.
Value rootOf(Value v) {
  while (auto view = v.getDefiningOp<mlir::ViewLikeOpInterface>())
    v = view.getViewSource();
  return v;
}

class Phases {
public:
  explicit Phases(scf::ForOp spread) : spread_(spread), b_(spread) {}

  LogicalResult run() {
    Location l = spread_.getLoc();
    auto fn = spread_->getParentOfType<mlir::func::FuncOp>();
    if (!fn)
      return spread_.emitError("a spread with collectives must be in a "
                               "function");
    entry_ = &fn.getBody().front();
    // What the body writes: a load from one of these cannot be computed
    // again in a later phase.
    spread_.getBody()->walk([&](Operation *op) {
      if (auto st = mlir::dyn_cast<memref::StoreOp>(op))
        written_.insert(rootOf(st.getMemRef()));
      else if (auto at = mlir::dyn_cast<memref::AtomicRMWOp>(op))
        written_.insert(rootOf(at.getMemref()));
      else if (auto cp = mlir::dyn_cast<memref::CopyOp>(op))
        written_.insert(rootOf(cp.getTarget()));
      else if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        for (Value a : call.getOperands())
          if (mlir::isa<mlir::MemRefType>(a.getType()))
            written_.insert(rootOf(a));
    });
    lo_ = spread_.getLowerBound();
    hi_ = spread_.getUpperBound();
    one_ = make<arith::ConstantIndexOp>(b_, l, 1);
    zero_ = make<arith::ConstantIndexOp>(b_, l, 0);
    // An empty range runs nothing, not even the lifted control flow, whose
    // conditions are computed as the iteration at lo would.
    Value any = make<arith::CmpIOp>(b_, l, arith::CmpIPredicate::slt, lo_, hi_);
    auto guard = make<scf::IfOp>(b_, l, mlir::TypeRange{}, any, false);
    b_.setInsertionPoint(guard.thenBlock()->getTerminator());
    // Each gathered slice is a buffer of the spread's count on the heap,
    // for the whole spread: a gather in a lifted loop fills it again at
    // each step.
    mlir::IRMapping outer;
    Value count = make<arith::SubIOp>(b_, l, hi_, lo_);
    llvm::SmallVector<Value> buffers;
    LogicalResult made = mlir::success();
    spread_.getBody()->walk([&](mlir::func::CallOp c) {
      if (!gatherCall(c))
        return;
      auto rt = mlir::dyn_cast<mlir::MemRefType>(c.getResult(0).getType());
      if (!rt || rt.getRank() != 1) {
        made = c.emitError("internal error: a gathered slice is not a "
                           "one-dimensional memref");
        return;
      }
      auto plain = mlir::MemRefType::get({mlir::ShapedType::kDynamic},
                                         rt.getElementType());
      Value buf = make<memref::AllocOp>(b_, l, plain, mlir::ValueRange{count});
      buffers.push_back(buf);
      Value view = buf;
      if (plain != rt)
        view = make<memref::CastOp>(b_, l, rt, buf);
      gathered_[c.getResult(0)] = buf;
      outer.map(c.getResult(0), view);
    });
    if (mlir::failed(made))
      return mlir::failure();
    if (mlir::failed(block(*spread_.getBody(), outer)))
      return mlir::failure();
    for (Value buf : buffers)
      make<memref::DeallocOp>(b_, l, buf);
    spread_.erase();
    return mlir::success();
  }

private:
  scf::ForOp spread_;
  mlir::OpBuilder b_; // outside the parallel loops
  mlir::Block *entry_ = nullptr;
  Value lo_, hi_, one_, zero_;
  llvm::DenseSet<Value> written_;
  // Each gather's result, and the buffer it fills.
  llvm::DenseMap<Value, Value> gathered_;

  bool inBody(Value v) {
    return spread_.getRegion().isAncestor(v.getParentRegion());
  }

  // Whether `op`, which a later phase needs, may run again there: it reads
  // nothing the spread writes and writes nothing.
  bool recomputable(Operation *op) {
    if (op->getNumRegions() > 0) {
      bool ok = true;
      op->walk([&](Operation *in) {
        if (in != op && in->getNumRegions() == 0 &&
            !in->hasTrait<mlir::OpTrait::IsTerminator>() && !recomputable(in))
          ok = false;
      });
      return ok;
    }
    if (auto ld = mlir::dyn_cast<memref::LoadOp>(op))
      return !written_.contains(rootOf(ld.getMemRef()));
    if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
      return llvm::none_of(call.getOperands(), [&](Value a) {
        return mlir::isa<mlir::MemRefType>(a.getType()) &&
               written_.contains(rootOf(a));
      });
    return mlir::isMemoryEffectFree(op);
  }

  // `v` where `m` maps the body's values, computing it again at `b` if it
  // was computed in another phase. The protocol check (ADR 0086, section
  // 2) lets only uniform values and the loop variable cross a collective.
  mlir::FailureOr<Value> remat(Value v, mlir::IRMapping &m,
                               mlir::OpBuilder &b) {
    if (Value got = m.lookupOrNull(v))
      return got;
    if (!inBody(v))
      return v;
    Operation *def = v.getDefiningOp();
    if (!def)
      return spread_.emitError("internal error: a block argument of a "
                               "spread's body crosses a collective");
    if (!recomputable(def))
      return def->emitError("internal error: this value crosses a "
                            "collective but cannot be computed again "
                            "(ADR 0086)");
    if (mlir::failed(cloneInto(def, m, b)))
      return mlir::failure();
    return m.lookup(v);
  }

  // Clones `op` at `b`, after whatever it uses from the body.
  LogicalResult cloneInto(Operation *op, mlir::IRMapping &m,
                          mlir::OpBuilder &b) {
    llvm::SetVector<Value> used;
    for (Value o : op->getOperands())
      used.insert(o);
    for (mlir::Region &r : op->getRegions())
      mlir::getUsedValuesDefinedAbove(r, used);
    for (Value u : used)
      if (!m.contains(u) && inBody(u) && mlir::failed(remat(u, m, b)))
        return mlir::failure();
    b.clone(*op, m);
    return mlir::success();
  }

  // A value for the lifted control flow: computed as the iteration at lo,
  // which a uniform value does not depend on.
  mlir::FailureOr<Value> control(Value v, const mlir::IRMapping &outer) {
    mlir::IRMapping ctl = outer;
    ctl.map(spread_.getInductionVar(), lo_);
    return remat(v, ctl, b_);
  }

  // One phase: `ops` as a parallel loop over the range, in which each
  // iteration also stores its argument to each of `gathers` in its cell.
  LogicalResult phase(llvm::ArrayRef<Operation *> ops,
                      llvm::ArrayRef<mlir::func::CallOp> gathers,
                      mlir::IRMapping &outer) {
    if (ops.empty() && gathers.empty())
      return mlir::success();
    Location l =
        !ops.empty() ? ops.front()->getLoc() : gathers.front().getLoc();
    auto par =
        make<scf::ParallelOp>(b_, l, mlir::ValueRange{lo_},
                              mlir::ValueRange{hi_}, mlir::ValueRange{one_});
    mlir::OpBuilder pb(par.getBody()->getTerminator());
    mlir::IRMapping m = outer;
    Value iv = par.getInductionVars()[0];
    m.map(spread_.getInductionVar(), iv);
    for (Operation *o : ops)
      if (mlir::failed(cloneInto(o, m, pb)))
        return mlir::failure();
    for (mlir::func::CallOp g : gathers) {
      mlir::FailureOr<Value> x = remat(g.getOperand(0), m, pb);
      if (mlir::failed(x))
        return mlir::failure();
      Value at = make<arith::SubIOp>(pb, g.getLoc(), iv, lo_);
      make<memref::StoreOp>(pb, g.getLoc(), *x,
                            gathered_.lookup(g.getResult(0)),
                            mlir::ValueRange{at});
    }
    return mlir::success();
  }

  // A collective's call, made once between two phases. What it does not
  // gather is uniform, so it is computed as the iteration at lo would.
  LogicalResult collective(mlir::func::CallOp c, mlir::IRMapping &outer) {
    llvm::SmallVector<Value> args;
    for (Value a : c.getOperands()) {
      if (Value got = outer.lookupOrNull(a)) {
        args.push_back(got);
        continue;
      }
      mlir::FailureOr<Value> v = control(a, outer);
      if (mlir::failed(v))
        return mlir::failure();
      args.push_back(*v);
    }
    auto call = make<mlir::func::CallOp>(b_, c.getLoc(), c.getCalleeAttr(),
                                         c.getResultTypes(), args);
    for (auto [from, to] : llvm::zip(c.getResults(), call.getResults()))
      outer.map(from, to);
    return mlir::success();
  }

  // The ops of `blk`, in phases, at b_, with `outer` mapping the values
  // computed outside the parallel loops.
  LogicalResult block(mlir::Block &blk, mlir::IRMapping outer) {
    llvm::SmallVector<Operation *> ops;
    llvm::SmallVector<mlir::func::CallOp> gathers;
    auto flush = [&]() {
      LogicalResult r = phase(ops, gathers, outer);
      ops.clear();
      gathers.clear();
      return r;
    };
    for (Operation &op : blk.without_terminator()) {
      if (auto g = gatherCall(&op)) {
        gathers.push_back(g);
        continue;
      }
      if (auto c = collectiveCall(&op)) {
        if (mlir::failed(flush()) || mlir::failed(collective(c, outer)))
          return mlir::failure();
        continue;
      }
      if (!holdsCollective(&op)) {
        ops.push_back(&op);
        continue;
      }
      if (mlir::failed(flush()))
        return mlir::failure();
      if (mlir::failed(lift(op, outer)))
        return mlir::failure();
    }
    return flush();
  }

  // An if or for that holds a collective, lifted out of the
  // parallel loops: every iteration takes the same way through it.
  LogicalResult lift(Operation &op, const mlir::IRMapping &outer) {
    Location l = op.getLoc();
    if (op.getNumResults() != 0)
      return op.emitError("code that holds a collective cannot compute a "
                          "value yet (ADR 0086)");
    if (auto ifOp = mlir::dyn_cast<scf::IfOp>(op)) {
      mlir::FailureOr<Value> c = control(ifOp.getCondition(), outer);
      if (mlir::failed(c))
        return mlir::failure();
      bool hasElse = !ifOp.getElseRegion().empty();
      auto nif = make<scf::IfOp>(b_, l, mlir::TypeRange{}, *c, hasElse);
      mlir::OpBuilder::InsertionGuard g(b_);
      b_.setInsertionPoint(nif.thenBlock()->getTerminator());
      if (mlir::failed(block(*ifOp.thenBlock(), outer)))
        return mlir::failure();
      if (!hasElse)
        return mlir::success();
      b_.setInsertionPoint(nif.elseBlock()->getTerminator());
      return block(*ifOp.elseBlock(), outer);
    }
    if (auto forOp = mlir::dyn_cast<scf::ForOp>(op)) {
      if (forOp.getNumRegionIterArgs() != 0)
        return op.emitError("a loop that holds a collective cannot carry a "
                            "value yet (ADR 0086)");
      mlir::FailureOr<Value> lb = control(forOp.getLowerBound(), outer);
      mlir::FailureOr<Value> ub = control(forOp.getUpperBound(), outer);
      mlir::FailureOr<Value> st = control(forOp.getStep(), outer);
      if (mlir::failed(lb) || mlir::failed(ub) || mlir::failed(st))
        return mlir::failure();
      auto nfor = make<scf::ForOp>(b_, l, *lb, *ub, *st);
      mlir::IRMapping inner = outer;
      inner.map(forOp.getInductionVar(), nfor.getInductionVar());
      mlir::OpBuilder::InsertionGuard g(b_);
      b_.setInsertionPoint(nfor.getBody()->getTerminator());
      return block(*forOp.getBody(), inner);
    }
    return op.emitError("internal error: a collective inside this op cannot "
                        "be split into phases (ADR 0086)");
  }
};

} // namespace

LogicalResult splitIntoPhases(scf::ForOp spread) {
  return Phases(spread).run();
}

void eraseCollectiveDeclarations(mlir::ModuleOp module) {
  for (auto f : llvm::make_early_inc_range(module.getOps<mlir::func::FuncOp>()))
    if (f.isExternal() && f.getSymName().starts_with(kGatherPrefix) &&
        mlir::SymbolTable::symbolKnownUseEmpty(f, module))
      f.erase();
}

} // namespace pia::codegen
