#include "codegen/SliceBuffers.h"

#include <vector>

#include "dialect/PiaDialect.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Func/Transforms/FuncConversions.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SCF/Transforms/Patterns.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/Transforms/DialectConversion.h"
#include "llvm/Config/llvm-config.h"

namespace pia::codegen {

using mlir::Type;
using mlir::Value;

namespace {

// Ops are created with the builder API of the LLVM in use.
template <typename Op, typename... Args>
Op make(mlir::OpBuilder &b, mlir::Location loc, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
  return Op::create(b, loc, std::forward<Args>(args)...);
#else
  return b.create<Op>(loc, std::forward<Args>(args)...);
#endif
}

// The slice type a buffer of slices holds, if it holds slices.
SliceType heldSlice(Type t) {
  if (auto s = mlir::dyn_cast<SliceType>(t))
    return mlir::dyn_cast<SliceType>(s.getElementType());
  if (auto a = mlir::dyn_cast<ArrayType>(t))
    return mlir::dyn_cast<SliceType>(a.getElementType());
  return {};
}

// A buffer of the same shape as `t` whose elements are indices: the
// addresses, or the lengths, of `t`'s elements.
Type indexBuffer(Type t) {
  Type index = mlir::IndexType::get(t.getContext());
  if (auto a = mlir::dyn_cast<ArrayType>(t))
    return ArrayType::get(t.getContext(), a.getLength(), index);
  return SliceType::get(t.getContext(), index);
}

class SplitTypes : public mlir::TypeConverter {
public:
  SplitTypes() {
    addConversion([](Type t) { return t; });
    auto split = [](Type t, llvm::SmallVectorImpl<Type> &out)
        -> std::optional<mlir::LogicalResult> {
      if (!heldSlice(t))
        return std::nullopt;
      out.push_back(indexBuffer(t));
      out.push_back(indexBuffer(t));
      return mlir::success();
    };
    addConversion([split](SliceType t, llvm::SmallVectorImpl<Type> &out) {
      return split(t, out);
    });
    addConversion([split](ArrayType t, llvm::SmallVectorImpl<Type> &out) {
      return split(t, out);
    });
  }
};

// `xs.[i]` rebuilds element i from its address and length.
struct LoadLowering : mlir::OpConversionPattern<LoadOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult
  matchAndRewrite(LoadOp op, OneToNOpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    if (!heldSlice(op.getBuffer().getType()))
      return mlir::failure();
    mlir::ValueRange buffers = adaptor.getBuffer();
    Value index = adaptor.getIndex().front();
    Type indexType = rw.getIndexType();
    Value addr = make<LoadOp>(rw, op.getLoc(), indexType, buffers[0], index);
    Value len = make<LoadOp>(rw, op.getLoc(), indexType, buffers[1], index);
    rw.replaceOp(op, make<AtAddressOp>(rw, op.getLoc(), op.getType(), addr, len)
                         .getResult());
    return mlir::success();
  }
};

// `xs.[i] <- s` records s's address and length. An element moved out keeps
// its address and gets length 0, as the verifier modelled it.
struct StoreLowering : mlir::OpConversionPattern<StoreOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult
  matchAndRewrite(StoreOp op, OneToNOpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    if (!heldSlice(op.getBuffer().getType()))
      return mlir::failure();
    mlir::ValueRange buffers = adaptor.getBuffer();
    Value index = adaptor.getIndex().front();
    Value slice = adaptor.getValue().front();
    Type indexType = rw.getIndexType();
    Value addr = make<AddressOp>(rw, op.getLoc(), indexType, slice);
    Value len = make<LenOp>(rw, op.getLoc(), indexType, slice);
    make<StoreOp>(rw, op.getLoc(), addr, buffers[0], index);
    make<StoreOp>(rw, op.getLoc(), len, buffers[1], index);
    rw.eraseOp(op);
    return mlir::success();
  }
};

struct LenLowering : mlir::OpConversionPattern<LenOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult
  matchAndRewrite(LenOp op, OneToNOpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    if (!heldSlice(op.getBuffer().getType()))
      return mlir::failure();
    rw.replaceOp(op, make<LenOp>(rw, op.getLoc(), rw.getIndexType(),
                                 adaptor.getBuffer()[0])
                         .getResult());
    return mlir::success();
  }
};

// A view of a buffer of slices is the same view of both buffers.
struct SliceLowering : mlir::OpConversionPattern<SliceOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult
  matchAndRewrite(SliceOp op, OneToNOpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    if (!heldSlice(op.getBuffer().getType()))
      return mlir::failure();
    Value lo = adaptor.getLo().front(), hi = adaptor.getHi().front();
    Type t = SliceType::get(rw.getContext(), rw.getIndexType());
    llvm::SmallVector<Value> views;
    for (Value b : adaptor.getBuffer())
      views.push_back(make<SliceOp>(rw, op.getLoc(), t, b, lo, hi));
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.push_back(std::move(views));
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

struct EmptyLowering : mlir::OpConversionPattern<EmptyOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult
  matchAndRewrite(EmptyOp op, OneToNOpAdaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    if (!heldSlice(op.getType()))
      return mlir::failure();
    Type t = SliceType::get(rw.getContext(), rw.getIndexType());
    llvm::SmallVector<Value> both{make<EmptyOp>(rw, op.getLoc(), t),
                                  make<EmptyOp>(rw, op.getLoc(), t)};
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.push_back(std::move(both));
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

bool usesSliceBuffers(mlir::ModuleOp module) {
  bool found = false;
  auto held = [](Type t) { return static_cast<bool>(heldSlice(t)); };
  module.walk([&](mlir::Operation *op) {
    if (llvm::any_of(op->getOperandTypes(), held) ||
        llvm::any_of(op->getResultTypes(), held))
      found = true;
    if (auto f = mlir::dyn_cast<mlir::func::FuncOp>(op))
      if (llvm::any_of(f.getFunctionType().getInputs(), held) ||
          llvm::any_of(f.getFunctionType().getResults(), held))
        found = true;
    return found ? mlir::WalkResult::interrupt() : mlir::WalkResult::advance();
  });
  return found;
}

} // namespace

mlir::LogicalResult splitSliceBuffers(mlir::ModuleOp module) {
  if (!usesSliceBuffers(module))
    return mlir::success();
  mlir::MLIRContext *ctx = module.getContext();

  // Each parameter's attributes and names, to rebuild them after the
  // signature conversion makes new block arguments.
  struct Param {
    Type type;
    mlir::DictionaryAttr attrs;
    mlir::Location loc;
  };
  std::vector<std::pair<mlir::func::FuncOp, std::vector<Param>>> params;
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    if (f.isExternal())
      continue;
    std::vector<Param> ps;
    for (mlir::BlockArgument a : f.getArguments())
      ps.push_back(
          {a.getType(), f.getArgAttrDict(a.getArgNumber()), a.getLoc()});
    params.emplace_back(f, std::move(ps));
  }

  SplitTypes types;
  mlir::ConversionTarget target(*ctx);
  target.markUnknownOpDynamicallyLegal(
      [&](mlir::Operation *op) { return types.isLegal(op); });
  target.addDynamicallyLegalOp<mlir::func::FuncOp>([&](mlir::func::FuncOp f) {
    return types.isSignatureLegal(f.getFunctionType()) &&
           types.isLegal(&f.getBody());
  });
  mlir::RewritePatternSet patterns(ctx);
  patterns.add<LoadLowering, StoreLowering, LenLowering, SliceLowering,
               EmptyLowering>(types, ctx);
  mlir::populateFunctionOpInterfaceTypeConversionPattern<mlir::func::FuncOp>(
      patterns, types);
  mlir::populateCallOpTypeConversionPattern(patterns, types);
  mlir::populateReturnOpTypeConversionPattern(patterns, types);
  mlir::scf::populateSCFStructuralTypeConversionsAndLegality(types, patterns,
                                                             target);
  if (mlir::failed(
          mlir::applyPartialConversion(module, target, std::move(patterns))))
    return mlir::failure();

  // A buffer of slices is now its addresses, then its lengths, which keep
  // its attributes. The lengths buffer shares the addresses' length, and
  // pia.length_of naming an earlier argument moves with it.
  auto lengthOf = PiaDialect::getLengthOfAttrName();
  auto i64 = mlir::IntegerType::get(ctx, 64);
  for (auto &[f, ps] : params) {
    std::vector<unsigned> first;
    unsigned next = 0;
    for (const Param &p : ps) {
      first.push_back(next);
      next += heldSlice(p.type) ? 2 : 1;
    }
    if (next == ps.size())
      continue;
    llvm::SmallVector<mlir::DictionaryAttr> attrs;
    for (auto [i, p] : llvm::enumerate(ps)) {
      mlir::NamedAttrList list(p.attrs);
      if (auto shared = list.get(lengthOf))
        list.set(
            lengthOf,
            mlir::IntegerAttr::get(
                i64, first[mlir::cast<mlir::IntegerAttr>(shared).getInt()]));
      attrs.push_back(list.getDictionary(ctx));
      if (!heldSlice(p.type))
        continue;
      // The lengths share the addresses' length, or what that shares.
      if (mlir::isa<SliceType>(p.type) && !list.get(lengthOf))
        list.set(lengthOf, mlir::IntegerAttr::get(i64, first[i]));
      attrs.push_back(list.getDictionary(ctx));
      f.getArgument(first[i] + 1).setLoc(p.loc);
    }
    f.setAllArgAttrs(attrs);
  }
  return mlir::success();
}

} // namespace pia::codegen
