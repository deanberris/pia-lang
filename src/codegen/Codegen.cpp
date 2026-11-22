// Codegen v0 (milestone M6). docs/codegen.md describes the lowering.

#include "codegen/Codegen.h"

#include <algorithm>
#include <cctype>
#include <optional>
#include <set>
#include <type_traits>
#include <string>
#include <utility>
#include <vector>

#include "dialect/ContractDialect.h"
#include "dialect/PiaDialect.h"
#include "llvm/ADT/APInt.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Triple.h"
#include "mlir/Conversion/ArithToLLVM/ArithToLLVM.h"
#include "mlir/Conversion/ControlFlowToLLVM/ControlFlowToLLVM.h"
#include "mlir/Conversion/FuncToLLVM/ConvertFuncToLLVMPass.h"
#include "mlir/Conversion/IndexToLLVM/IndexToLLVM.h"
#include "mlir/Conversion/MemRefToLLVM/MemRefToLLVM.h"
#include "mlir/Conversion/ReconcileUnrealizedCasts/ReconcileUnrealizedCasts.h"
#include "mlir/Conversion/SCFToControlFlow/SCFToControlFlow.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlow.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Func/Transforms/FuncConversions.h"
#include "mlir/Dialect/Index/IR/IndexDialect.h"
#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SCF/Transforms/Patterns.h"
#include "mlir/ExecutionEngine/OptUtils.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Target/LLVMIR/Dialect/Builtin/BuiltinToLLVMIRTranslation.h"
#include "mlir/Target/LLVMIR/Dialect/LLVMIR/LLVMToLLVMIRTranslation.h"
#include "mlir/Target/LLVMIR/Export.h"
#include "mlir/Transforms/DialectConversion.h"
#include "mlir/Transforms/Passes.h"

namespace pia::codegen {

using llvm::APInt;
using mlir::Location;
using mlir::LogicalResult;
using mlir::OpBuilder;
using mlir::Type;
using mlir::Value;

namespace {

template <typename OpTy, typename... Args>
OpTy make(OpBuilder &b, Location loc, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
  return OpTy::create(b, loc, std::forward<Args>(args)...);
#else
  return b.create<OpTy>(loc, std::forward<Args>(args)...);
#endif
}

//===----------------------------------------------------------------------===//
// Ranges and machine representations
//===----------------------------------------------------------------------===//

// Exact ranges are computed at a width no product of two Pia values can
// leave: both factors lie in [-2^63, 2^64 - 1].
constexpr unsigned kExact = 256;

struct Range {
  APInt lo, hi;  // kExact bits, signed
};

Range rangeOf(IntType t) {
  return {t.getLo().sextOrTrunc(kExact), t.getHi().sextOrTrunc(kExact)};
}

Range join(const Range &a, const Range &b) {
  return {a.lo.slt(b.lo) ? a.lo : b.lo, a.hi.sgt(b.hi) ? a.hi : b.hi};
}

// How a range is held in a machine integer.
struct Repr {
  unsigned width;
  bool isSigned;
};

unsigned roundWidth(unsigned bits) {
  for (unsigned w : {8u, 16u, 32u, 64u, 128u})
    if (bits <= w) return w;
  return (bits + 63) / 64 * 64;
}

Repr reprOf(const Range &r) {
  if (!r.lo.isNegative())
    return {roundWidth(std::max(1u, r.hi.getActiveBits())), false};
  return {roundWidth(std::max(r.lo.getSignificantBits(),
                              r.hi.getSignificantBits())),
          true};
}

Repr reprOf(IntType t) { return reprOf(rangeOf(t)); }

// A range type covers every value of a machine integer of its width, so
// wrapping into it is truncation.
bool isFullWidth(IntType t) {
  Range r = rangeOf(t);
  Repr repr = reprOf(r);
  if (repr.isSigned)
    return r.lo == APInt::getSignedMinValue(repr.width).sext(kExact) &&
           r.hi == APInt::getSignedMaxValue(repr.width).sext(kExact);
  return r.lo.isZero() && r.hi == APInt::getMaxValue(repr.width).zext(kExact);
}

enum class Arith { Add, Sub, Mul, Div, Rem, BAnd, BOr, BXor, Shl, Shr };

// The exact range of `a op b` for operands in the given ranges. Division
// and remainder are bounded by the operands' magnitudes. A shift amount is
// proved below the left operand's width, so at most `maxShift`.
Range exactRange(Arith kind, const Range &a, const Range &b,
                 unsigned maxShift = 0) {
  auto minOf = [](std::initializer_list<APInt> xs) {
    APInt m = *xs.begin();
    for (const APInt &x : xs)
      if (x.slt(m)) m = x;
    return m;
  };
  auto maxOf = [](std::initializer_list<APInt> xs) {
    APInt m = *xs.begin();
    for (const APInt &x : xs)
      if (x.sgt(m)) m = x;
    return m;
  };
  auto mag = [&](const Range &r) { return maxOf({r.lo.abs(), r.hi.abs()}); };
  switch (kind) {
    case Arith::Add:
      return {a.lo + b.lo, a.hi + b.hi};
    case Arith::Sub:
      return {a.lo - b.hi, a.hi - b.lo};
    case Arith::Mul: {
      APInt p1 = a.lo * b.lo, p2 = a.lo * b.hi, p3 = a.hi * b.lo,
            p4 = a.hi * b.hi;
      return {minOf({p1, p2, p3, p4}), maxOf({p1, p2, p3, p4})};
    }
    case Arith::Div: {
      APInt m = mag(a);
      return {-m, m};
    }
    case Arith::Rem: {
      APInt m = maxOf({mag(a), mag(b)});
      return {-m, m};
    }
    case Arith::BAnd:
    case Arith::BOr:
    case Arith::BXor: {
      // Both operands fit k signed bits, and so does the result.
      unsigned k = std::max({a.lo.getSignificantBits(),
                             a.hi.getSignificantBits(),
                             b.lo.getSignificantBits(),
                             b.hi.getSignificantBits()});
      bool nonneg = !a.lo.isNegative() && !b.lo.isNegative();
      APInt hi = APInt::getSignedMaxValue(k).sext(kExact);
      APInt lo = nonneg ? APInt(kExact, 0)
                        : APInt::getSignedMinValue(k).sext(kExact);
      return {lo, hi};
    }
    case Arith::Shl:
      return {minOf({a.lo, a.lo.shl(maxShift)}),
              maxOf({a.hi, a.hi.shl(maxShift)})};
    case Arith::Shr: {
      APInt zero(kExact, 0);
      return {minOf({a.lo, zero}), maxOf({a.hi, zero})};
    }
  }
  return a;
}

// Sign- or zero-extends, or truncates, `v` to `width` bits.
Value resize(OpBuilder &b, Location loc, Value v, bool isSigned,
             unsigned width) {
  unsigned from = v.getType().getIntOrFloatBitWidth();
  if (from == width) return v;
  Type to = b.getIntegerType(width);
  if (from > width) return make<mlir::arith::TruncIOp>(b, loc, to, v);
  if (isSigned) return make<mlir::arith::ExtSIOp>(b, loc, to, v);
  return make<mlir::arith::ExtUIOp>(b, loc, to, v);
}

Value constant(OpBuilder &b, Location loc, const APInt &value,
               unsigned width) {
  Type t = b.getIntegerType(width);
  return make<mlir::arith::ConstantOp>(
      b, loc, t, b.getIntegerAttr(t, value.sextOrTrunc(width)));
}

// Brings an exact result `r`, held as `repr`, into the result type under
// `mode`, and returns it in the result type's representation.
Value finish(OpBuilder &b, Location loc, Value r, Repr repr, IntType result,
             OverflowMode mode) {
  Range rr = rangeOf(result);
  Repr out = reprOf(rr);
  switch (mode) {
    case OverflowMode::proof:
      // The verifier proved the exact value lies in the result type.
      break;
    case OverflowMode::saturate: {
      Value lo = constant(b, loc, rr.lo, repr.width);
      Value hi = constant(b, loc, rr.hi, repr.width);
      if (repr.isSigned) {
        r = make<mlir::arith::MaxSIOp>(b, loc, r, lo);
        r = make<mlir::arith::MinSIOp>(b, loc, r, hi);
      } else {
        r = make<mlir::arith::MaxUIOp>(b, loc, r, lo);
        r = make<mlir::arith::MinUIOp>(b, loc, r, hi);
      }
      break;
    }
    case OverflowMode::trap: {
      using mlir::arith::CmpIPredicate;
      Value lo = constant(b, loc, rr.lo, repr.width);
      Value hi = constant(b, loc, rr.hi, repr.width);
      Value below = make<mlir::arith::CmpIOp>(
          b, loc, repr.isSigned ? CmpIPredicate::slt : CmpIPredicate::ult, r,
          lo);
      Value above = make<mlir::arith::CmpIOp>(
          b, loc, repr.isSigned ? CmpIPredicate::sgt : CmpIPredicate::ugt, r,
          hi);
      Value outside = make<mlir::arith::OrIOp>(b, loc, below, above);
      auto ifOp = make<mlir::scf::IfOp>(b, loc, outside, /*withElse=*/false);
      OpBuilder::InsertionGuard guard(b);
      b.setInsertionPoint(ifOp.thenBlock()->getTerminator());
      make<mlir::LLVM::Trap>(b, loc);
      break;
    }
    case OverflowMode::wrap: {
      if (isFullWidth(result)) break;  // truncation below wraps
      // lo + ((r - lo) mod size), with a non-negative mod, computed with
      // room for r - lo.
      unsigned w = repr.width * 2;
      Value x = resize(b, loc, r, repr.isSigned, w);
      APInt size = rr.hi - rr.lo + 1;
      Value lo = constant(b, loc, rr.lo, w);
      Value n = constant(b, loc, size, w);
      Value zero = constant(b, loc, APInt(kExact, 0), w);
      Value d = make<mlir::arith::SubIOp>(b, loc, x, lo);
      Value m = make<mlir::arith::RemSIOp>(b, loc, d, n);
      Value neg = make<mlir::arith::CmpIOp>(
          b, loc, mlir::arith::CmpIPredicate::slt, m, zero);
      Value fixed = make<mlir::arith::AddIOp>(b, loc, m, n);
      m = make<mlir::arith::SelectOp>(b, loc, neg, fixed, m);
      r = make<mlir::arith::AddIOp>(b, loc, m, lo);
      repr = {w, true};
      break;
    }
  }
  return resize(b, loc, r, repr.isSigned, out.width);
}

//===----------------------------------------------------------------------===//
// Type conversion
//===----------------------------------------------------------------------===//

// int, real and a theory's sort: values only the verifier computes with.
bool isSpecOnly(Type t) {
  return mlir::isa<UnboundedIntType, RealType, SortType>(t);
}

class CoreTypes : public mlir::TypeConverter {
 public:
  CoreTypes() {
    addConversion([](Type t) { return t; });
    addConversion([](IntType t) -> Type {
      return mlir::IntegerType::get(t.getContext(), reprOf(t).width);
    });
    // Spec-only state is erased (ADR 0041): what is left of it is a bit
    // that nothing reads, and LLVM drops it.
    addConversion([](Type t) -> std::optional<Type> {
      if (!isSpecOnly(t)) return std::nullopt;
      return mlir::IntegerType::get(t.getContext(), 1);
    });
    addConversion([this](ArrayType t) -> std::optional<Type> {
      Type elem = element(t.getElementType());
      if (!elem) return std::nullopt;
      return mlir::MemRefType::get({static_cast<int64_t>(t.getLength())},
                                   elem);
    });
    // A slice may start part way into its storage (`xs.[a .. b]`), so its
    // offset is dynamic. The descriptor is the same as an identity one's.
    addConversion([this](SliceType t) -> std::optional<Type> {
      Type elem = element(t.getElementType());
      if (!elem) return std::nullopt;
      auto layout = mlir::StridedLayoutAttr::get(
          t.getContext(), mlir::ShapedType::kDynamic, {1});
      return mlir::MemRefType::get({mlir::ShapedType::kDynamic}, elem, layout);
    });
    auto cast = [](OpBuilder &b, Type t, mlir::ValueRange in,
                   Location loc) -> Value {
      return make<mlir::UnrealizedConversionCastOp>(b, loc, t, in)
          .getResult(0);
    };
    addSourceMaterialization(cast);
    addTargetMaterialization(cast);
  }

 private:
  // Buffers hold scalars only in v0.
  Type element(Type t) {
    Type c = convertType(t);
    if (c && mlir::isa<mlir::IntegerType, mlir::IndexType>(c)) return c;
    return {};
  }
};

//===----------------------------------------------------------------------===//
// Patterns
//===----------------------------------------------------------------------===//

struct ConstantLowering : mlir::OpConversionPattern<ConstantOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ConstantOp op, OpAdaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    auto t = mlir::cast<IntType>(op.getResult().getType());
    rw.replaceOp(op, constant(rw, op.getLoc(), op.getValue(),
                              reprOf(t).width));
    return mlir::success();
  }
};

template <typename OpTy, Arith kind>
struct ArithLowering : mlir::OpConversionPattern<OpTy> {
  using mlir::OpConversionPattern<OpTy>::OpConversionPattern;
  using OpAdaptor = typename OpTy::Adaptor;
  LogicalResult matchAndRewrite(
      OpTy op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto lt = mlir::cast<IntType>(op.getLhs().getType());
    auto rt = mlir::cast<IntType>(op.getRhs().getType());
    auto res = mlir::cast<IntType>(op.getResult().getType());
    OverflowMode mode = op.getOverflow();
    Range ra = rangeOf(lt), rb = rangeOf(rt);
    // The computation width holds both operands, the result type and,
    // unless the result was proved to fit, the exact result.
    Range span = join(join(ra, rb), rangeOf(res));
    if (mode != OverflowMode::proof)
      span = join(span, exactRange(kind, ra, rb, lt.getStorageWidth() - 1));
    Repr c = reprOf(span);
    Value a = resize(rw, loc, adaptor.getLhs(), reprOf(lt).isSigned, c.width);
    Value b = resize(rw, loc, adaptor.getRhs(), reprOf(rt).isSigned, c.width);
    Value r;
    switch (kind) {
      case Arith::Add:
        r = make<mlir::arith::AddIOp>(rw, loc, a, b);
        break;
      case Arith::Sub:
        r = make<mlir::arith::SubIOp>(rw, loc, a, b);
        break;
      case Arith::Mul:
        r = make<mlir::arith::MulIOp>(rw, loc, a, b);
        break;
      case Arith::Div:
        r = c.isSigned ? Value(make<mlir::arith::DivSIOp>(rw, loc, a, b))
                       : Value(make<mlir::arith::DivUIOp>(rw, loc, a, b));
        break;
      case Arith::Rem:
        r = c.isSigned ? Value(make<mlir::arith::RemSIOp>(rw, loc, a, b))
                       : Value(make<mlir::arith::RemUIOp>(rw, loc, a, b));
        break;
      // Extended to the computation width, the operands' bits agree with
      // the exact integers', so these are exact (Pia.td).
      case Arith::BAnd:
        r = make<mlir::arith::AndIOp>(rw, loc, a, b);
        break;
      case Arith::BOr:
        r = make<mlir::arith::OrIOp>(rw, loc, a, b);
        break;
      case Arith::BXor:
        r = make<mlir::arith::XOrIOp>(rw, loc, a, b);
        break;
      case Arith::Shl:
        r = make<mlir::arith::ShLIOp>(rw, loc, a, b);
        break;
      case Arith::Shr:
        r = c.isSigned ? Value(make<mlir::arith::ShRSIOp>(rw, loc, a, b))
                       : Value(make<mlir::arith::ShRUIOp>(rw, loc, a, b));
        break;
    }
    rw.replaceOp(op, finish(rw, loc, r, c, res, mode));
    return mlir::success();
  }
};

// `clz`, `ctz`, `popcount` and `bswap` on the w-bit machine integer of an
// unsigned operand, through LLVM's intrinsics, which arm64 has instructions
// for (clz, rbit + clz, cnt, rev). A zero operand counts w (no poison).
template <typename OpTy>
struct BitLowering : mlir::OpConversionPattern<OpTy> {
  using mlir::OpConversionPattern<OpTy>::OpConversionPattern;
  using OpAdaptor = typename OpTy::Adaptor;
  LogicalResult matchAndRewrite(
      OpTy op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto in = mlir::cast<IntType>(op.getInput().getType());
    auto res = mlir::cast<IntType>(op.getResult().getType());
    unsigned w = in.getStorageWidth();
    Value x = resize(rw, loc, adaptor.getInput(), false, w);
    Type t = rw.getIntegerType(w);
    Value r;
    if constexpr (std::is_same_v<OpTy, ClzOp>)
      r = make<mlir::LLVM::CountLeadingZerosOp>(rw, loc, t, x, false);
    else if constexpr (std::is_same_v<OpTy, CtzOp>)
      r = make<mlir::LLVM::CountTrailingZerosOp>(rw, loc, t, x, false);
    else if constexpr (std::is_same_v<OpTy, PopcountOp>)
      r = make<mlir::LLVM::CtPopOp>(rw, loc, t, x);
    else
      r = w == 8 ? x : Value(make<mlir::LLVM::ByteSwapOp>(rw, loc, t, x));
    rw.replaceOp(op, resize(rw, loc, r, false, reprOf(res).width));
    return mlir::success();
  }
};

// `rotl x n` and `rotr x n` are funnel shifts of x with itself, at w bits.
// The amount is proved to be below w.
template <typename OpTy>
struct RotateLowering : mlir::OpConversionPattern<OpTy> {
  using mlir::OpConversionPattern<OpTy>::OpConversionPattern;
  using OpAdaptor = typename OpTy::Adaptor;
  LogicalResult matchAndRewrite(
      OpTy op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto in = mlir::cast<IntType>(op.getValue().getType());
    auto at = mlir::cast<IntType>(op.getAmount().getType());
    auto res = mlir::cast<IntType>(op.getResult().getType());
    unsigned w = in.getStorageWidth();
    Value x = resize(rw, loc, adaptor.getValue(), false, w);
    Value n = resize(rw, loc, adaptor.getAmount(), reprOf(at).isSigned, w);
    Type t = rw.getIntegerType(w);
    Value r;
    if constexpr (std::is_same_v<OpTy, RotlOp>)
      r = make<mlir::LLVM::FshlOp>(rw, loc, t, x, x, n);
    else
      r = make<mlir::LLVM::FshrOp>(rw, loc, t, x, x, n);
    rw.replaceOp(op, resize(rw, loc, r, false, reprOf(res).width));
    return mlir::success();
  }
};

struct ConvertLowering : mlir::OpConversionPattern<ConvertOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ConvertOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    auto in = mlir::cast<IntType>(op.getInput().getType());
    auto res = mlir::cast<IntType>(op.getResult().getType());
    Repr c = reprOf(join(rangeOf(in), rangeOf(res)));
    Value v = resize(rw, op.getLoc(), adaptor.getInput(), reprOf(in).isSigned,
                     c.width);
    rw.replaceOp(op, finish(rw, op.getLoc(), v, c, res, op.getOverflow()));
    return mlir::success();
  }
};

struct CmpLowering : mlir::OpConversionPattern<CmpOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      CmpOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    using mlir::arith::CmpIPredicate;
    Location loc = op.getLoc();
    auto lt = mlir::cast<IntType>(op.getLhs().getType());
    auto rt = mlir::cast<IntType>(op.getRhs().getType());
    Repr c = reprOf(join(rangeOf(lt), rangeOf(rt)));
    Value a = resize(rw, loc, adaptor.getLhs(), reprOf(lt).isSigned, c.width);
    Value b = resize(rw, loc, adaptor.getRhs(), reprOf(rt).isSigned, c.width);
    CmpIPredicate p = CmpIPredicate::eq;
    switch (op.getPredicate()) {
      case CmpPredicate::eq: p = CmpIPredicate::eq; break;
      case CmpPredicate::ne: p = CmpIPredicate::ne; break;
      case CmpPredicate::lt:
        p = c.isSigned ? CmpIPredicate::slt : CmpIPredicate::ult;
        break;
      case CmpPredicate::le:
        p = c.isSigned ? CmpIPredicate::sle : CmpIPredicate::ule;
        break;
      case CmpPredicate::gt:
        p = c.isSigned ? CmpIPredicate::sgt : CmpIPredicate::ugt;
        break;
      case CmpPredicate::ge:
        p = c.isSigned ? CmpIPredicate::sge : CmpIPredicate::uge;
        break;
    }
    rw.replaceOpWithNewOp<mlir::arith::CmpIOp>(op, p, a, b);
    return mlir::success();
  }
};

struct ToIndexLowering : mlir::OpConversionPattern<ToIndexOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ToIndexOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Type index = rw.getIndexType();
    if (reprOf(mlir::cast<IntType>(op.getInput().getType())).isSigned)
      rw.replaceOpWithNewOp<mlir::arith::IndexCastOp>(op, index,
                                                      adaptor.getInput());
    else
      rw.replaceOpWithNewOp<mlir::arith::IndexCastUIOp>(op, index,
                                                        adaptor.getInput());
    return mlir::success();
  }
};

struct FromIndexLowering : mlir::OpConversionPattern<FromIndexOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      FromIndexOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    // The index is proved to lie in the result type, so it is non-negative.
    Type t = getTypeConverter()->convertType(op.getResult().getType());
    rw.replaceOpWithNewOp<mlir::arith::IndexCastUIOp>(op, t,
                                                      adaptor.getInput());
    return mlir::success();
  }
};

struct LenLowering : mlir::OpConversionPattern<LenOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      LenOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    if (auto array = mlir::dyn_cast<ArrayType>(op.getBuffer().getType())) {
      rw.replaceOpWithNewOp<mlir::arith::ConstantIndexOp>(
          op, static_cast<int64_t>(array.getLength()));
      return mlir::success();
    }
    rw.replaceOpWithNewOp<mlir::memref::DimOp>(op, adaptor.getBuffer(), 0);
    return mlir::success();
  }
};

struct LoadLowering : mlir::OpConversionPattern<LoadOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      LoadOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    rw.replaceOpWithNewOp<mlir::memref::LoadOp>(
        op, adaptor.getBuffer(), mlir::ValueRange{adaptor.getIndex()});
    return mlir::success();
  }
};

// Constant data: a private constant memref.global, which LLVM places in
// read-only data, shared by every use of the same constant.
struct ConstArrayLowering : mlir::OpConversionPattern<ConstArrayOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ConstArrayOp op, OpAdaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    if (!type) return mlir::failure();
    auto elem = mlir::cast<mlir::IntegerType>(type.getElementType());
    llvm::SmallVector<APInt> values;
    for (mlir::Attribute a : op.getValues())
      values.push_back(
          mlir::cast<mlir::IntegerAttr>(a).getValue().sextOrTrunc(
              elem.getWidth()));
    auto init = mlir::DenseIntElementsAttr::get(
        mlir::RankedTensorType::get({type.getDimSize(0)}, elem), values);

    auto module = op->getParentOfType<mlir::ModuleOp>();
    std::string base = "__pia_const_" +
                       (op.getLabel() ? op.getLabel()->str() : std::string("lit"));
    // Reuse a global with this name and these values; otherwise pick a
    // fresh name.
    std::string name = base;
    for (unsigned n = 1;; ++n) {
      auto g = module.lookupSymbol<mlir::memref::GlobalOp>(name);
      if (!g) {
        mlir::OpBuilder::InsertionGuard guard(rw);
        rw.setInsertionPointToStart(module.getBody());
        make<mlir::memref::GlobalOp>(
            rw, loc, name, rw.getStringAttr("private"), type, init,
            /*constant=*/true, /*alignment=*/mlir::IntegerAttr());
        break;
      }
      if (g.getType() == type && g.getInitialValueAttr() == init) break;
      name = base + "_" + std::to_string(n);
    }
    rw.replaceOpWithNewOp<mlir::memref::GetGlobalOp>(op, type, name);
    return mlir::success();
  }
};

// `xs.[lo .. hi]`: the same storage, from the buffer's offset plus lo, with
// hi - lo elements.
struct SliceLowering : mlir::OpConversionPattern<SliceOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      SliceOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    if (!type) return mlir::failure();
    Value src = adaptor.getBuffer();
    auto meta = make<mlir::memref::ExtractStridedMetadataOp>(rw, loc, src);
    Value offset = make<mlir::arith::AddIOp>(rw, loc, meta.getOffset(),
                                             adaptor.getLo());
    Value size =
        make<mlir::arith::SubIOp>(rw, loc, adaptor.getHi(), adaptor.getLo());
    rw.replaceOpWithNewOp<mlir::memref::ReinterpretCastOp>(
        op, type, src, mlir::OpFoldResult(offset),
        llvm::ArrayRef<mlir::OpFoldResult>{size},
        llvm::ArrayRef<mlir::OpFoldResult>{rw.getIndexAttr(1)});
    return mlir::success();
  }
};

// An empty slice, the unused payload of a variant: zero elements of no
// storage in particular.
struct EmptyLowering : mlir::OpConversionPattern<EmptyOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      EmptyOp op, OpAdaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    if (!type) return mlir::failure();
    auto none = mlir::MemRefType::get({0}, type.getElementType());
    Value storage = make<mlir::memref::AllocaOp>(rw, op.getLoc(), none);
    rw.replaceOpWithNewOp<mlir::memref::CastOp>(op, type, storage);
    return mlir::success();
  }
};

// A `with_arena`'s memory (#70): stack storage made once on entry to the
// function, so a `with_arena` in a loop does not grow the stack, and
// zeroed each time the `with_arena` is entered.
struct ErasedLowering : mlir::OpConversionPattern<ErasedOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ErasedOp op, OpAdaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Type t = getTypeConverter()->convertType(op.getType());
    if (!t) return mlir::failure();
    rw.replaceOpWithNewOp<mlir::arith::ConstantOp>(op, t, rw.getZeroAttr(t));
    return mlir::success();
  }
};

struct RegionLowering : mlir::OpConversionPattern<RegionOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      RegionOp op, OpAdaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    if (!type) return mlir::failure();
    auto elem = mlir::dyn_cast<mlir::IntegerType>(type.getElementType());
    auto fn = op->getParentOfType<mlir::func::FuncOp>();
    if (!elem || !fn) return mlir::failure();
    Value storage;
    {
      mlir::OpBuilder::InsertionGuard guard(rw);
      rw.setInsertionPointToStart(&fn.getBody().front());
      storage = make<mlir::memref::AllocaOp>(rw, loc, type);
    }
    Value zero = make<mlir::arith::ConstantOp>(rw, loc, elem,
                                               rw.getIntegerAttr(elem, 0));
    Value lo = make<mlir::arith::ConstantIndexOp>(rw, loc, 0);
    Value hi = make<mlir::arith::ConstantIndexOp>(
        rw, loc, static_cast<int64_t>(op.getType().getLength()));
    Value one = make<mlir::arith::ConstantIndexOp>(rw, loc, 1);
    auto loop = make<mlir::scf::ForOp>(rw, loc, lo, hi, one);
    {
      mlir::OpBuilder::InsertionGuard guard(rw);
      rw.setInsertionPoint(loop.getBody()->getTerminator());
      make<mlir::memref::StoreOp>(rw, loc, zero, storage,
                                  mlir::ValueRange{loop.getInductionVar()});
    }
    rw.replaceOp(op, storage);
    return mlir::success();
  }
};

// `unsafe view addr n`: a memref descriptor over foreign memory, built
// as the LLVM struct a memref lowers to, so its uses lower as usual.
struct ViewLowering : mlir::OpConversionPattern<ViewOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ViewOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    Value addr = adaptor.getAddress();
    auto i64 = rw.getI64Type();
    if (!type || addr.getType() != i64) return mlir::failure();
    auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
    auto dims = mlir::LLVM::LLVMArrayType::get(i64, 1);
    auto desc = mlir::LLVM::LLVMStructType::getLiteral(
        rw.getContext(), {ptr, ptr, i64, dims, dims});
    Value p = make<mlir::LLVM::IntToPtrOp>(rw, loc, ptr, addr);
    Value n = make<mlir::arith::IndexCastOp>(rw, loc, i64, adaptor.getLength());
    Value zero = make<mlir::LLVM::ConstantOp>(rw, loc, i64,
                                              rw.getI64IntegerAttr(0));
    Value one = make<mlir::LLVM::ConstantOp>(rw, loc, i64,
                                             rw.getI64IntegerAttr(1));
    Value d = make<mlir::LLVM::UndefOp>(rw, loc, desc);
    auto insert = [&](Value v, llvm::ArrayRef<int64_t> at) {
      d = make<mlir::LLVM::InsertValueOp>(rw, loc, d, v, at);
    };
    insert(p, {0});
    insert(p, {1});
    insert(zero, {2});
    insert(n, {3, 0});
    insert(one, {4, 0});
    rw.replaceOpWithNewOp<mlir::UnrealizedConversionCastOp>(op, type, d);
    return mlir::success();
  }
};

// `abort ()`: proved unreachable; if reached anyway, it traps. A result it
// stands for is never used, so it is zero.
struct AbortLowering : mlir::OpConversionPattern<AbortOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      AbortOp op, OpAdaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    llvm::SmallVector<Value> results;
    for (Type t : op.getResultTypes()) {
      auto i = mlir::dyn_cast_or_null<mlir::IntegerType>(
          getTypeConverter()->convertType(t));
      if (!i) return mlir::failure();
      results.push_back(make<mlir::arith::ConstantOp>(
          rw, loc, i, rw.getIntegerAttr(i, 0)));
    }
    make<mlir::LLVM::Trap>(rw, loc);
    rw.replaceOp(op, results);
    return mlir::success();
  }
};

// `pia.foreign`: a call of the C function, which the pre-pass in
// lowerToCore declared. A buffer is passed as a pointer to its first
// element (#55).
struct ForeignLowering : mlir::OpConversionPattern<ForeignOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      ForeignOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
    llvm::SmallVector<Value> args;
    for (Value v : adaptor.getArgs()) {
      if (auto m = mlir::dyn_cast<mlir::MemRefType>(v.getType())) {
        auto meta = make<mlir::memref::ExtractStridedMetadataOp>(rw, loc, v);
        Value base = make<mlir::memref::ExtractAlignedPointerAsIndexOp>(
            rw, loc, v);
        Value addr = make<mlir::arith::IndexCastOp>(rw, loc, rw.getI64Type(),
                                                    base);
        Value p = make<mlir::LLVM::IntToPtrOp>(rw, loc, ptr, addr);
        Value off = make<mlir::arith::IndexCastOp>(rw, loc, rw.getI64Type(),
                                                   meta.getOffset());
        v = make<mlir::LLVM::GEPOp>(
            rw, loc, ptr, m.getElementType(), p,
            llvm::ArrayRef<mlir::LLVM::GEPArg>{mlir::LLVM::GEPArg(off)});
      }
      args.push_back(v);
    }
    llvm::SmallVector<Type> results;
    for (Type t : op.getResultTypes())
      results.push_back(getTypeConverter()->convertType(t));
    rw.replaceOpWithNewOp<mlir::func::CallOp>(op, op.getSymbol(), results,
                                              args);
    return mlir::success();
  }
};

struct StoreLowering : mlir::OpConversionPattern<StoreOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      StoreOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    rw.replaceOpWithNewOp<mlir::memref::StoreOp>(
        op, adaptor.getValue(), adaptor.getBuffer(),
        mlir::ValueRange{adaptor.getIndex()});
    return mlir::success();
  }
};

constexpr llvm::StringLiteral kSigned = "pia.signed";
constexpr llvm::StringLiteral kErased = "pia.erased";
constexpr llvm::StringLiteral kInternalPrefix = "__pia_";

bool isContractStatement(mlir::Operation *op) {
  return mlir::isa<contract::RequiresOp, contract::EnsuresOp,
                   contract::InvariantOp, contract::DecreasesOp,
                   contract::AssertOp, contract::AssumeOp,
                   contract::ObligationOp>(op);
}

// An op whose results are unused and that has no effect but reading.
bool isDead(mlir::Operation *op) {
  if (op->getNumResults() == 0 || !op->use_empty()) return false;
  if (op->hasTrait<mlir::OpTrait::IsTerminator>()) return false;
  if (mlir::isa<contract::ContractDialect>(op->getDialect())) return true;
  if (mlir::isa<LoadOp>(op)) return true;
  return mlir::isMemoryEffectFree(op);
}

}  // namespace

//===----------------------------------------------------------------------===//
// Stages
//===----------------------------------------------------------------------===//

void loadDialects(mlir::MLIRContext &ctx) {
  ctx.loadDialect<mlir::arith::ArithDialect, mlir::cf::ControlFlowDialect,
                  mlir::func::FuncDialect, mlir::index::IndexDialect,
                  mlir::LLVM::LLVMDialect, mlir::memref::MemRefDialect,
                  mlir::scf::SCFDialect>();
  mlir::registerBuiltinDialectTranslation(ctx);
  mlir::registerLLVMDialectTranslation(ctx);
}

namespace {
std::string cName(llvm::StringRef name);

// The symbol under which a module's function keeps its Pia calling
// convention, for importers to call (ADR 0039): `__pia$Image$Png$decode`.
std::string linkSymbol(llvm::StringRef path, llvm::StringRef name) {
  std::string p = path.str();
  std::replace(p.begin(), p.end(), '.', '$');
  return "__pia$" + p + "$" + cName(name);
}
}  // namespace

void eraseContracts(mlir::ModuleOp module) {
  // An imported function's body is its interface's contract, for the
  // verifier. The code is in its module's object file, so what remains is
  // a declaration of the module's link symbol (ADR 0039).
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    auto from = f->getAttrOfType<mlir::StringAttr>(PiaDialect::getImportAttrName());
    if (!from) continue;
    llvm::StringRef local = f.getSymName();
    local.consume_front(from.getValue());
    local.consume_front(".");
    auto link = mlir::StringAttr::get(module.getContext(),
                                      linkSymbol(from.getValue(), local));
    (void)mlir::SymbolTable::replaceAllSymbolUses(f, link, module);
    f.setSymName(link);
    f.getBody().getBlocks().clear();
    f.setPrivate();
    f->removeAttr(PiaDialect::getImportAttrName());
  }
  // Lemmas and spec functions exist only for the verifier: calls to them,
  // and the functions themselves, are erased (docs/codegen.md).
  auto isLemma = [&](mlir::func::CallOp call) {
    auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    return f && f->hasAttr(PiaDialect::getLemmaAttrName());
  };
  llvm::SmallVector<mlir::Operation *> statements;
  module.walk([&](mlir::Operation *op) {
    if (isContractStatement(op)) statements.push_back(op);
    if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
      if (isLemma(call)) statements.push_back(op);
  });
  for (mlir::Operation *op : statements) op->erase();
  // Spec-only state (ADR 0041): code may store a spec value in a
  // parameter, local or field of a spec-only type, but never computes with
  // one, so each spec computation still in code only feeds such places.
  // It becomes `pia.erased`, and the parameters and results that carry it
  // are marked for the C entry points, which leave them out.
  auto specCallee = [&](mlir::func::FuncOp f) {
    return f && (f->hasAttr(PiaDialect::getLemmaAttrName()) ||
                 f->hasAttr(PiaDialect::getSpecAttrName()) ||
                 f->hasAttr(PiaDialect::getAxiomAttrName()));
  };
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    if (specCallee(f)) continue;
    mlir::FunctionType ft = f.getFunctionType();
    for (unsigned i = 0; i < ft.getNumInputs(); ++i)
      if (isSpecOnly(ft.getInput(i)))
        f.setArgAttr(i, kErased, mlir::UnitAttr::get(module.getContext()));
    for (unsigned i = 0; i < ft.getNumResults(); ++i)
      if (isSpecOnly(ft.getResult(i)))
        f.setResultAttr(i, kErased, mlir::UnitAttr::get(module.getContext()));
    llvm::SmallVector<mlir::Operation *> spec;
    f.walk<mlir::WalkOrder::PreOrder>([&](mlir::Operation *op) {
      if (op->getNumResults() == 0 || op->getNumRegions() > 0) return;
      if (mlir::isa<ErasedOp>(op)) return;
      if (!llvm::all_of(op->getResultTypes(), isSpecOnly)) return;
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        if (!specCallee(
                module.lookupSymbol<mlir::func::FuncOp>(call.getCallee())))
          return;
      spec.push_back(op);
    });
    // Uses come after definitions, so the last is replaced first.
    for (mlir::Operation *op : llvm::reverse(spec)) {
      OpBuilder b(op);
      for (Value r : op->getResults())
        r.replaceAllUsesWith(make<ErasedOp>(b, op->getLoc(), r.getType()));
      op->erase();
    }
  }
  // Whatever only fed a contract is now unused. Erase it, innermost and
  // last first, until nothing changes.
  for (bool changed = true; changed;) {
    changed = false;
    llvm::SmallVector<mlir::Operation *> dead, deadRegions;
    module.walk<mlir::WalkOrder::PostOrder>([&](mlir::Operation *op) {
      if (isDead(op)) dead.push_back(op);
      // A spec function is pure, so an unused call to one, such as one
      // that only a contract read, is dead too.
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op))
        if (call->use_empty() && call.getNumResults() > 0)
          if (auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee()))
            if (f->hasAttr(PiaDialect::getSpecAttrName())) dead.push_back(op);
      // An unused region op, such as the `scf.if` of a `match` in a
      // contract, is dead when all it holds is: its nested spec calls
      // still have uses, inside it, so the loop above never reaches them.
      if (op->getNumRegions() > 0 && op->getNumResults() > 0 &&
          op->use_empty() && !op->hasTrait<mlir::OpTrait::IsTerminator>() &&
          !mlir::isa<mlir::func::FuncOp>(op)) {
        bool pure = true;
        op->walk([&](mlir::Operation *in) {
          if (in == op || in->hasTrait<mlir::OpTrait::IsTerminator>() ||
              in->getNumRegions() > 0)
            return mlir::WalkResult::advance();
          if (mlir::isa<contract::ContractDialect>(in->getDialect()) ||
              mlir::isa<LoadOp, ErasedOp>(in) || mlir::isMemoryEffectFree(in))
            return mlir::WalkResult::advance();
          if (auto call = mlir::dyn_cast<mlir::func::CallOp>(in))
            if (auto f =
                    module.lookupSymbol<mlir::func::FuncOp>(call.getCallee()))
              if (f->hasAttr(PiaDialect::getSpecAttrName()))
                return mlir::WalkResult::advance();
          pure = false;
          return mlir::WalkResult::interrupt();
        });
        if (pure) deadRegions.push_back(op);
      }
    });
    for (mlir::Operation *op : llvm::reverse(dead)) {
      if (!op->use_empty()) continue;
      op->erase();
      changed = true;
    }
    // A dead region op goes once nothing inside it is about to be erased,
    // outermost first, so no op is erased twice.
    if (changed) continue;
    for (mlir::Operation *op : deadRegions) {
      bool outermost = llvm::none_of(deadRegions, [&](mlir::Operation *o) {
        return o != op && o->isProperAncestor(op);
      });
      if (!outermost || !op->use_empty()) continue;
      op->erase();
      changed = true;
    }
  }
  for (auto f : llvm::make_early_inc_range(module.getOps<mlir::func::FuncOp>()))
    if (f->hasAttr(PiaDialect::getLemmaAttrName()) ||
        f->hasAttr(PiaDialect::getSpecAttrName()) ||
        f->hasAttr(PiaDialect::getAxiomAttrName()))
      f.erase();
}

LogicalResult lowerToCore(mlir::ModuleOp module) {
  mlir::MLIRContext *ctx = module.getContext();
  loadDialects(*ctx);

  // Signedness is a property of pia types that iN loses, and the C entry
  // points need it, so record it on the signature first.
  module.walk([&](mlir::func::FuncOp f) {
    mlir::FunctionType ft = f.getFunctionType();
    for (unsigned i = 0; i < ft.getNumInputs(); ++i)
      if (auto t = mlir::dyn_cast<IntType>(ft.getInput(i)); t && t.isSigned())
        f.setArgAttr(i, kSigned, mlir::UnitAttr::get(ctx));
    for (unsigned i = 0; i < ft.getNumResults(); ++i)
      if (auto t = mlir::dyn_cast<IntType>(ft.getResult(i)); t && t.isSigned())
        f.setResultAttr(i, kSigned, mlir::UnitAttr::get(ctx));
  });

  CoreTypes types;
  // Foreign functions (#55): each C symbol a `pia.foreign` calls gets a
  // private declaration with C types, marked `pia.c`. A Pia declaration
  // with the same name as its symbol is renamed out of the way.
  {
    llvm::SmallVector<ForeignOp> foreign;
    module.walk([&](ForeignOp op) { foreign.push_back(op); });
    std::set<std::string> declared;
    for (ForeignOp op : foreign) {
      std::string sym = op.getSymbol().str();
      if (auto own = module.lookupSymbol<mlir::func::FuncOp>(sym);
          own && !own->hasAttr("pia.c")) {
        if (!own->hasAttr("pia.extern"))
          return own.emitError() << "the C symbol '" << sym
                                 << "' is also the name of a Pia function";
        std::string renamed = "pia$ffi$" + sym;
        if (mlir::failed(mlir::SymbolTable::replaceAllSymbolUses(
                own, mlir::StringAttr::get(ctx, renamed), module)))
          return mlir::failure();
        own.setSymName(renamed);
      }
      if (!declared.insert(sym).second) continue;
      auto ptr = mlir::LLVM::LLVMPointerType::get(ctx);
      auto cType = [&](Type t) -> Type {
        Type c = types.convertType(t);
        if (c && mlir::isa<mlir::MemRefType>(c)) return ptr;
        return c;
      };
      // C extends small integers at the call (Apple arm64).
      auto ext = [&](Type t) -> std::optional<llvm::StringRef> {
        auto i = mlir::dyn_cast<IntType>(t);
        unsigned width = i ? reprOf(i).width : 0;
        if (t.isInteger(1)) return mlir::LLVM::LLVMDialect::getZExtAttrName();
        if (!i || width >= 32) return std::nullopt;
        return i.isSigned() ? mlir::LLVM::LLVMDialect::getSExtAttrName()
                            : mlir::LLVM::LLVMDialect::getZExtAttrName();
      };
      llvm::SmallVector<Type> args, results;
      for (Value a : op.getArgs()) args.push_back(cType(a.getType()));
      for (Type t : op.getResultTypes()) results.push_back(cType(t));
      OpBuilder b(ctx);
      b.setInsertionPointToEnd(module.getBody());
      auto decl = make<mlir::func::FuncOp>(
          b, op.getLoc(), sym, b.getFunctionType(args, results));
      decl.setPrivate();
      decl->setAttr("pia.c", b.getUnitAttr());
      for (auto [i, a] : llvm::enumerate(op.getArgs()))
        if (auto e = ext(a.getType()))
          decl.setArgAttr(i, *e, b.getUnitAttr());
      for (auto [i, t] : llvm::enumerate(op.getResultTypes()))
        if (auto e = ext(t)) decl.setResultAttr(i, *e, b.getUnitAttr());
    }
    // The trust marks are for the verifier and --trust-report only.
    module.walk([](mlir::Operation *op) {
      op->removeAttr("pia.extern");
      op->removeAttr("pia.unsafe");
    });
  }
  mlir::ConversionTarget target(*ctx);
  target.addLegalDialect<mlir::arith::ArithDialect, mlir::cf::ControlFlowDialect,
                         mlir::index::IndexDialect, mlir::LLVM::LLVMDialect,
                         mlir::memref::MemRefDialect>();
  target.addIllegalDialect<PiaDialect, contract::ContractDialect>();
  // ViewLowering's descriptor-to-memref cast, which the LLVM lowering's
  // reconcile-unrealized-casts removes.
  target.addLegalOp<mlir::UnrealizedConversionCastOp>();
  target.addDynamicallyLegalOp<mlir::func::FuncOp>([&](mlir::func::FuncOp f) {
    return types.isSignatureLegal(f.getFunctionType()) &&
           types.isLegal(&f.getBody());
  });
  target.addDynamicallyLegalOp<mlir::func::CallOp, mlir::func::ReturnOp>(
      [&](mlir::Operation *op) { return types.isLegal(op); });

  mlir::RewritePatternSet patterns(ctx);
  patterns.add<ConstantLowering, ArithLowering<AddOp, Arith::Add>,
               ArithLowering<SubOp, Arith::Sub>,
               ArithLowering<MulOp, Arith::Mul>,
               ArithLowering<DivOp, Arith::Div>,
               ArithLowering<RemOp, Arith::Rem>,
               ArithLowering<BAndOp, Arith::BAnd>,
               ArithLowering<BOrOp, Arith::BOr>,
               ArithLowering<BXorOp, Arith::BXor>,
               ArithLowering<ShlOp, Arith::Shl>,
               ArithLowering<ShrOp, Arith::Shr>, BitLowering<ClzOp>,
               BitLowering<CtzOp>, BitLowering<PopcountOp>,
               BitLowering<BSwapOp>, RotateLowering<RotlOp>,
               RotateLowering<RotrOp>, ConvertLowering, CmpLowering,
               ToIndexLowering, FromIndexLowering, LenLowering, LoadLowering,
               StoreLowering, SliceLowering, EmptyLowering, ErasedLowering, RegionLowering, ViewLowering, AbortLowering, ConstArrayLowering,
               ForeignLowering>(
      types, ctx);
  mlir::populateFunctionOpInterfaceTypeConversionPattern<mlir::func::FuncOp>(
      patterns, types);
  mlir::populateCallOpTypeConversionPattern(patterns, types);
  mlir::populateReturnOpTypeConversionPattern(patterns, types);
  mlir::scf::populateSCFStructuralTypeConversionsAndLegality(types, patterns,
                                                             target);
  if (mlir::failed(
          mlir::applyPartialConversion(module, target, std::move(patterns))))
    return mlir::failure();
  // Tidy the casts and constants the conversion leaves behind.
  mlir::PassManager pm(ctx);
  pm.addPass(mlir::createCanonicalizerPass());
  pm.addPass(mlir::createCSEPass());
  return pm.run(module);
}

namespace {

// A public function's C entry point, recorded before lowering.
struct Entry {
  std::string name;
  std::string cname;  // the entry point's symbol
  mlir::FunctionType type;  // core types
  std::vector<bool> argSigned;
  bool resultSigned = false;
  Location loc;
  // For each argument, the earlier argument whose length it shares (a
  // field buffer of a slice of records), or -1.
  std::vector<int> lengthOf = {};
  // The function itself, renamed: `__pia_f`, or a module's link symbol.
  std::string internal = {};
  // Whether `internal` stays external, for other modules to call.
  bool linked = false;
  // The spec-only arguments and results, which C does not see (ADR 0041).
  std::vector<bool> argErased = {}, resultErased = {};
};

// The C types of one core argument: a buffer is its data pointer, plus its
// length when that is not fixed by the type.
void cArgTypes(Type t, mlir::MLIRContext *ctx, llvm::SmallVectorImpl<Type> &out) {
  if (auto m = mlir::dyn_cast<mlir::MemRefType>(t)) {
    out.push_back(mlir::LLVM::LLVMPointerType::get(ctx));
    if (m.isDynamicDim(0)) out.push_back(mlir::IntegerType::get(ctx, 64));
    return;
  }
  if (mlir::isa<mlir::IndexType>(t)) {
    out.push_back(mlir::IntegerType::get(ctx, 64));
    return;
  }
  out.push_back(t);
}

// Small integers are extended to 32 bits at the call boundary, as Apple's
// arm64 ABI and C compilers expect.
std::optional<llvm::StringRef> extAttr(Type t, bool isSigned) {
  auto i = mlir::dyn_cast<mlir::IntegerType>(t);
  if (!i || i.getWidth() >= 32) return std::nullopt;
  if (i.getWidth() == 1 || !isSigned)
    return mlir::LLVM::LLVMDialect::getZExtAttrName();
  return mlir::LLVM::LLVMDialect::getSExtAttrName();
}

// The C name of a Pia function: each prime becomes `_prime`, so `step'`
// is `step_prime` (codegen.md, "C ABI").
std::string cName(llvm::StringRef name) {
  // An overload's symbol names its parameter types, `eq(u8, u8)`, and its
  // C entry point is `eq__u8_u8` (ADR 0034): `(` becomes `__`, and each
  // other run of characters C does not allow becomes one `_`.
  std::string out;
  bool gap = false, opened = false;
  for (char c : name) {
    if (c == '\'') {
      out += "_prime";
    } else if (c == '(') {
      out += "__";
      gap = false;
      opened = true;
    } else if (std::isalnum(static_cast<unsigned char>(c)) || c == '_') {
      if (gap) out += '_';
      gap = false;
      opened = false;
      out += c;
    } else if (!opened) {
      gap = true;
    }
  }
  return out;
}

LogicalResult buildEntry(mlir::ModuleOp module, const Entry &e) {
  mlir::MLIRContext *ctx = module.getContext();
  auto internal = module.lookupSymbol<mlir::LLVM::LLVMFuncOp>(e.internal);
  if (!internal) return mlir::emitError(e.loc) << "lost function " << e.name;
  for (Type t : e.type.getResults())
    if (mlir::isa<mlir::MemRefType>(t))
      return mlir::emitError(e.loc)
             << "codegen v0 cannot return a buffer from '" << e.name << "'";

  // A field buffer that shares another's length takes only its pointer.
  llvm::SmallVector<Type> argTypes;
  for (auto [i, t] : llvm::enumerate(e.type.getInputs())) {
    if (e.argErased[i]) continue;
    if (e.lengthOf[i] >= 0) {
      argTypes.push_back(mlir::LLVM::LLVMPointerType::get(ctx));
      continue;
    }
    cArgTypes(t, ctx, argTypes);
  }
  // A record result comes back through a pointer to a C struct of its
  // fields, which is the last argument.
  // Spec-only results are not returned.
  llvm::SmallVector<unsigned> kept;
  for (unsigned i = 0; i < e.type.getNumResults(); ++i)
    if (!e.resultErased[i]) kept.push_back(i);
  bool outStruct = kept.size() > 1;
  if (outStruct) argTypes.push_back(mlir::LLVM::LLVMPointerType::get(ctx));
  Type resultType = mlir::LLVM::LLVMVoidType::get(ctx);
  if (kept.size() == 1) {
    llvm::SmallVector<Type, 1> r;
    cArgTypes(e.type.getResult(kept[0]), ctx, r);
    resultType = r[0];
  }

  OpBuilder b(ctx);
  b.setInsertionPointAfter(internal);
  auto entry = make<mlir::LLVM::LLVMFuncOp>(
      b, e.loc, e.cname,
      mlir::LLVM::LLVMFunctionType::get(resultType, argTypes));
  mlir::Block *block = entry.addEntryBlock(b);
  b.setInsertionPointToStart(block);

  Type i64 = b.getI64Type();
  auto c64 = [&](int64_t v) -> Value {
    return make<mlir::LLVM::ConstantOp>(b, e.loc, i64, b.getI64IntegerAttr(v));
  };
  llvm::SmallVector<Value> operands;
  llvm::SmallVector<Value> sizes(e.type.getNumInputs());
  unsigned arg = 0;
  for (unsigned i = 0; i < e.type.getNumInputs(); ++i) {
    Type t = e.type.getInput(i);
    if (e.argErased[i]) {
      operands.push_back(make<mlir::LLVM::ConstantOp>(
          b, e.loc, t, b.getIntegerAttr(t, 0)));
      continue;
    }
    if (auto m = mlir::dyn_cast<mlir::MemRefType>(t)) {
      // The memref descriptor: allocated and aligned pointers, offset,
      // size and stride.
      Value data = block->getArgument(arg++);
      Value size = e.lengthOf[i] >= 0 ? sizes[e.lengthOf[i]]
                   : m.isDynamicDim(0) ? block->getArgument(arg++)
                                       : c64(m.getDimSize(0));
      sizes[i] = size;
      operands.append({data, data, c64(0), size, c64(1)});
      continue;
    }
    if (auto ext = extAttr(t, e.argSigned[i]))
      entry.setArgAttr(arg, *ext, b.getUnitAttr());
    operands.push_back(block->getArgument(arg++));
  }
  auto call = make<mlir::LLVM::CallOp>(b, e.loc, internal, operands);
  if (outStruct) {
    // Each field at its C offset: aligned to its own size.
    Value out = block->getArgument(arg);
    unsigned offset = 0;
    for (unsigned i : kept) {
      Type t = e.type.getResult(i);
      llvm::SmallVector<Type, 1> c;
      cArgTypes(t, ctx, c);
      unsigned width = c[0].getIntOrFloatBitWidth();
      unsigned size = width <= 8 ? 1 : width / 8;
      offset = (offset + size - 1) / size * size;
      Value field = make<mlir::LLVM::ExtractValueOp>(
          b, e.loc, call.getResult(), llvm::ArrayRef<int64_t>{int64_t(i)});
      if (width == 1)
        field = make<mlir::LLVM::ZExtOp>(b, e.loc, b.getI8Type(), field);
      Value at = make<mlir::LLVM::GEPOp>(
          b, e.loc, mlir::LLVM::LLVMPointerType::get(ctx), b.getI8Type(), out,
          llvm::ArrayRef<mlir::LLVM::GEPArg>{int32_t(offset)});
      make<mlir::LLVM::StoreOp>(b, e.loc, field, at);
      offset += size;
    }
    make<mlir::LLVM::ReturnOp>(b, e.loc, mlir::ValueRange{});
  } else if (kept.size() == 1) {
    if (auto ext = extAttr(e.type.getResult(kept[0]), e.resultSigned))
      entry.setResultAttr(0, *ext, b.getUnitAttr());
    Value result = call.getResult();
    if (e.type.getNumResults() > 1)
      result = make<mlir::LLVM::ExtractValueOp>(
          b, e.loc, result, llvm::ArrayRef<int64_t>{int64_t(kept[0])});
    make<mlir::LLVM::ReturnOp>(b, e.loc, result);
  } else {
    make<mlir::LLVM::ReturnOp>(b, e.loc, mlir::ValueRange{});
  }
  return mlir::success();
}

}  // namespace

LogicalResult lowerToLLVM(mlir::ModuleOp module, bool exportsOnly) {
  mlir::MLIRContext *ctx = module.getContext();
  loadDialects(*ctx);

  std::vector<Entry> entries;
  for (auto f : llvm::make_early_inc_range(module.getOps<mlir::func::FuncOp>())) {
    Entry e{f.getSymName().str(), cName(f.getSymName()), f.getFunctionType(),
            {}, false, f.getLoc()};
    e.internal = (kInternalPrefix + e.name).str();
    // An exported function's entry point is named by its module unless its
    // interface is `@abi(c)`, and its Pia calling convention stays
    // reachable, for importers, under its link symbol (ADR 0039).
    auto exported =
        f->getAttrOfType<mlir::StringAttr>(PiaDialect::getExportAttrName());
    if (exported && !exported.getValue().empty()) {
      if (exportsOnly) {
        e.internal = linkSymbol(exported.getValue(), f.getSymName());
        e.linked = true;
      }
      if (!f->hasAttr(PiaDialect::getAbiCAttrName())) {
        std::string path = exported.getValue().str();
        std::replace(path.begin(), path.end(), '.', '$');
        e.cname = "pia$" + path + "$" + e.cname;
      }
    }
    if (exported) f->removeAttr(PiaDialect::getExportAttrName());
    f->removeAttr(PiaDialect::getAbiCAttrName());
    if (exportsOnly && !exported && f.isPublic() && !f.isExternal())
      f.setPrivate();
    for (unsigned i = 0; i < f.getNumArguments(); ++i) {
      e.argSigned.push_back(static_cast<bool>(f.getArgAttr(i, kSigned)));
      auto shared = f.getArgAttrOfType<mlir::IntegerAttr>(
          i, PiaDialect::getLengthOfAttrName());
      e.lengthOf.push_back(shared ? int(shared.getInt()) : -1);
      e.argErased.push_back(static_cast<bool>(f.getArgAttr(i, kErased)));
    }
    for (unsigned i = 0; i < f.getNumResults(); ++i)
      e.resultErased.push_back(static_cast<bool>(f.getResultAttr(i, kErased)));
    // The one result C sees, if there is one.
    llvm::SmallVector<unsigned> seen;
    for (unsigned i = 0; i < f.getNumResults(); ++i)
      if (!e.resultErased[i]) seen.push_back(i);
    e.resultSigned = seen.size() == 1 &&
                     static_cast<bool>(f.getResultAttr(seen[0], kSigned));
    // Pia's own attributes have no meaning in LLVM IR. A C declaration's
    // are LLVM's: the extensions C expects (#55).
    if (f->hasAttr("pia.c")) {
      f->removeAttr("pia.c");
    } else {
      f.removeArgAttrsAttr();
      f.removeResAttrsAttr();
    }
    if (f.isExternal() || !f.isPublic()) continue;
    if (mlir::failed(mlir::SymbolTable::replaceAllSymbolUses(
            f, mlir::StringAttr::get(ctx, e.internal), module)))
      return mlir::failure();
    f.setSymName(e.internal);
    f.setPrivate();
    entries.push_back(std::move(e));
  }

  mlir::PassManager pm(ctx);
  pm.addPass(mlir::createSCFToControlFlowPass());
  pm.addPass(mlir::createConvertControlFlowToLLVMPass());
  pm.addPass(mlir::createArithToLLVMConversionPass());
  pm.addPass(mlir::createConvertIndexToLLVMPass());
  pm.addPass(mlir::createFinalizeMemRefToLLVMConversionPass());
  pm.addPass(mlir::createConvertFuncToLLVMPass());
  pm.addPass(mlir::createReconcileUnrealizedCastsPass());
  if (mlir::failed(pm.run(module))) return mlir::failure();

  std::map<std::string, std::string> cNames;
  for (const Entry &e : entries) {
    auto [it, fresh] = cNames.emplace(e.cname, e.name);
    if (!fresh || (e.cname != e.name &&
                   module.lookupSymbol((kInternalPrefix + e.cname).str())))
      return mlir::emitError(e.loc)
             << "the C entry point of '" << e.name << "' would be named '"
             << e.cname << "', which another function already uses";
  }
  // A module's private functions are internal to its object file
  // (ADR 0039), so LLVM may inline them and drop the ones nothing calls.
  if (exportsOnly)
    for (auto f : module.getOps<mlir::LLVM::LLVMFuncOp>())
      if (!f.isExternal() && f.isPrivate()) {
        f.setLinkage(mlir::LLVM::Linkage::Internal);
        f.setSymVisibility(std::nullopt);
      }
  for (const Entry &e : entries) {
    if (mlir::failed(buildEntry(module, e))) return mlir::failure();
    auto internal = module.lookupSymbol<mlir::LLVM::LLVMFuncOp>(e.internal);
    if (e.linked) {
      internal.setLinkage(mlir::LLVM::Linkage::External);
      internal.setSymVisibility(std::nullopt);
      continue;
    }
    internal.setLinkage(mlir::LLVM::Linkage::Internal);
    internal.setSymVisibility(std::nullopt);
  }
  return mlir::success();
}

namespace {

std::unique_ptr<llvm::TargetMachine> targetMachine(const Options &options,
                                                   std::string &error) {
  static bool initialised = [] {
    llvm::InitializeAllTargetInfos();
    llvm::InitializeAllTargets();
    llvm::InitializeAllTargetMCs();
    llvm::InitializeAllAsmPrinters();
    return true;
  }();
  (void)initialised;
  llvm::Triple triple(options.triple);
  const llvm::Target *target = llvm::TargetRegistry::lookupTarget(triple, error);
  if (!target) return nullptr;
  llvm::CodeGenOptLevel level = options.optLevel == 0
                                    ? llvm::CodeGenOptLevel::None
                                    : llvm::CodeGenOptLevel::Default;
  std::unique_ptr<llvm::TargetMachine> tm(target->createTargetMachine(
      triple, options.cpu, "", llvm::TargetOptions(), llvm::Reloc::PIC_,
      std::nullopt, level));
  if (!tm) error = "cannot create a target machine for " + options.triple;
  return tm;
}

}  // namespace

std::unique_ptr<llvm::Module> translate(mlir::ModuleOp module,
                                        llvm::LLVMContext &llvmCtx,
                                        const Options &options,
                                        std::string &error) {
  std::unique_ptr<llvm::TargetMachine> tm = targetMachine(options, error);
  if (!tm) return nullptr;
  std::unique_ptr<llvm::Module> m = mlir::translateModuleToLLVMIR(module, llvmCtx);
  if (!m) {
    error = "translation to LLVM IR failed";
    return nullptr;
  }
  m->setTargetTriple(tm->getTargetTriple());
  m->setDataLayout(tm->createDataLayout());
  auto optimise =
      mlir::makeOptimizingTransformer(options.optLevel, 0, tm.get());
  if (llvm::Error e = optimise(m.get())) {
    error = llvm::toString(std::move(e));
    return nullptr;
  }
  return m;
}

bool emitObject(llvm::Module &module, const Options &options,
                llvm::raw_pwrite_stream &os, std::string &error,
                bool assembly) {
  std::unique_ptr<llvm::TargetMachine> tm = targetMachine(options, error);
  if (!tm) return false;
  llvm::legacy::PassManager pm;
  if (tm->addPassesToEmitFile(pm, os, nullptr,
                              assembly ? llvm::CodeGenFileType::AssemblyFile
                                       : llvm::CodeGenFileType::ObjectFile)) {
    error = "the target cannot emit an object file";
    return false;
  }
  pm.run(module);
  return true;
}

}  // namespace pia::codegen
