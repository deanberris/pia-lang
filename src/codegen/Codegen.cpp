// Codegen v0 (milestone M6). docs/codegen.md describes the lowering.

#include "codegen/Codegen.h"
#include "codegen/ArrayResults.h"
#include "codegen/Lowerings.h"
#include "codegen/SliceBuffers.h"
#include "gpu/Place.h"

#include "cert/Certificate.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "dialect/ContractDialect.h"
#include "dialect/PiaDialect.h"
#include "mlir/Conversion/ArithToLLVM/ArithToLLVM.h"
#include "mlir/Conversion/AsyncToLLVM/AsyncToLLVM.h"
#include "mlir/Conversion/ControlFlowToLLVM/ControlFlowToLLVM.h"
#include "mlir/Conversion/FuncToLLVM/ConvertFuncToLLVMPass.h"
#include "mlir/Conversion/IndexToLLVM/IndexToLLVM.h"
#include "mlir/Conversion/MemRefToLLVM/MemRefToLLVM.h"
#include "mlir/Conversion/ReconcileUnrealizedCasts/ReconcileUnrealizedCasts.h"
#include "mlir/Conversion/SCFToControlFlow/SCFToControlFlow.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Async/IR/Async.h"
#include "mlir/Dialect/Async/Passes.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlow.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Func/Transforms/FuncConversions.h"
#include "mlir/Dialect/Index/IR/IndexDialect.h"
#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "transforms/ScalarizeRecords.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SCF/Transforms/Patterns.h"
#include "mlir/ExecutionEngine/OptUtils.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Target/LLVMIR/Dialect/Builtin/BuiltinToLLVMIRTranslation.h"
#include "mlir/Target/LLVMIR/Dialect/LLVMIR/LLVMToLLVMIRTranslation.h"
#include "mlir/Target/LLVMIR/Export.h"
#include "mlir/Transforms/DialectConversion.h"
#include "mlir/Transforms/Passes.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

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

// The buffer of a spec-only field of a buffer's records (ADR 0041): code
// only stores into it, and those stores are erased, so it holds nothing
// and C entry points leave it out.
bool isSpecBuffer(Type t) {
  if (auto s = mlir::dyn_cast<SliceType>(t)) return isSpecOnly(s.getElementType());
  if (auto a = mlir::dyn_cast<ArrayType>(t)) return isSpecOnly(a.getElementType());
  return false;
}

// The LLVM struct of a memref descriptor of rank 1, as the MemRef to LLVM
// lowering makes it.
mlir::LLVM::LLVMStructType descriptorType(mlir::MLIRContext *ctx) {
  auto i64 = mlir::IntegerType::get(ctx, 64);
  auto ptr = mlir::LLVM::LLVMPointerType::get(ctx);
  auto dims = mlir::LLVM::LLVMArrayType::get(i64, 1);
  return mlir::LLVM::LLVMStructType::getLiteral(ctx, {ptr, ptr, i64, dims, dims});
}

class CoreTypes : public mlir::TypeConverter {
 public:
  // A recursive value (ADR 0047, step 3) is laid out as its variant is
  // (ADR 0030): a struct of its tag and every constructor's payload
  // fields, in order. A buffer in a payload, such as a box's slot, is its
  // memref descriptor, so a recursive occurrence is a pointer into
  // memory its allocator lent. Each type is an identified LLVM struct,
  // `pia.rec.tree`, so a box of a tree inside a tree is no cycle of types.
  struct RecLayout {
    mlir::LLVM::LLVMStructType type;
    // Each constructor's first field; field 0 is the tag.
    std::map<std::string, unsigned> first;
    std::map<std::string, unsigned> tag;
  };

  void addDatatypes(mlir::ModuleOp module) {
    mlir::MLIRContext *ctx = module.getContext();
    for (DatatypeOp d : module.getOps<DatatypeOp>())
      recs_[d.getSymName().str()].type =
          mlir::LLVM::LLVMStructType::getIdentified(
              ctx, ("pia.rec." + d.getSymName()).str());
    for (DatatypeOp d : module.getOps<DatatypeOp>()) {
      RecLayout &l = recs_[d.getSymName().str()];
      llvm::SmallVector<Type> fields{tagType(ctx, d.getCtors().size())};
      for (auto [i, c] :
           llvm::enumerate(d.getCtors().getAsValueRange<mlir::StringAttr>())) {
        l.first[c.str()] = fields.size();
        l.tag[c.str()] = i;
        llvm::SmallVector<Type> leaves;
        if (Type p = d.payloadOf(i)) {
          if (mlir::isa<RecordType>(p))
            transforms::recordLeaves(p, leaves);
          else
            leaves.push_back(p);
        }
        for (Type leaf : leaves) {
          Type f = convertType(leaf);
          if (f && mlir::isa<mlir::MemRefType>(f)) f = descriptorType(ctx);
          if (!f) f = mlir::IntegerType::get(ctx, 1);
          fields.push_back(f);
        }
      }
      (void)l.type.setBody(fields, /*isPacked=*/false);
    }
  }

  const RecLayout *layout(RecType t) const {
    auto it = recs_.find(t.getName().str());
    return it == recs_.end() ? nullptr : &it->second;
  }

  // The tag's type: as `rec_tag` gives it, the range 0 to n - 1.
  Type tagType(mlir::MLIRContext *ctx, size_t n) {
    return convertType(IntType::get(ctx, APInt(128, 0), APInt(128, n - 1)));
  }

  CoreTypes() {
    addConversion([](Type t) { return t; });
    addConversion([this](RecType t) -> std::optional<Type> {
      auto it = recs_.find(t.getName().str());
      if (it == recs_.end()) return std::nullopt;
      return Type(it->second.type);
    });
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
    // An atomic cell is one element in memory (ADR 0052). A bool is held
    // as a byte, since LLVM's atomics take whole bytes.
    addConversion([this](AtomicType t) -> std::optional<Type> {
      Type elem = t.getElementType().isInteger(1)
                      ? mlir::IntegerType::get(t.getContext(), 8)
                      : element(t.getElementType());
      if (!elem)
        return std::nullopt;
      return mlir::MemRefType::get({1}, elem);
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
    // A function reference's type, in machine types (ADR 0071).
    addConversion([this](mlir::FunctionType t) -> std::optional<Type> {
      llvm::SmallVector<Type> inputs, results;
      if (mlir::failed(convertTypes(t.getInputs(), inputs)) ||
          mlir::failed(convertTypes(t.getResults(), results)))
        return std::nullopt;
      return mlir::FunctionType::get(t.getContext(), inputs, results);
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
  // Buffers hold scalars, and recursive values (ADR 0047).
  Type element(Type t) {
    Type c = convertType(t);
    if (c && mlir::isa<mlir::IntegerType, mlir::IndexType, mlir::FloatType,
                       mlir::LLVM::LLVMStructType>(c))
      return c;
    // A buffer of function references, such as a handler table's field
    // once its records are scalarized, holds addresses (ADR 0071), as
    // 64-bit integers: a memref holds no pointers, and both targets'
    // addresses are 64 bits (ADR 0049).
    if (c && mlir::isa<mlir::FunctionType>(c))
      return mlir::IntegerType::get(t.getContext(), 64);
    return {};
  }

  std::map<std::string, RecLayout> recs_;
};

//===----------------------------------------------------------------------===//
// Patterns
//===----------------------------------------------------------------------===//

// A function reference's address and a call through it (ADR 0071) keep
// their ops; only the function type they carry changes to machine types.
struct FunctionConstantLowering
    : mlir::OpConversionPattern<mlir::func::ConstantOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(mlir::func::ConstantOp op, OpAdaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Type t = getTypeConverter()->convertType(op.getType());
    if (!t)
      return mlir::failure();
    rw.replaceOpWithNewOp<mlir::func::ConstantOp>(op, t, op.getValueAttr());
    return mlir::success();
  }
};

struct CallIndirectLowering
    : mlir::OpConversionPattern<mlir::func::CallIndirectOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(mlir::func::CallIndirectOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    rw.replaceOpWithNewOp<mlir::func::CallIndirectOp>(
        op, adaptor.getCallee(), adaptor.getCalleeOperands());
    return mlir::success();
  }
};

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

// Floats and integers (M11). A range integer is held in its repr, whose
// signedness says which LLVM conversion reads it. Truncation toward zero is
// what fptosi and fptoui do, and the verifier proved the result fits the
// target's range, so neither can produce LLVM's poison.
struct IntToFloatLowering : mlir::OpConversionPattern<IntToFloatOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(IntToFloatOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Type t = op.getResult().getType();
    if (reprOf(mlir::cast<IntType>(op.getInput().getType())).isSigned)
      rw.replaceOpWithNewOp<mlir::arith::SIToFPOp>(op, t, adaptor.getInput());
    else
      rw.replaceOpWithNewOp<mlir::arith::UIToFPOp>(op, t, adaptor.getInput());
    return mlir::success();
  }
};

struct FloatToIntLowering : mlir::OpConversionPattern<FloatToIntOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(FloatToIntOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Repr r = reprOf(mlir::cast<IntType>(op.getResult().getType()));
    Type t = rw.getIntegerType(r.width);
    if (r.isSigned)
      rw.replaceOpWithNewOp<mlir::arith::FPToSIOp>(op, t, adaptor.getInput());
    else
      rw.replaceOpWithNewOp<mlir::arith::FPToUIOp>(op, t, adaptor.getInput());
    return mlir::success();
  }
};

// IRGen gives `to_bits` and `from_bits` the unsigned type of the float's
// width, whose repr is that width, so both are a bitcast.
template <typename OpTy>
struct BitcastLowering : mlir::OpConversionPattern<OpTy> {
  using mlir::OpConversionPattern<OpTy>::OpConversionPattern;
  using OpAdaptor = typename OpTy::Adaptor;
  LogicalResult
  matchAndRewrite(OpTy op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Type t = this->getTypeConverter()->convertType(op.getResult().getType());
    rw.replaceOpWithNewOp<mlir::arith::BitcastOp>(op, t, adaptor.getInput());
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
    Value load =
        make<mlir::memref::LoadOp>(rw, op.getLoc(), adaptor.getBuffer(),
                                   mlir::ValueRange{adaptor.getIndex()});
    // A function reference is held as its address (ADR 0071), and is a
    // function value again once read.
    Type want = getTypeConverter()->convertType(op.getType());
    if (want && mlir::isa<mlir::FunctionType>(want)) {
      auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
      load = make<mlir::LLVM::IntToPtrOp>(rw, op.getLoc(), ptr, load);
      load = make<mlir::UnrealizedConversionCastOp>(rw, op.getLoc(), want, load)
                 .getResult(0);
    }
    rw.replaceOp(op, load);
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
    // Spec state's storage (ADR 0058) that a loop or a record still
    // carries: nothing reads or writes it, so a view of one byte of the
    // frame, at the type the carrier needs, stands in for it.
    if (auto m = mlir::dyn_cast<mlir::MemRefType>(t)) {
      auto one = mlir::MemRefType::get({1}, m.getElementType());
      Value cell = make<mlir::memref::AllocaOp>(rw, op.getLoc(), one);
      llvm::SmallVector<mlir::OpFoldResult> sizes, strides;
      for (int64_t d : m.getShape()) {
        sizes.push_back(d == mlir::ShapedType::kDynamic
                            ? mlir::OpFoldResult(rw.getIndexAttr(0))
                            : mlir::OpFoldResult(rw.getIndexAttr(d)));
        strides.push_back(rw.getIndexAttr(1));
      }
      rw.replaceOpWithNewOp<mlir::memref::ReinterpretCastOp>(
          op, m, cell, rw.getIndexAttr(0), sizes, strides);
      return mlir::success();
    }
    rw.replaceOpWithNewOp<mlir::arith::ConstantOp>(op, t, rw.getZeroAttr(t));
    return mlir::success();
  }
};

// `pia.copy src, dst`: memref.copy of every element.
struct CopyLowering : mlir::OpConversionPattern<CopyOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      CopyOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    rw.replaceOpWithNewOp<mlir::memref::CopyOp>(op, adaptor.getSrc(),
                                                adaptor.getDst());
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
    Type elem = type.getElementType();
    auto fn = op->getParentOfType<mlir::func::FuncOp>();
    if (!mlir::isa<mlir::IntegerType, mlir::FloatType>(elem) || !fn)
      return mlir::failure();
    Value storage;
    {
      mlir::OpBuilder::InsertionGuard guard(rw);
      rw.setInsertionPointToStart(&fn.getBody().front());
      storage = make<mlir::memref::AllocaOp>(rw, loc, type);
    }
    // Zero is all bits clear for an integer and for a float (+0.0).
    mlir::TypedAttr zeroAttr =
        mlir::isa<mlir::FloatType>(elem)
            ? mlir::TypedAttr(rw.getFloatAttr(elem, 0.0))
            : mlir::TypedAttr(rw.getIntegerAttr(elem, 0));
    Value zero = make<mlir::arith::ConstantOp>(rw, loc, elem, zeroAttr);
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

// Builds a memref descriptor `{p, p, 0, [n], [1]}` for `n` elements at `p`.
Value sliceFromPtr(mlir::ConversionPatternRewriter &rw, Location loc,
                   mlir::MemRefType type, Value p, Value n) {
  auto i64 = rw.getI64Type();
  auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
  auto dims = mlir::LLVM::LLVMArrayType::get(i64, 1);
  auto desc = mlir::LLVM::LLVMStructType::getLiteral(
      rw.getContext(), {ptr, ptr, i64, dims, dims});
  Value zero =
      make<mlir::LLVM::ConstantOp>(rw, loc, i64, rw.getI64IntegerAttr(0));
  Value one =
      make<mlir::LLVM::ConstantOp>(rw, loc, i64, rw.getI64IntegerAttr(1));
  Value d = make<mlir::LLVM::UndefOp>(rw, loc, desc);
  auto insert = [&](Value v, llvm::ArrayRef<int64_t> at) {
    d = make<mlir::LLVM::InsertValueOp>(rw, loc, d, v, at);
  };
  insert(p, {0});
  insert(p, {1});
  insert(zero, {2});
  insert(n, {3, 0});
  insert(one, {4, 0});
  return make<mlir::UnrealizedConversionCastOp>(rw, loc, mlir::TypeRange{type},
                                                mlir::ValueRange{d})
      .getResult(0);
}

// `unsafe view addr n`: a memref descriptor over foreign memory, built
// as the LLVM struct a memref lowers to, so its uses lower as usual.
// The memref descriptor of the `length` elements at the address `addr`,
// an i64: no offset, unit stride.
Value sliceAt(mlir::ConversionPatternRewriter &rw, Location loc,
              mlir::MemRefType type, Value addr, Value length) {
  auto i64 = rw.getI64Type();
  auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
  Value p = make<mlir::LLVM::IntToPtrOp>(rw, loc, ptr, addr);
  Value n = make<mlir::arith::IndexCastOp>(rw, loc, i64, length);
  return sliceFromPtr(rw, loc, type, p, n);
}

// Embedded binary blob (ADR 0070): for non-empty blobs, declare an external
// constant llvm.mlir.global (populated directly with a ConstantDataArray in
// translate()) and wrap its address in a slice descriptor; for empty blobs,
// cast a zero-length stack allocation as in EmptyLowering.
struct EmbedLowering : mlir::OpConversionPattern<EmbedOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(EmbedOp op, OpAdaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto sliceType = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    if (!sliceType)
      return mlir::failure();
    int64_t len = op.getLength();
    if (len == 0) {
      auto none = mlir::MemRefType::get({0}, sliceType.getElementType());
      Value storage = make<mlir::memref::AllocaOp>(rw, loc, none);
      rw.replaceOpWithNewOp<mlir::memref::CastOp>(op, sliceType, storage);
      return mlir::success();
    }
    auto i8 = rw.getI8Type();
    auto i64 = rw.getI64Type();
    auto arrType = mlir::LLVM::LLVMArrayType::get(i8, len);
    auto module = op->getParentOfType<mlir::ModuleOp>();
    llvm::StringRef sym = op.getSymbol();
    if (!module.lookupSymbol<mlir::LLVM::GlobalOp>(sym)) {
      mlir::OpBuilder::InsertionGuard guard(rw);
      rw.setInsertionPointToStart(module.getBody());
      make<mlir::LLVM::GlobalOp>(rw, loc, arrType, /*isConstant=*/true,
                                 mlir::LLVM::Linkage::External, sym,
                                 mlir::Attribute());
    }
    auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
    Value p = make<mlir::LLVM::AddressOfOp>(rw, loc, ptr, sym);
    Value n =
        make<mlir::LLVM::ConstantOp>(rw, loc, i64, rw.getI64IntegerAttr(len));
    rw.replaceOp(op, sliceFromPtr(rw, loc, sliceType, p, n));
    return mlir::success();
  }
};

// A box over a concept (ADR 0046, the cache-line amendment) is one cache
// line of 64-bit words: the first holds its descriptor's address, and the
// object follows in its C layout, each field at its natural alignment.

// The bytes a field of machine type `t` takes in an object, which is also
// its alignment; 0 for a type an object cannot hold inline.
int64_t boxFieldBytes(Type t) {
  if (!t.isIntOrFloat())
    return 0;
  unsigned bits = t.getIntOrFloatBitWidth();
  int64_t bytes = llvm::PowerOf2Ceil(std::max(1u, (bits + 7) / 8));
  return bytes <= 8 ? bytes : 0;
}

// `p + bytes`, as an LLVM pointer.
Value bytesAfter(OpBuilder &b, Location loc, Value p, int64_t bytes) {
  auto ptr = mlir::LLVM::LLVMPointerType::get(b.getContext());
  return make<mlir::LLVM::GEPOp>(
      b, loc, ptr, b.getI8Type(), p,
      llvm::ArrayRef<mlir::LLVM::GEPArg>{static_cast<int32_t>(bytes)});
}

// A stack slot for a box's words, so that its object has an address.
Value boxSlot(OpBuilder &b, Location loc, int64_t words) {
  auto ptr = mlir::LLVM::LLVMPointerType::get(b.getContext());
  Value one = make<mlir::LLVM::ConstantOp>(b, loc, b.getI64Type(),
                                           b.getI64IntegerAttr(1));
  auto line = mlir::LLVM::LLVMArrayType::get(b.getI64Type(), words);
  return make<mlir::LLVM::AllocaOp>(b, loc, ptr, line, one,
                                    static_cast<unsigned>(words * 8));
}

// `pia.box_pack`: the descriptor's address and the object's fields stored
// in a cache line, read back as its words. The descriptor is declared
// here, with what addBoxEntries and defineBoxDescriptors need to define it.
struct BoxPackLowering : mlir::OpConversionPattern<BoxPackOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(BoxPackOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    mlir::MLIRContext *ctx = rw.getContext();
    auto ptr = mlir::LLVM::LLVMPointerType::get(ctx);
    auto i64 = rw.getI64Type();
    int64_t words = op.getNumResults();
    llvm::SmallVector<Type> leaves;
    llvm::SmallVector<int64_t> offsets;
    int64_t end = 0, align = 1;
    for (Value v : adaptor.getObject()) {
      int64_t bytes = boxFieldBytes(v.getType());
      if (bytes == 0)
        return op.emitError()
               << "a box over a concept holds integers, floats, bools and "
                  "records of them for now, not "
               << v.getType();
      end = llvm::alignTo(end, bytes);
      offsets.push_back(end);
      leaves.push_back(v.getType());
      end += bytes;
      align = std::max(align, bytes);
    }
    int64_t size = llvm::alignTo(end, align);
    int64_t room = (words - 1) * 8;
    if (size > room)
      return op.emitError()
             << "this object takes " << size << " bytes, more than the " << room
             << " a box's cache line holds inline; a larger object needs "
                "a block through the box's lease, which is not built yet "
                "(ADR 0046)";
    auto module = op->getParentOfType<mlir::ModuleOp>();
    llvm::StringRef sym = op.getDescriptor();
    if (!module.lookupSymbol<mlir::LLVM::GlobalOp>(sym)) {
      llvm::SmallVector<Type> entries{i64, i64, ptr};
      for (size_t i = 0; i < op.getThunks().size(); ++i)
        entries.push_back(ptr);
      auto type = mlir::LLVM::LLVMStructType::getLiteral(ctx, entries);
      mlir::OpBuilder::InsertionGuard guard(rw);
      rw.setInsertionPointToStart(module.getBody());
      auto g = make<mlir::LLVM::GlobalOp>(rw, loc, type, /*isConstant=*/true,
                                          mlir::LLVM::Linkage::External, sym,
                                          mlir::Attribute());
      g->setAttr("pia.box_thunks", op.getThunks());
      g->setAttr("pia.box_leaves", rw.getTypeArrayAttr(leaves));
      g->setAttr("pia.box_offsets", rw.getDenseI64ArrayAttr(offsets));
      g->setAttr("pia.box_size", rw.getI64IntegerAttr(size));
      g->setAttr("pia.box_align", rw.getI64IntegerAttr(align));
    }
    Value slot = boxSlot(rw, loc, words);
    Value zero =
        make<mlir::LLVM::ConstantOp>(rw, loc, i64, rw.getI64IntegerAttr(0));
    for (int64_t w = 1; w < words; ++w)
      make<mlir::LLVM::StoreOp>(rw, loc, zero,
                                bytesAfter(rw, loc, slot, w * 8));
    Value desc = make<mlir::LLVM::AddressOfOp>(rw, loc, ptr, sym);
    make<mlir::LLVM::StoreOp>(rw, loc, desc, slot);
    for (auto [v, off] : llvm::zip_equal(adaptor.getObject(), offsets))
      make<mlir::LLVM::StoreOp>(rw, loc, v, bytesAfter(rw, loc, slot, 8 + off));
    llvm::SmallVector<Value> out;
    for (int64_t w = 0; w < words; ++w)
      out.push_back(make<mlir::LLVM::LoadOp>(rw, loc, i64,
                                             bytesAfter(rw, loc, slot, w * 8)));
    rw.replaceOp(op, out);
    return mlir::success();
  }
};

// `pia.box_call`: the requirement's entry, loaded from the descriptor the
// box's first word points to, called with the object's address and the
// other arguments. Where LLVM sees which descriptor the box holds, the
// loads fold and the call is direct.
struct BoxCallLowering : mlir::OpConversionPattern<BoxCallOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(BoxCallOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
    int64_t words = op.getWords();
    mlir::ValueRange args = adaptor.getArgs();
    if (static_cast<int64_t>(args.size()) < words)
      return mlir::failure();
    llvm::SmallVector<Type> results;
    if (mlir::failed(
            getTypeConverter()->convertTypes(op.getResultTypes(), results)))
      return mlir::failure();
    if (results.size() > 1 ||
        (results.size() == 1 && !boxFieldBytes(results.front())))
      return op.emitError() << "a call through a box returns one integer, "
                               "float or bool for now";
    Value slot = boxSlot(rw, loc, words);
    for (int64_t w = 0; w < words; ++w)
      make<mlir::LLVM::StoreOp>(rw, loc, args[w],
                                bytesAfter(rw, loc, slot, w * 8));
    Value desc = make<mlir::LLVM::LoadOp>(rw, loc, ptr, slot);
    // The size, the alignment and the drop come first.
    Value fn = make<mlir::LLVM::LoadOp>(
        rw, loc, ptr,
        bytesAfter(rw, loc, desc,
                   8 * (3 + static_cast<int64_t>(op.getEntry()))));
    llvm::SmallVector<Type> params{ptr};
    llvm::SmallVector<Value> operands{fn, bytesAfter(rw, loc, slot, 8)};
    for (Value a : args.drop_front(words)) {
      if (!boxFieldBytes(a.getType()))
        return op.emitError() << "a call through a box passes integers, "
                                 "floats and bools for now, not "
                              << a.getType();
      params.push_back(a.getType());
      operands.push_back(a);
    }
    Type result = results.empty()
                      ? Type(mlir::LLVM::LLVMVoidType::get(rw.getContext()))
                      : results.front();
    auto fnType = mlir::LLVM::LLVMFunctionType::get(result, params);
    auto call = make<mlir::LLVM::CallOp>(rw, loc, fnType, operands);
    if (results.empty())
      rw.eraseOp(op);
    else
      rw.replaceOp(op, call.getResult());
    return mlir::success();
  }
};

struct ViewLowering : mlir::OpConversionPattern<ViewOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(ViewOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    Value addr = adaptor.getAddress();
    if (!type || addr.getType() != rw.getI64Type())
      return mlir::failure();
    rw.replaceOp(op, sliceAt(rw, op.getLoc(), type, addr, adaptor.getLength()));
    return mlir::success();
  }
};

// An element of a buffer of slices, rebuilt from its address and length
// (ADR 0048, section 4).
struct AtAddressLowering : mlir::OpConversionPattern<AtAddressOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AtAddressOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    if (!type)
      return mlir::failure();
    Value addr = make<mlir::arith::IndexCastOp>(
        rw, op.getLoc(), rw.getI64Type(), adaptor.getAddress());
    rw.replaceOp(op, sliceAt(rw, op.getLoc(), type, addr, adaptor.getLength()));
    return mlir::success();
  }
};

// The address of a slice's first element: its storage's aligned pointer
// plus its offset, in bytes.
struct AddressLowering : mlir::OpConversionPattern<AddressOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AddressOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    Value src = adaptor.getSlice();
    auto type = mlir::dyn_cast<mlir::MemRefType>(src.getType());
    if (!type)
      return mlir::failure();
    // An element's size in bytes, as LLVM stores it: a power of two.
    unsigned bits = type.getElementType().isIndex()
                        ? 64
                        : type.getElementType().getIntOrFloatBitWidth();
    int64_t bytes = llvm::PowerOf2Ceil(std::max(1u, (bits + 7) / 8));
    auto meta = make<mlir::memref::ExtractStridedMetadataOp>(rw, loc, src);
    Value base =
        make<mlir::memref::ExtractAlignedPointerAsIndexOp>(rw, loc, src);
    Value size = make<mlir::arith::ConstantIndexOp>(rw, loc, bytes);
    Value skip = make<mlir::arith::MulIOp>(rw, loc, meta.getOffset(), size);
    rw.replaceOpWithNewOp<mlir::arith::AddIOp>(op, base, skip);
    return mlir::success();
  }
};

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
    if (op->hasAttr("pia.variadic") || op->hasAttr("pia.deref")) {
      auto module = op->getParentOfType<mlir::ModuleOp>();
      auto callee = module.lookupSymbol<mlir::LLVM::LLVMFuncOp>(op.getSymbol());
      if (!callee)
        return rw.notifyMatchFailure(op, "no llvm.func declaration");
      auto call = make<mlir::LLVM::CallOp>(rw, loc, callee, args);
      if (!op->hasAttr("pia.deref")) {
        rw.replaceOp(op, call->getResults());
        return mlir::success();
      }
      // C returned a pointer to the result: read it here, so that the
      // pointer never reaches Pia (ADR 0057, section 5).
      Type result = getTypeConverter()->convertType(op.getResult(0).getType());
      auto load = make<mlir::LLVM::LoadOp>(rw, loc, result, call.getResult());
      rw.replaceOp(op, load.getResult());
      return mlir::success();
    }
    llvm::SmallVector<Type> results;
    for (Type t : op.getResultTypes())
      results.push_back(getTypeConverter()->convertType(t));
    rw.replaceOpWithNewOp<mlir::func::CallOp>(op, op.getSymbol(), results,
                                              args);
    return mlir::success();
  }
};

//===----------------------------------------------------------------------===//
// Recursive values (ADR 0047, step 3)
//===----------------------------------------------------------------------===//

// A memref as its descriptor, a field of a recursive value, and back.
Value toDescriptor(mlir::ConversionPatternRewriter &rw, Location loc, Value v) {
  if (!mlir::isa<mlir::MemRefType>(v.getType())) return v;
  return make<mlir::UnrealizedConversionCastOp>(
             rw, loc, mlir::TypeRange{descriptorType(rw.getContext())},
             mlir::ValueRange{v})
      .getResult(0);
}

// A value of the constructor `ctor`: its tag, and its payload in the
// constructor's fields. The other constructors' fields are zero, which
// nothing reads.
struct RecMakeLowering : mlir::OpConversionPattern<RecMakeOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      RecMakeOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    auto &types = *static_cast<const CoreTypes *>(getTypeConverter());
    const CoreTypes::RecLayout *l = types.layout(op.getType());
    if (!l) return mlir::failure();
    Location loc = op.getLoc();
    unsigned tag = l->tag.at(op.getCtor().str());
    Value v = make<mlir::LLVM::ZeroOp>(rw, loc, l->type);
    Type tt = l->type.getBody()[0];
    Value k = make<mlir::LLVM::ConstantOp>(rw, loc, tt,
                                           rw.getIntegerAttr(tt, tag));
    v = make<mlir::LLVM::InsertValueOp>(rw, loc, v, k, llvm::ArrayRef<int64_t>{0});
    unsigned at = l->first.at(op.getCtor().str());
    for (Value p : adaptor.getPayload())
      v = make<mlir::LLVM::InsertValueOp>(
          rw, loc, v, toDescriptor(rw, loc, p),
          llvm::ArrayRef<int64_t>{static_cast<int64_t>(at++)});
    rw.replaceOp(op, v);
    return mlir::success();
  }
};

struct RecTagLowering : mlir::OpConversionPattern<RecTagOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      RecTagOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Type t = getTypeConverter()->convertType(op.getType());
    Value tag = make<mlir::LLVM::ExtractValueOp>(rw, op.getLoc(), adaptor.getInput(),
                                                 llvm::ArrayRef<int64_t>{0});
    if (tag.getType() != t) return mlir::failure();
    rw.replaceOp(op, tag);
    return mlir::success();
  }
};

struct RecPayloadLowering : mlir::OpConversionPattern<RecPayloadOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      RecPayloadOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    auto &types = *static_cast<const CoreTypes *>(getTypeConverter());
    const CoreTypes::RecLayout *l = types.layout(op.getInput().getType());
    if (!l) return mlir::failure();
    Location loc = op.getLoc();
    unsigned at = l->first.at(op.getCtor().str());
    llvm::SmallVector<Value> out;
    for (Type r : op.getResultTypes()) {
      Type t = getTypeConverter()->convertType(r);
      if (!t) return mlir::failure();
      Value f = make<mlir::LLVM::ExtractValueOp>(
          rw, loc, adaptor.getInput(),
          llvm::ArrayRef<int64_t>{static_cast<int64_t>(at++)});
      if (mlir::isa<mlir::MemRefType>(t))
        f = make<mlir::UnrealizedConversionCastOp>(rw, loc, mlir::TypeRange{t},
                                                   mlir::ValueRange{f})
                .getResult(0);
      out.push_back(f);
    }
    rw.replaceOp(op, out);
    return mlir::success();
  }
};

struct StoreLowering : mlir::OpConversionPattern<StoreOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult matchAndRewrite(
      StoreOp op, OpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    Value v = adaptor.getValue();
    // A function reference is stored as its address (ADR 0071).
    if (mlir::isa<mlir::FunctionType>(v.getType())) {
      auto ptr = mlir::LLVM::LLVMPointerType::get(rw.getContext());
      v = make<mlir::UnrealizedConversionCastOp>(rw, op.getLoc(), ptr, v)
              .getResult(0);
      v = make<mlir::LLVM::PtrToIntOp>(rw, op.getLoc(), rw.getI64Type(), v);
    }
    rw.replaceOpWithNewOp<mlir::memref::StoreOp>(
        op, v, adaptor.getBuffer(), mlir::ValueRange{adaptor.getIndex()});
    return mlir::success();
  }
};

//===----------------------------------------------------------------------===//
// Atomics (ADR 0052)
//===----------------------------------------------------------------------===//

// A cell is a one-element memref, and its ops are LLVM atomics on the
// memref's aligned pointer. LLVM's backends pick each target's instructions
// (ADR 0052, section 5); `relaxed` is LLVM's `monotonic`.
mlir::LLVM::AtomicOrdering llvmOrder(MemoryOrder o) {
  using L = mlir::LLVM::AtomicOrdering;
  switch (o) {
  case MemoryOrder::relaxed:
    return L::monotonic;
  case MemoryOrder::acquire:
    return L::acquire;
  case MemoryOrder::release:
    return L::release;
  case MemoryOrder::acq_rel:
    return L::acq_rel;
  case MemoryOrder::seq_cst:
    return L::seq_cst;
  }
  return L::seq_cst;
}

// The failure order a compare-and-swap loop uses for an op of order `o`:
// its read half, which is all a failed exchange does.
mlir::LLVM::AtomicOrdering readHalf(MemoryOrder o) {
  using L = mlir::LLVM::AtomicOrdering;
  switch (o) {
  case MemoryOrder::acquire:
  case MemoryOrder::acq_rel:
    return L::acquire;
  case MemoryOrder::seq_cst:
    return L::seq_cst;
  default:
    return L::monotonic;
  }
}

// A cell's address and how its values are held there. A bool is a byte,
// since LLVM's atomics take whole bytes.
struct CellAccess {
  Value ptr;
  mlir::IntegerType storage;
  unsigned align;
  bool isBool;
  bool isSigned;

  Value toStorage(OpBuilder &b, Location loc, Value v) const {
    if (!isBool)
      return v;
    return make<mlir::arith::ExtUIOp>(b, loc, storage, v);
  }
  Value fromStorage(OpBuilder &b, Location loc, Value v) const {
    if (!isBool)
      return v;
    Value zero = make<mlir::arith::ConstantOp>(b, loc, storage,
                                               b.getIntegerAttr(storage, 0));
    return make<mlir::arith::CmpIOp>(b, loc, mlir::arith::CmpIPredicate::ne, v,
                                     zero);
  }
};

CellAccess cellAccess(OpBuilder &b, Location loc, AtomicType cell,
                      Value memref) {
  auto ptr = mlir::LLVM::LLVMPointerType::get(b.getContext());
  Value base =
      make<mlir::memref::ExtractAlignedPointerAsIndexOp>(b, loc, memref);
  Value addr = make<mlir::arith::IndexCastOp>(b, loc, b.getI64Type(), base);
  CellAccess c;
  c.ptr = make<mlir::LLVM::IntToPtrOp>(b, loc, ptr, addr);
  c.storage = mlir::cast<mlir::IntegerType>(
      mlir::cast<mlir::MemRefType>(memref.getType()).getElementType());
  c.align = c.storage.getWidth() / 8;
  c.isBool = cell.getElementType().isInteger(1);
  auto it = mlir::dyn_cast<IntType>(cell.getElementType());
  c.isSigned = it && reprOf(it).isSigned;
  return c;
}

// `atomic_new v`: the cell's memory is a slot in the function's frame,
// allocated at entry so that a cell made in a loop does not grow the stack.
struct AtomicNewLowering : mlir::OpConversionPattern<AtomicNewOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AtomicNewOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    auto type = mlir::dyn_cast_or_null<mlir::MemRefType>(
        getTypeConverter()->convertType(op.getType()));
    auto fn = op->getParentOfType<mlir::func::FuncOp>();
    if (!type || !fn)
      return mlir::failure();
    Value storage;
    {
      mlir::OpBuilder::InsertionGuard guard(rw);
      rw.setInsertionPointToStart(&fn.getBody().front());
      storage = make<mlir::memref::AllocaOp>(rw, loc, type);
    }
    Value v = adaptor.getValue();
    if (v.getType() != type.getElementType())
      v = make<mlir::arith::ExtUIOp>(rw, loc, type.getElementType(), v);
    Value zero = make<mlir::arith::ConstantIndexOp>(rw, loc, 0);
    make<mlir::memref::StoreOp>(rw, loc, v, storage, mlir::ValueRange{zero});
    rw.replaceOp(op, storage);
    return mlir::success();
  }
};

struct AtomicLoadLowering : mlir::OpConversionPattern<AtomicLoadOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AtomicLoadOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    CellAccess c =
        cellAccess(rw, loc, op.getCell().getType(), adaptor.getCell());
    Value v = make<mlir::LLVM::LoadOp>(
        rw, loc, c.storage, c.ptr, c.align, /*isVolatile=*/false,
        /*isNonTemporal=*/false, /*isInvariant=*/false,
        /*isInvariantGroup=*/false, /*isNoundef=*/false,
        llvmOrder(op.getOrder()));
    rw.replaceOp(op, c.fromStorage(rw, loc, v));
    return mlir::success();
  }
};

struct AtomicStoreLowering : mlir::OpConversionPattern<AtomicStoreOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AtomicStoreOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    CellAccess c =
        cellAccess(rw, loc, op.getCell().getType(), adaptor.getCell());
    make<mlir::LLVM::StoreOp>(
        rw, loc, c.toStorage(rw, loc, adaptor.getValue()), c.ptr, c.align,
        /*isVolatile=*/false, /*isNonTemporal=*/false,
        /*isInvariantGroup=*/false, llvmOrder(op.getOrder()));
    rw.eraseOp(op);
    return mlir::success();
  }
};

struct AtomicCasLowering : mlir::OpConversionPattern<AtomicCasOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AtomicCasOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    Location loc = op.getLoc();
    CellAccess c =
        cellAccess(rw, loc, op.getCell().getType(), adaptor.getCell());
    auto pair = make<mlir::LLVM::AtomicCmpXchgOp>(
        rw, loc, c.ptr, c.toStorage(rw, loc, adaptor.getExpected()),
        c.toStorage(rw, loc, adaptor.getDesired()), llvmOrder(op.getSuccess()),
        llvmOrder(op.getFailure()), llvm::StringRef(), c.align);
    Value old = make<mlir::LLVM::ExtractValueOp>(rw, loc, pair,
                                                 llvm::ArrayRef<int64_t>{0});
    rw.replaceOp(op, c.fromStorage(rw, loc, old));
    return mlir::success();
  }
};

// The read-modify-writes. An add or sub lowers by its stated mode (ADR
// 0052, section 2): `wrap` and `proof` are one atomicrmw; `trap` is one
// too, after which the exact result is computed from the old value it
// returns and checked as ordinary trap arithmetic is; `saturate` is a
// compare-and-swap loop, so no wrapped value is ever stored.
struct AtomicRmwLowering : mlir::OpConversionPattern<AtomicRmwOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(AtomicRmwOp op, OpAdaptor adaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    using B = mlir::LLVM::AtomicBinOp;
    Location loc = op.getLoc();
    CellAccess c =
        cellAccess(rw, loc, op.getCell().getType(), adaptor.getCell());
    Value v = c.toStorage(rw, loc, adaptor.getValue());
    bool add = op.getKind() == RmwKind::add;
    bool arith = add || op.getKind() == RmwKind::sub;
    if (arith && op.getOverflow() == OverflowMode::saturate) {
      rw.replaceOp(op, saturatingLoop(rw, op, c, v, add));
      return mlir::success();
    }
    B bin = B::xchg;
    switch (op.getKind()) {
    case RmwKind::swap:
      bin = B::xchg;
      break;
    case RmwKind::add:
      bin = B::add;
      break;
    case RmwKind::sub:
      bin = B::sub;
      break;
    case RmwKind::band:
      bin = B::_and;
      break;
    case RmwKind::bor:
      bin = B::_or;
      break;
    case RmwKind::bxor:
      bin = B::_xor;
      break;
    case RmwKind::min:
      bin = c.isSigned ? B::min : B::umin;
      break;
    case RmwKind::max:
      bin = c.isSigned ? B::max : B::umax;
      break;
    }
    Value old = make<mlir::LLVM::AtomicRMWOp>(rw, loc, bin, c.ptr, v,
                                              llvmOrder(op.getOrder()),
                                              llvm::StringRef(), c.align);
    if (arith && op.getOverflow() == OverflowMode::trap)
      finish(rw, loc, exact(rw, loc, c, old, v, add),
             Repr{2 * c.storage.getWidth(), true},
             mlir::cast<IntType>(op.getType()), OverflowMode::trap);
    rw.replaceOp(op, c.fromStorage(rw, loc, old));
    return mlir::success();
  }

  // `old + v` or `old - v` exactly, at twice the cell's width.
  static Value exact(OpBuilder &b, Location loc, const CellAccess &c, Value old,
                     Value v, bool add) {
    unsigned w = 2 * c.storage.getWidth();
    Value x = resize(b, loc, old, c.isSigned, w);
    Value y = resize(b, loc, v, c.isSigned, w);
    if (add)
      return make<mlir::arith::AddIOp>(b, loc, x, y);
    return make<mlir::arith::SubIOp>(b, loc, x, y);
  }

  // Exchanges the old value for the clamped result until no other task
  // changed the cell in between; the result is the old value it replaced.
  static Value saturatingLoop(mlir::ConversionPatternRewriter &rw,
                              AtomicRmwOp op, const CellAccess &c, Value v,
                              bool add) {
    Location loc = op.getLoc();
    auto t = mlir::cast<IntType>(op.getType());
    Value first = make<mlir::LLVM::LoadOp>(
        rw, loc, c.storage, c.ptr, c.align, false, false, false, false, false,
        mlir::LLVM::AtomicOrdering::monotonic);
    auto loop = make<mlir::scf::WhileOp>(
        rw, loc, mlir::TypeRange{c.storage}, mlir::ValueRange{first},
        [&](OpBuilder &b, Location l, mlir::ValueRange args) {
          Value old = args[0];
          Value next = finish(b, l, exact(b, l, c, old, v, add),
                              Repr{2 * c.storage.getWidth(), true}, t,
                              OverflowMode::saturate);
          auto pair = make<mlir::LLVM::AtomicCmpXchgOp>(
              b, l, c.ptr, old, next, llvmOrder(op.getOrder()),
              readHalf(op.getOrder()), llvm::StringRef(), c.align);
          Value seen = make<mlir::LLVM::ExtractValueOp>(
              b, l, pair, llvm::ArrayRef<int64_t>{0});
          Value done = make<mlir::LLVM::ExtractValueOp>(
              b, l, pair, llvm::ArrayRef<int64_t>{1});
          Value yes = make<mlir::arith::ConstantOp>(b, l, b.getBoolAttr(true));
          Value again = make<mlir::arith::XOrIOp>(b, l, done, yes);
          make<mlir::scf::ConditionOp>(b, l, again, mlir::ValueRange{seen});
        },
        [&](OpBuilder &b, Location l, mlir::ValueRange args) {
          make<mlir::scf::YieldOp>(b, l, args);
        });
    return loop.getResult(0);
  }
};

struct FenceLowering : mlir::OpConversionPattern<FenceOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(FenceOp op, OpAdaptor,
                  mlir::ConversionPatternRewriter &rw) const override {
    make<mlir::LLVM::FenceOp>(rw, op.getLoc(), llvmOrder(op.getOrder()));
    rw.eraseOp(op);
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
                   contract::ObligationOp, contract::HavocOthersOp,
                   contract::ReadsOp, contract::RevealOp>(op);
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

namespace {
// A buffer of recursive values (ADR 0047) is a memref of their LLVM
// struct, which MemRef's lowering loads and stores as any element. MLIR
// lets a memref hold only types that say they may be its elements.
struct StructElement
    : mlir::MemRefElementTypeInterface::ExternalModel<
          StructElement, mlir::LLVM::LLVMStructType> {};
}  // namespace

void loadDialects(mlir::MLIRContext &ctx) {
  ctx.loadDialect<mlir::arith::ArithDialect, mlir::cf::ControlFlowDialect,
                  mlir::func::FuncDialect, mlir::index::IndexDialect,
                  mlir::LLVM::LLVMDialect, mlir::memref::MemRefDialect,
                  mlir::scf::SCFDialect, mlir::async::AsyncDialect>();
  if (!mlir::isa<mlir::MemRefElementTypeInterface>(
          mlir::LLVM::LLVMStructType::getLiteral(&ctx, {})))
    mlir::LLVM::LLVMStructType::attachInterface<StructElement>(ctx);
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

// Spec state (ADR 0058): the storage of each `let spec` local and each
// spec parameter, both marked `pia.spec_state`. IRGen lets code write spec
// state but read it only in contracts, which are gone by now, and in other
// spec writes. So every op that uses spec state, and every op that uses
// one of those, only computes spec state: all of it goes. A call passes
// spec state only for a spec parameter, and those parameters go too, with
// the arguments every call passes for them.
void eraseSpecState(mlir::ModuleOp module) {
  auto specArgs = [](mlir::func::FuncOp f) {
    llvm::BitVector out(f.getNumArguments());
    for (unsigned i = 0; i < f.getNumArguments(); ++i)
      if (f.getArgAttr(i, PiaDialect::getSpecStateAttrName()))
        out.set(i);
    return out;
  };
  auto specResult = [](mlir::func::FuncOp f, unsigned i) {
    return f && static_cast<bool>(
                    f.getResultAttr(i, PiaDialect::getSpecStateAttrName()));
  };
  // A call to a spec function, lemma or axiom only computes spec state.
  auto specOnlyCallee = [&](mlir::func::CallOp call) {
    auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    return f && (f->hasAttr(PiaDialect::getLemmaAttrName()) ||
                 f->hasAttr(PiaDialect::getSpecAttrName()) ||
                 f->hasAttr(PiaDialect::getAxiomAttrName()));
  };
  llvm::SetVector<mlir::Operation *> doomed;
  llvm::SmallVector<Value> work;
  llvm::DenseSet<Value> seen;
  auto push = [&](Value v) {
    if (seen.insert(v).second)
      work.push_back(v);
  };
  module.walk([&](mlir::Operation *op) {
    if (op->hasAttr(PiaDialect::getSpecStateAttrName())) {
      doomed.insert(op);
      for (Value r : op->getResults())
        push(r);
    }
    // A spec field's leaf in a callee's result (ADR 0058).
    if (auto call = mlir::dyn_cast<mlir::func::CallOp>(op)) {
      auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
      for (unsigned i = 0; i < call.getNumResults(); ++i)
        if (specResult(f, i))
          push(call.getResult(i));
    }
  });
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    if (f.isExternal())
      continue;
    llvm::BitVector spec = specArgs(f);
    for (unsigned i : spec.set_bits())
      push(f.getArgument(i));
  }
  // Spec state that a record held moves through structured control flow
  // once records are scalarized (ADR 0058): what a loop or branch carries
  // stays spec state, and the operand that carried it becomes pia.erased.
  llvm::SmallVector<std::pair<mlir::Operation *, unsigned>> erasedOperands;
  while (!work.empty()) {
    Value v = work.pop_back_val();
    for (mlir::OpOperand &use : v.getUses()) {
      mlir::Operation *user = use.getOwner();
      unsigned at = use.getOperandNumber();
      if (doomed.contains(user))
        continue;
      // A spec argument that a spec function computes, as in
      // `f (pick bj i)`: the call goes with the argument it feeds.
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(user)) {
        if (specOnlyCallee(call)) {
          doomed.insert(user);
          for (Value r : user->getResults())
            push(r);
        }
        continue; // otherwise dropped below
      }
      if (mlir::isa<mlir::func::ReturnOp>(user))
        continue; // dropped below, with the result

      if (auto yield = mlir::dyn_cast<mlir::scf::YieldOp>(user)) {
        erasedOperands.push_back({user, at});
        mlir::Operation *parent = yield->getParentOp();
        if (auto loop = mlir::dyn_cast<mlir::scf::ForOp>(parent)) {
          push(loop.getResult(at));
          push(loop.getRegionIterArgs()[at]);
        } else if (mlir::isa<mlir::scf::IfOp, mlir::scf::IndexSwitchOp>(
                       parent)) {
          push(parent->getResult(at));
        } else if (auto loop = mlir::dyn_cast<mlir::scf::WhileOp>(parent)) {
          push(loop.getBeforeArguments()[at]);
        }
        continue;
      }
      if (auto cond = mlir::dyn_cast<mlir::scf::ConditionOp>(user)) {
        erasedOperands.push_back({user, at});
        if (at > 0) {
          auto loop = mlir::cast<mlir::scf::WhileOp>(cond->getParentOp());
          push(loop.getAfterArguments()[at - 1]);
          push(loop.getResult(at - 1));
        }
        continue;
      }
      if (auto loop = mlir::dyn_cast<mlir::scf::ForOp>(user)) {
        if (at >= loop.getNumControlOperands()) {
          unsigned k = at - loop.getNumControlOperands();
          erasedOperands.push_back({user, at});
          push(loop.getRegionIterArgs()[k]);
          push(loop.getResult(k));
        }
        continue;
      }
      if (auto loop = mlir::dyn_cast<mlir::scf::WhileOp>(user)) {
        erasedOperands.push_back({user, at});
        push(loop.getBeforeArguments()[at]);
        continue;
      }
      // A branch on spec state, as in `f (if h then bj.[0] else 0)`: code
      // reads spec state only to compute spec state, so the whole branch
      // goes, and what it yields is spec state.
      if (mlir::isa<mlir::scf::IfOp, mlir::scf::IndexSwitchOp>(user) &&
          at == 0) {
        doomed.insert(user);
        for (Value r : user->getResults())
          push(r);
        continue;
      }
      if (user->getNumRegions() > 0)
        continue;
      doomed.insert(user);
      for (Value r : user->getResults())
        push(r);
    }
  }
  // An op inside a doomed branch goes with the branch, not on its own.
  llvm::SmallVector<mlir::Operation *> nested;
  for (mlir::Operation *op : doomed)
    for (mlir::Operation *p = op->getParentOp(); p; p = p->getParentOp())
      if (doomed.contains(p)) {
        nested.push_back(op);
        break;
      }
  for (mlir::Operation *op : nested)
    doomed.remove(op);
  for (auto [op, at] : erasedOperands) {
    if (doomed.contains(op))
      continue;
    OpBuilder b(op);
    Value v = op->getOperand(at);
    op->setOperand(at, make<ErasedOp>(b, op->getLoc(), v.getType()));
  }
  // The results that are spec fields' leaves, which go below.
  llvm::DenseMap<mlir::Operation *, llvm::BitVector> specResults;
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    llvm::BitVector r(f.getNumResults());
    for (unsigned i = 0; i < f.getNumResults(); ++i)
      if (specResult(f, i))
        r.set(i);
    if (r.any())
      specResults[f] = r;
  }
  // Each call drops the arguments for its callee's spec parameters.
  module.walk([&](mlir::func::CallOp call) {
    auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    if (!f)
      return;
    llvm::BitVector spec = specArgs(f);
    if (spec.any())
      call->eraseOperands(spec);
  });
  for (mlir::Operation *op : doomed)
    op->dropAllUses();
  for (mlir::Operation *op : doomed)
    op->dropAllReferences();
  for (mlir::Operation *op : doomed)
    op->erase();
  // A spec result goes from the function, its returns and its calls,
  // whose uses of it went with the spec state above.
  llvm::SmallVector<mlir::func::CallOp> calls;
  module.walk([&](mlir::func::CallOp call) { calls.push_back(call); });
  for (mlir::func::CallOp call : calls) {
    auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    auto r = f ? specResults.find(f) : specResults.end();
    if (r == specResults.end())
      continue;
    llvm::SmallVector<Type> kept;
    for (unsigned i = 0; i < call.getNumResults(); ++i)
      if (!r->second.test(i))
        kept.push_back(call.getResult(i).getType());
    OpBuilder b(call);
    auto fresh = make<mlir::func::CallOp>(b, call.getLoc(), call.getCallee(),
                                          kept, call.getOperands());
    unsigned k = 0;
    for (unsigned i = 0; i < call.getNumResults(); ++i)
      if (!r->second.test(i))
        call.getResult(i).replaceAllUsesWith(fresh.getResult(k++));
    call.erase();
  }
  for (auto &entry : specResults) {
    auto f = mlir::cast<mlir::func::FuncOp>(entry.first);
    const llvm::BitVector &r = entry.second;
    f.walk([&](mlir::func::ReturnOp ret) { ret->eraseOperands(r); });
    (void)f.eraseResults(r);
  }
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    llvm::BitVector spec = specArgs(f);
    if (spec.none())
      continue;
    // pia.length_of names an argument by position: the fields of a slice
    // of records share the first field's length. When that field is a
    // spec field, the first field kept carries the length instead.
    auto lengthOf = PiaDialect::getLengthOfAttrName();
    auto i64 = mlir::IntegerType::get(module.getContext(), 64);
    llvm::SmallVector<int> newIndex(f.getNumArguments(), -1);
    for (unsigned i = 0, k = 0; i < f.getNumArguments(); ++i)
      if (!spec.test(i))
        newIndex[i] = k++;
    llvm::DenseMap<unsigned, unsigned> carrier; // old carrier -> new one
    for (unsigned i = 0; i < f.getNumArguments(); ++i) {
      if (spec.test(i))
        continue;
      auto shared = f.getArgAttrOfType<mlir::IntegerAttr>(i, lengthOf);
      if (!shared)
        continue;
      unsigned c = shared.getInt();
      if (!spec.test(c)) {
        f.setArgAttr(i, lengthOf, mlir::IntegerAttr::get(i64, newIndex[c]));
        continue;
      }
      auto [it, fresh] = carrier.try_emplace(c, i);
      if (fresh)
        f.removeArgAttr(i, lengthOf);
      else
        f.setArgAttr(i, lengthOf,
                     mlir::IntegerAttr::get(i64, newIndex[it->second]));
    }
    if (f.isExternal()) {
      llvm::SmallVector<Type> inputs;
      llvm::SmallVector<mlir::DictionaryAttr> attrs;
      for (unsigned i = 0; i < f.getNumArguments(); ++i)
        if (!spec.test(i)) {
          inputs.push_back(f.getFunctionType().getInput(i));
          attrs.push_back(f.getArgAttrDict(i));
        }
      f.setType(mlir::FunctionType::get(module.getContext(), inputs,
                                        f.getFunctionType().getResults()));
      f.setAllArgAttrs(attrs);
      continue;
    }
    (void)f.eraseArguments(spec);
  }
}

void eraseContracts(mlir::ModuleOp module) {
  // A generic's proof over sorts (ADR 0043) is for the verifier only.
  for (auto f : llvm::make_early_inc_range(module.getOps<mlir::func::FuncOp>()))
    if (f->hasAttr("pia.generic_proof")) f.erase();
  // A constant of `Target` used in code, such as `Target.page_size`, is the
  // value its model gives for the target compiled for (ADR 0049): the
  // model's definition is a constant, which takes the call's place.
  module.walk([&](mlir::func::CallOp call) {
    auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
    if (!f)
      return;
    auto of = f->getAttrOfType<mlir::StringAttr>("pia.target_value");
    if (!of)
      return;
    auto def = module.lookupSymbol<mlir::func::FuncOp>(of.getValue());
    if (!def || def.getBody().empty())
      return;
    auto ret = mlir::dyn_cast<mlir::func::ReturnOp>(
        def.getBody().front().getTerminator());
    if (!ret || ret.getNumOperands() != 1 || call.getNumResults() != 1)
      return;
    // The value and the ops it is computed from, such as a literal and
    // its conversion, all without regions or block arguments.
    mlir::OpBuilder b(call);
    mlir::IRMapping map;
    std::function<Value(Value)> copy = [&](Value v) -> Value {
      if (Value done = map.lookupOrNull(v))
        return done;
      mlir::Operation *op = v.getDefiningOp();
      if (!op || op->getNumRegions() != 0 || mlir::isa<mlir::func::CallOp>(op))
        return Value();
      for (Value o : op->getOperands())
        if (!copy(o))
          return Value();
      mlir::Operation *c = b.clone(*op, map);
      return c->getResult(mlir::cast<mlir::OpResult>(v).getResultNumber());
    };
    Value v = copy(ret.getOperand(0));
    if (!v || v.getType() != call.getResult(0).getType())
      return;
    call.getResult(0).replaceAllUsesWith(v);
    call.erase();
  });
  // An imported function's body is its interface's contract, for the
  // verifier. The code is in its module's object file, so what remains is
  // a declaration of the module's link symbol (ADR 0039).
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    auto from = f->getAttrOfType<mlir::StringAttr>(PiaDialect::getImportAttrName());
    if (!from) continue;
    // An imported lemma or spec function has no code in its module: it is
    // erased here with the local ones, calls and all.
    if (auto ghost = f->getAttrOfType<mlir::StringAttr>("pia.import_ghost")) {
      f->setAttr(ghost.getValue() == "spec"    ? PiaDialect::getSpecAttrName()
                 : ghost.getValue() == "lemma" ? PiaDialect::getLemmaAttrName()
                                               : PiaDialect::getAxiomAttrName(),
                 mlir::UnitAttr::get(module.getContext()));
      f->removeAttr(PiaDialect::getImportAttrName());
      continue;
    }
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
  // What only feeds a contract never runs, so it goes with the contract,
  // calls included: a contract evaluates both sides of `&&`, so code kept
  // for one could load out of bounds, and a call to another module's
  // function, a declaration here, would otherwise stay (it is not known to
  // be pure). An op is contract-only when each of its uses is in a
  // contract statement or in a contract-only op. Ops that write are kept.
  llvm::SmallPtrSet<mlir::Operation *, 32> contractOnly;
  llvm::SmallPtrSet<mlir::Operation *, 32> isStatement(statements.begin(),
                                                       statements.end());
  auto insideOnly = [&](mlir::Operation *user) {
    for (mlir::Operation *p = user; p; p = p->getParentOp())
      if (isStatement.count(p) || contractOnly.count(p)) return true;
    return false;
  };
  // Whether erasing `op` could lose an effect: a write, an allocation, or
  // a call that may write, which is one that takes a buffer (an `inout`
  // slice) or is inside a loop or branch being erased with it, unless it
  // calls a spec function. A loop whose results only a contract reads,
  // such as an insertion sort's inner loop, still moves elements.
  auto writes = [&](mlir::Operation *op) {
    bool w = false;
    op->walk([&](mlir::Operation *in) {
      if (auto e = mlir::dyn_cast<mlir::MemoryEffectOpInterface>(in))
        if (e.hasEffect<mlir::MemoryEffects::Write>() ||
            e.hasEffect<mlir::MemoryEffects::Allocate>() ||
            e.hasEffect<mlir::MemoryEffects::Free>())
          w = true;
      if (mlir::isa<StoreOp>(in)) w = true;
      if (auto call = mlir::dyn_cast<mlir::func::CallOp>(in)) {
        auto f = module.lookupSymbol<mlir::func::FuncOp>(call.getCallee());
        bool spec = f && (f->hasAttr(PiaDialect::getSpecAttrName()) ||
                          f->hasAttr(PiaDialect::getLemmaAttrName()));
        bool buffers = llvm::any_of(call.getOperandTypes(), [](Type t) {
          return mlir::isa<ArrayType, SliceType>(t);
        });
        if (!spec && (in != op || buffers)) w = true;
      }
    });
    return w;
  };
  for (bool changed = true; changed;) {
    changed = false;
    module.walk([&](mlir::Operation *op) {
      if (contractOnly.count(op) || isStatement.count(op)) return;
      if (op->getNumResults() == 0 || op->use_empty()) return;
      if (op->hasTrait<mlir::OpTrait::IsTerminator>()) return;
      if (mlir::isa<mlir::func::FuncOp>(op)) return;
      for (Value r : op->getResults())
        for (mlir::Operation *user : r.getUsers())
          if (!insideOnly(user)) return;
      if (writes(op)) return;
      contractOnly.insert(op);
      changed = true;
    });
  }
  // Outermost first, so a feeder inside another goes with it.
  llvm::SmallVector<mlir::Operation *> feeders;
  module.walk<mlir::WalkOrder::PreOrder>([&](mlir::Operation *op) {
    if (!contractOnly.count(op)) return mlir::WalkResult::advance();
    feeders.push_back(op);
    return mlir::WalkResult::skip();
  });
  for (mlir::Operation *op : statements) op->erase();
  // Users come after definitions, so the last goes first.
  for (mlir::Operation *op : llvm::reverse(feeders))
    if (op->use_empty()) op->erase();
  eraseSpecState(module);
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
      if (isSpecOnly(ft.getInput(i)) || isSpecBuffer(ft.getInput(i)))
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
    // A store into a spec-only field's buffer writes what nothing reads.
    // The store that empties an element moved out of a buffer of boxes
    // stays: the program may read the element's length (ADR 0048,
    // section 6).
    f.walk([&](StoreOp store) {
      if (isSpecBuffer(store.getBuffer().getType()))
        spec.push_back(store);
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

// The entries of each box descriptor (ADR 0046, the cache-line amendment):
// for each requirement, a function that takes the object's address and
// the requirement's other arguments, loads the object's fields from their
// offsets, and calls the type's thunk, the Pia function that calls the
// requirement on a value. Named `<descriptor>$<k>`.
static LogicalResult addBoxEntries(mlir::ModuleOp module) {
  OpBuilder b(module.getContext());
  auto ptr = mlir::LLVM::LLVMPointerType::get(module.getContext());
  llvm::SmallVector<mlir::LLVM::GlobalOp> descriptors;
  for (auto g : module.getOps<mlir::LLVM::GlobalOp>())
    if (g->hasAttr("pia.box_thunks"))
      descriptors.push_back(g);
  for (mlir::LLVM::GlobalOp g : descriptors) {
    auto thunks = g->getAttrOfType<mlir::ArrayAttr>("pia.box_thunks");
    auto leaves = g->getAttrOfType<mlir::ArrayAttr>("pia.box_leaves");
    auto offsets = g->getAttrOfType<mlir::DenseI64ArrayAttr>("pia.box_offsets");
    Location loc = g.getLoc();
    for (auto [k, t] : llvm::enumerate(thunks)) {
      llvm::StringRef name = mlir::cast<mlir::StringAttr>(t).getValue();
      auto thunk = module.lookupSymbol<mlir::func::FuncOp>(name);
      if (!thunk)
        return g.emitError() << "the box's thunk '" << name << "' is missing";
      mlir::FunctionType ft = thunk.getFunctionType();
      unsigned n = leaves.size();
      bool same = ft.getNumInputs() >= n;
      for (unsigned i = 0; same && i < n; ++i)
        same =
            ft.getInput(i) == mlir::cast<mlir::TypeAttr>(leaves[i]).getValue();
      if (!same)
        return g.emitError() << "the box's thunk '" << name
                             << "' does not take the object's fields";
      llvm::SmallVector<Type> inputs{ptr};
      for (Type a : ft.getInputs().drop_front(n))
        inputs.push_back(a);
      b.setInsertionPointToEnd(module.getBody());
      auto entry = make<mlir::func::FuncOp>(
          b, loc, (g.getSymName() + "$" + llvm::Twine(k)).str(),
          b.getFunctionType(inputs, ft.getResults()));
      entry.setPrivate();
      mlir::Block *body = entry.addEntryBlock();
      b.setInsertionPointToStart(body);
      llvm::SmallVector<Value> callArgs;
      for (unsigned i = 0; i < n; ++i)
        callArgs.push_back(make<mlir::LLVM::LoadOp>(
            b, loc, mlir::cast<mlir::TypeAttr>(leaves[i]).getValue(),
            bytesAfter(b, loc, body->getArgument(0), offsets[i])));
      for (unsigned i = 1; i < body->getNumArguments(); ++i)
        callArgs.push_back(body->getArgument(i));
      auto call = make<mlir::func::CallOp>(b, loc, thunk, callArgs);
      make<mlir::func::ReturnOp>(b, loc, call.getResults());
    }
  }
  return mlir::success();
}

// Defines each box descriptor once its entries are LLVM functions: the
// object's size and alignment, its drop (none yet), and the entries.
static void defineBoxDescriptors(mlir::ModuleOp module) {
  mlir::MLIRContext *ctx = module.getContext();
  OpBuilder b(ctx);
  auto ptr = mlir::LLVM::LLVMPointerType::get(ctx);
  auto i64 = b.getI64Type();
  for (auto g : module.getOps<mlir::LLVM::GlobalOp>()) {
    auto thunks = g->getAttrOfType<mlir::ArrayAttr>("pia.box_thunks");
    if (!thunks)
      continue;
    Location loc = g.getLoc();
    mlir::Block *init = b.createBlock(&g.getInitializerRegion());
    b.setInsertionPointToStart(init);
    Value v = make<mlir::LLVM::UndefOp>(b, loc, g.getType());
    auto word = [&](llvm::StringRef attr) -> Value {
      return make<mlir::LLVM::ConstantOp>(
          b, loc, i64,
          b.getI64IntegerAttr(
              g->getAttrOfType<mlir::IntegerAttr>(attr).getInt()));
    };
    v = make<mlir::LLVM::InsertValueOp>(b, loc, v, word("pia.box_size"),
                                        llvm::ArrayRef<int64_t>{0});
    v = make<mlir::LLVM::InsertValueOp>(b, loc, v, word("pia.box_align"),
                                        llvm::ArrayRef<int64_t>{1});
    v = make<mlir::LLVM::InsertValueOp>(b, loc, v,
                                        make<mlir::LLVM::ZeroOp>(b, loc, ptr),
                                        llvm::ArrayRef<int64_t>{2});
    for (size_t k = 0; k < thunks.size(); ++k) {
      Value f = make<mlir::LLVM::AddressOfOp>(
          b, loc, ptr, (g.getSymName() + "$" + llvm::Twine(k)).str());
      v = make<mlir::LLVM::InsertValueOp>(
          b, loc, v, f, llvm::ArrayRef<int64_t>{static_cast<int64_t>(3 + k)});
    }
    make<mlir::LLVM::ReturnOp>(b, loc, v);
    g.setLinkage(mlir::LLVM::Linkage::Internal);
    for (llvm::StringRef a :
         {"pia.box_thunks", "pia.box_leaves", "pia.box_offsets", "pia.box_size",
          "pia.box_align"})
      g->removeAttr(a);
  }
}

// A `spread` (ADR 0060) reaches codegen as an `scf.for` marked
// `pia.spread`, so that the verifier sees an ordinary loop. Its iterations
// own disjoint cells, which the verifier proved, so here it becomes an
// `scf.parallel`, which MLIR's async lowering runs on all cores.
static void lowerSpreads(mlir::ModuleOp module) {
  llvm::SmallVector<mlir::scf::ForOp> spreads;
  module.walk([&](mlir::scf::ForOp f) {
    if (f->hasAttr("pia.spread"))
      spreads.push_back(f);
  });
  for (mlir::scf::ForOp f : spreads) {
    mlir::OpBuilder b(f);
    auto par = make<mlir::scf::ParallelOp>(
        b, f.getLoc(), mlir::ValueRange{f.getLowerBound()},
        mlir::ValueRange{f.getUpperBound()}, mlir::ValueRange{f.getStep()});
    mlir::Block *src = f.getBody();
    mlir::Block *dst = par.getBody();
    src->getArgument(0).replaceAllUsesWith(par.getInductionVars()[0]);
    dst->getOperations().splice(mlir::Block::iterator(dst->getTerminator()),
                                src->getOperations(), src->begin(),
                                std::prev(src->end()));
    f.erase();
  }
}

LogicalResult lowerToCore(mlir::ModuleOp module) {
  mlir::MLIRContext *ctx = module.getContext();
  loadDialects(*ctx);

  // An array result becomes an output buffer its caller makes.
  if (mlir::failed(arrayResultsToBuffers(module)))
    return mlir::failure();

  // A buffer whose elements are slices becomes a buffer of addresses and
  // one of lengths (ADR 0048, section 4).
  if (mlir::failed(splitSliceBuffers(module)))
    return mlir::failure();

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
  // Recursive values' layouts (ADR 0047), from the datatypes, which make
  // no code themselves.
  types.addDatatypes(module);
  for (auto d : llvm::make_early_inc_range(module.getOps<DatatypeOp>()))
    d.erase();
  // Foreign functions (#55): each C symbol a `pia.foreign` calls gets a
  // private declaration with C types, marked `pia.c`. A Pia declaration
  // with the same name as its symbol is renamed out of the way.
  {
    llvm::SmallVector<ForeignOp> foreign;
    module.walk([&](ForeignOp op) { foreign.push_back(op); });
    std::set<std::string> declared;
    // A symbol's named parameters if it is variadic (ADR 0051), and
    // whether it is @deref, so that every call of it agrees.
    std::map<std::string, std::pair<std::optional<int64_t>, bool>> shapeOf;
    for (ForeignOp op : foreign) {
      std::string sym = op.getSymbol().str();
      std::optional<int64_t> named;
      if (auto v = op->getAttrOfType<mlir::IntegerAttr>("pia.variadic"))
        named = v.getInt();
      bool deref = op->hasAttr("pia.deref");
      if (auto [it, fresh] = shapeOf.try_emplace(sym, named, deref);
          !fresh && it->second.first != named)
        return op.emitError()
               << "the C symbol '" << sym
               << "' is declared both with and without @variadic, or with "
                  "different numbers of named parameters";
      else if (!fresh && it->second.second != deref)
        return op.emitError() << "the C symbol '" << sym
                              << "' is declared both with and without @deref";
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
      // C extends small integers at the call (Apple arm64, and x86_64
      // System V as clang and GCC compile it).
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
      // A C variadic function is an llvm.func with `...`, because
      // func.func cannot say so, and the calling convention differs:
      // Apple arm64 passes the variadic arguments on the stack, and
      // x86_64 System V counts vector registers in %al.
      // A @deref function returns a pointer in C, so it is an llvm.func
      // too, and its call loads the result through it.
      if (named || deref) {
        if (named)
          args.resize(*named);
        Type result = results.empty() ? Type(mlir::LLVM::LLVMVoidType::get(ctx))
                                      : results.front();
        if (deref)
          result = ptr;
        auto decl = make<mlir::LLVM::LLVMFuncOp>(
            b, op.getLoc(), sym,
            mlir::LLVM::LLVMFunctionType::get(result, args,
                                              /*isVarArg=*/named.has_value()));
        decl->setAttr("pia.c", b.getUnitAttr());
        for (auto [i, a] : llvm::enumerate(op.getArgs()))
          if (!named || static_cast<int64_t>(i) < *named)
            if (auto e = ext(a.getType()))
              decl.setArgAttr(i, *e, b.getUnitAttr());
        if (!deref)
          for (Type t : op.getResultTypes())
            if (auto e = ext(t))
              decl.setResultAttr(0, *e, b.getUnitAttr());
        continue;
      }
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
  target.addDynamicallyLegalOp<mlir::func::CallOp, mlir::func::ReturnOp,
                               mlir::func::ConstantOp,
                               mlir::func::CallIndirectOp>(
      [&](mlir::Operation *op) { return types.isLegal(op); });

  mlir::RewritePatternSet patterns(ctx);
  patterns
      .add<ConstantLowering, ArithLowering<AddOp, Arith::Add>,
           ArithLowering<SubOp, Arith::Sub>, ArithLowering<MulOp, Arith::Mul>,
           ArithLowering<DivOp, Arith::Div>, ArithLowering<RemOp, Arith::Rem>,
           ArithLowering<BAndOp, Arith::BAnd>, ArithLowering<BOrOp, Arith::BOr>,
           ArithLowering<BXorOp, Arith::BXor>, ArithLowering<ShlOp, Arith::Shl>,
           ArithLowering<ShrOp, Arith::Shr>, BitLowering<ClzOp>,
           BitLowering<CtzOp>, BitLowering<PopcountOp>, BitLowering<BSwapOp>,
           RotateLowering<RotlOp>, RotateLowering<RotrOp>, ConvertLowering,
           CmpLowering, ToIndexLowering, FromIndexLowering, LenLowering,
           LoadLowering, StoreLowering, SliceLowering, EmptyLowering,
           ErasedLowering, RegionLowering, CopyLowering, ViewLowering,
           AtAddressLowering, AddressLowering, AbortLowering,
           ConstArrayLowering, EmbedLowering, ForeignLowering, RecMakeLowering,
           RecTagLowering, RecPayloadLowering, FunctionConstantLowering,
           CallIndirectLowering, BoxPackLowering, BoxCallLowering>(types, ctx);
  // Floats and integers (M11).
  patterns.add<IntToFloatLowering, FloatToIntLowering,
               BitcastLowering<ToBitsOp>, BitcastLowering<FromBitsOp>>(types,
                                                                       ctx);
  // Atomics (ADR 0052).
  patterns.add<AtomicNewLowering, AtomicLoadLowering, AtomicStoreLowering,
               AtomicCasLowering, AtomicRmwLowering, FenceLowering>(types, ctx);
  mlir::populateFunctionOpInterfaceTypeConversionPattern<mlir::func::FuncOp>(
      patterns, types);
  mlir::populateCallOpTypeConversionPattern(patterns, types);
  mlir::populateReturnOpTypeConversionPattern(patterns, types);
  mlir::scf::populateSCFStructuralTypeConversionsAndLegality(types, patterns,
                                                             target);
  if (mlir::failed(
          mlir::applyPartialConversion(module, target, std::move(patterns))))
    return mlir::failure();
  if (mlir::failed(addBoxEntries(module)))
    return mlir::failure();
  // Spreads placed on the GPU become kernels and shim calls first; the
  // rest run on all cores (ADR 0068, step 3).
  if (mlir::failed(pia::gpu::lowerPlacedSpreads(module)))
    return mlir::failure();
  lowerSpreads(module);
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
  // No C entry point, as for a function that takes or returns a
  // recursive value by value; only its link symbol, if it has one.
  bool noC = false;
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
// arm64 ABI requires, and as clang and GCC do for x86_64 System V.
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

LogicalResult buildEntry(mlir::ModuleOp module, const Entry &entryInfo) {
  mlir::MLIRContext *ctx = module.getContext();
  // A spec-only field's buffer is left out (ADR 0041), so when the fields
  // of a slice of records share its length, the first field kept takes the
  // length instead, and the rest share that one.
  Entry e = entryInfo;
  for (unsigned i = 0; i < e.lengthOf.size(); ++i) {
    if (!e.argErased[i]) continue;
    int taker = -1;
    for (unsigned j = i + 1; j < e.lengthOf.size(); ++j) {
      if (e.lengthOf[j] != int(i)) continue;
      if (taker < 0) {
        taker = int(j);
        e.lengthOf[j] = -1;
      } else {
        e.lengthOf[j] = taker;
      }
    }
  }
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
      // A spec-only field's buffer (ADR 0041) is never read or written,
      // so it is an empty descriptor.
      if (mlir::isa<mlir::MemRefType>(t)) {
        Value null = make<mlir::LLVM::ZeroOp>(
            b, e.loc, mlir::LLVM::LLVMPointerType::get(ctx));
        operands.append({null, null, c64(0), c64(0), c64(1)});
        continue;
      }
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
  // A caller that did not apply the lowerings, such as the REPL's JIT,
  // compiles every body (ADR 0065).
  if (mlir::failed(applyLowerings(module, /*enabled=*/false)))
    return mlir::failure();
  bool lowered = takeLoweredMark(module);

  std::vector<Entry> entries;
  for (auto f : llvm::make_early_inc_range(module.getOps<mlir::func::FuncOp>())) {
    Entry e{f.getSymName().str(), cName(f.getSymName()), f.getFunctionType(),
            {}, false, f.getLoc()};
    e.internal = (kInternalPrefix + e.name).str();
    // The name the module's interfaces give it (#204): plain unless they
    // list several overloads of it.
    std::string linkName = f.getSymName().str();
    if (auto n = f->getAttrOfType<mlir::StringAttr>("pia.link_name")) {
      linkName = n.getValue().str();
      e.cname = cName(linkName);
      f->removeAttr("pia.link_name");
    }
    // An exported function's entry point is named by its module unless its
    // interface is `@abi(c)`, and its Pia calling convention stays
    // reachable, for importers, under its link symbol (ADR 0039).
    auto exported =
        f->getAttrOfType<mlir::StringAttr>(PiaDialect::getExportAttrName());
    if (exported && !exported.getValue().empty()) {
      if (exportsOnly) {
        e.internal = linkSymbol(exported.getValue(), linkName);
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
    // A recursive value (ADR 0047) has no C type yet: a function that
    // takes or returns one by value has no entry point, and C passes a
    // buffer of them instead.
    auto byValue = [](Type t) { return mlir::isa<mlir::LLVM::LLVMStructType>(t); };
    if (llvm::any_of(f.getFunctionType().getInputs(), byValue) ||
        llvm::any_of(f.getFunctionType().getResults(), byValue)) {
      // A module's export keeps its link symbol, for importers.
      if (!e.linked) {
        f.setPrivate();
        continue;
      }
      e.noC = true;
    }
    if (mlir::failed(mlir::SymbolTable::replaceAllSymbolUses(
            f, mlir::StringAttr::get(ctx, e.internal), module)))
      return mlir::failure();
    f.setSymName(e.internal);
    f.setPrivate();
    entries.push_back(std::move(e));
  }

  mlir::PassManager pm(ctx);
  // A spread runs on MLIR's async runtime, a trusted v0 (ADR 0060): the
  // range is split into blocks, at least one iteration each, on as many
  // workers as the runtime has.
  bool parallel = false;
  module.walk([&](mlir::scf::ParallelOp) { parallel = true; });
  if (parallel) {
    mlir::AsyncParallelForPassOptions par;
    par.asyncDispatch = true;
    par.numWorkerThreads = -1;
    par.minTaskSize = 1;
    pm.addPass(mlir::createAsyncParallelForPass(par));
    pm.addPass(mlir::createAsyncToAsyncRuntimePass());
    pm.addPass(mlir::createAsyncRuntimeRefCountingPass());
    pm.addPass(mlir::createAsyncRuntimeRefCountingOptPass());
    pm.addPass(mlir::createConvertAsyncToLLVMPass());
  }
  // What a lowering's MLIR uses beyond the core dialects goes down to them
  // first (ADR 0065).
  if (lowered)
    addLoweringPasses(pm);
  pm.addPass(mlir::createSCFToControlFlowPass());
  pm.addPass(mlir::createConvertControlFlowToLLVMPass());
  pm.addPass(mlir::createArithToLLVMConversionPass());
  pm.addPass(mlir::createConvertIndexToLLVMPass());
  pm.addPass(mlir::createFinalizeMemRefToLLVMConversionPass());
  pm.addPass(mlir::createConvertFuncToLLVMPass());
  pm.addPass(mlir::createReconcileUnrealizedCastsPass());
  if (mlir::failed(pm.run(module))) return mlir::failure();
  defineBoxDescriptors(module);

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
    if (!e.noC && mlir::failed(buildEntry(module, e)))
      return mlir::failure();
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

// The features x86-64-v3 adds to x86-64-v2, which an x86_64 CPU must have.
constexpr const char *kX86V3Features =
    "+avx2,+bmi,+bmi2,+f16c,+fma,+lzcnt,+movbe";

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
  // Floats are strict IEEE 754 by default (ADR 0004, ADR 0012). LLVM fuses
  // a multiply and an add into an FMA only when both carry the `contract`
  // fast-math flag, which IRGen never sets, and it never flushes
  // subnormals unless a function asks for it.
  std::unique_ptr<llvm::TargetMachine> tm(target->createTargetMachine(
      triple, options.cpu, "", llvm::TargetOptions(), llvm::Reloc::PIC_,
      std::nullopt, level));
  if (!tm) {
    error = "cannot create a target machine for " + options.triple;
    return nullptr;
  }
  // x86-64-v3 is the oldest x86_64 CPU Pia supports (ADR 0049): the
  // vectoriser and the cost model assume AVX2, so code for an older CPU
  // would be slower than promised, or would not run on the machine it was
  // compiled for.
  if (triple.getArch() == llvm::Triple::x86_64 &&
      !tm->getMCSubtargetInfo().checkFeatures(kX86V3Features)) {
    error = "the x86_64 CPU '" + options.cpu +
            "' is older than x86-64-v3, the oldest Pia supports (it needs "
            "AVX2, BMI1, BMI2, F16C, FMA, LZCNT and MOVBE)";
    return nullptr;
  }
  return tm;
}

}  // namespace

std::string witnessSymbol(const std::string &module, const std::string &iface,
                          llvm::StringRef text) {
  std::array<uint8_t, 32> hash = llvm::SHA256::hash(
      llvm::ArrayRef<uint8_t>(text.bytes_begin(), text.bytes_end()));
  // RFC 4648 base32 of the first 16 bytes, lowercase, without padding.
  static constexpr char kAlphabet[] = "abcdefghijklmnopqrstuvwxyz234567";
  std::string code;
  unsigned buffer = 0, bits = 0;
  for (size_t i = 0; i < 16; ++i) {
    buffer = (buffer << 8) | hash[i];
    bits += 8;
    for (; bits >= 5; bits -= 5)
      code += kAlphabet[(buffer >> (bits - 5)) & 31];
  }
  if (bits > 0)
    code += kAlphabet[(buffer << (5 - bits)) & 31];
  // Dots become '$', as in link symbols (`__pia$Image$Pixels$mix`).
  std::string path = module;
  std::replace(path.begin(), path.end(), '.', '$');
  return "pia$w$" + path + "$" + iface + "$" + code;
}

namespace {

// Defines the witnesses the module provides and references the ones it
// requires. A reference is a pointer kept by llvm.used, so neither the
// optimiser nor the linker's dead stripping can drop it: the linker, or
// dyld for a shared library, must find the exact hash it names.
void addWitnesses(llvm::Module &m, const Options &options) {
  llvm::Type *byte = llvm::Type::getInt8Ty(m.getContext());
  std::vector<llvm::GlobalValue *> used;
  for (const std::string &name : options.providedWitnesses) {
    if (m.getNamedGlobal(name))
      continue;
    auto *w = new llvm::GlobalVariable(m, byte, /*isConstant=*/true,
                                       llvm::GlobalValue::ExternalLinkage,
                                       llvm::ConstantInt::get(byte, 0), name);
    used.push_back(w);
  }
  for (const std::string &name : options.requiredWitnesses) {
    llvm::GlobalVariable *w = m.getNamedGlobal(name);
    if (!w)
      w = new llvm::GlobalVariable(m, byte, /*isConstant=*/true,
                                   llvm::GlobalValue::ExternalLinkage, nullptr,
                                   name);
    auto *ref = new llvm::GlobalVariable(
        m, llvm::PointerType::getUnqual(m.getContext()), /*isConstant=*/true,
        llvm::GlobalValue::PrivateLinkage, w, "pia$uses$" + name.substr(6));
    used.push_back(ref);
  }
  // The certificate, read by `pia-cert` from the object, never by code.
  if (!options.certificate.empty()) {
    llvm::Constant *bytes = llvm::ConstantDataArray::getString(
        m.getContext(), options.certificate, /*AddNull=*/false);
    auto *cert = new llvm::GlobalVariable(
        m, bytes->getType(), /*isConstant=*/true,
        llvm::GlobalValue::PrivateLinkage, bytes, "pia$cert");
    cert->setSection(cert::sectionFor(options.triple));
    cert->setAlignment(llvm::Align(4));
    used.push_back(cert);
  }
  if (!used.empty())
    llvm::appendToUsed(m, used);
}

// Populates embedded binary blobs (ADR 0070) directly as LLVM
// ConstantDataArrays, bypassing per-element MLIR attributes.
void addEmbeds(llvm::Module &m, const Options &options) {
  if (options.embeds.empty())
    return;
  llvm::LLVMContext &ctx = m.getContext();
  std::vector<llvm::GlobalValue *> used;
  for (const syntax::EmbeddedBlob &blob : options.embeds) {
    llvm::GlobalVariable *g = m.getNamedGlobal(blob.symbol);
    if (!g && !blob.isExternal && blob.section.empty())
      continue;
    llvm::Constant *data =
        llvm::ConstantDataArray::get(ctx, llvm::ArrayRef<uint8_t>(blob.bytes));
    auto linkage = blob.isExternal ? llvm::GlobalValue::ExternalLinkage
                                   : llvm::GlobalValue::PrivateLinkage;
    if (g) {
      g->setInitializer(data);
      g->setConstant(true);
      g->setLinkage(linkage);
    } else {
      g = new llvm::GlobalVariable(m, data->getType(), /*isConstant=*/true,
                                   linkage, data, blob.symbol);
    }
    g->setAlignment(llvm::Align(blob.align));
    if (!blob.section.empty()) {
      g->setSection(blob.section);
      used.push_back(g);
    }
    if (blob.emitLenSymbol) {
      std::string lenName = blob.symbol + "_len";
      if (!m.getNamedGlobal(lenName)) {
        llvm::Type *i64 = llvm::Type::getInt64Ty(ctx);
        auto *lenVar = new llvm::GlobalVariable(
            m, i64, /*isConstant=*/true, llvm::GlobalValue::ExternalLinkage,
            llvm::ConstantInt::get(i64, blob.bytes.size()), lenName);
        lenVar->setAlignment(llvm::Align(8));
      }
    }
  }
  if (!used.empty())
    llvm::appendToUsed(m, used);
}

} // namespace

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
  // Kernels placed on the GPU are built in the background from the
  // moment the program loads (ADR 0068, section 9). The constructor is
  // internal, so each object keeps its own.
  if (llvm::Function *warm = m->getFunction(pia::gpu::kWarmSymbol)) {
    warm->setLinkage(llvm::GlobalValue::InternalLinkage);
    llvm::appendToGlobalCtors(*m, warm, /*Priority=*/65535);
  }
  m->setTargetTriple(tm->getTargetTriple());
  m->setDataLayout(tm->createDataLayout());
  auto optimise =
      mlir::makeOptimizingTransformer(options.optLevel, 0, tm.get());
  if (llvm::Error e = optimise(m.get())) {
    error = llvm::toString(std::move(e));
    return nullptr;
  }
  addWitnesses(*m, options);
  addEmbeds(*m, options);
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
