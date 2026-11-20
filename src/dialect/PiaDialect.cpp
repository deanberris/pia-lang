#include "dialect/PiaDialect.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/ADT/TypeSwitch.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "mlir/IR/OpImplementation.h"

using namespace mlir;
using namespace pia;

static Type elementTypeOf(Type buffer) {
  if (auto a = dyn_cast<ArrayType>(buffer)) return a.getElementType();
  return cast<SliceType>(buffer).getElementType();
}

// custom<ElementType>: pia.load and pia.store print only the buffer type; the
// element type follows from it, so it is never printed.
static ParseResult parseElementType(OpAsmParser &parser, Type buffer,
                                    Type &element) {
  if (!isa<ArrayType, SliceType>(buffer))
    return parser.emitError(parser.getCurrentLocation(),
                            "expected a !pia.array or !pia.slice type, got ")
           << buffer;
  element = elementTypeOf(buffer);
  return success();
}

static void printElementType(OpAsmPrinter &, Operation *, Type, Type) {}

#include "dialect/PiaDialect.cpp.inc"
#include "dialect/PiaEnums.cpp.inc"

#define GET_TYPEDEF_CLASSES
#include "dialect/PiaTypes.cpp.inc"

#define GET_OP_CLASSES
#include "dialect/Pia.cpp.inc"

namespace {

// Range bounds are compared as 128-bit signed integers.
constexpr unsigned kBoundWidth = 128;

APInt widen(const APInt &v) { return v.sextOrTrunc(kBoundWidth); }

// The smallest and largest values Pia's integer types can hold: i64's
// minimum and u64's maximum.
APInt minBound() { return APInt::getSignedMinValue(64).sext(kBoundWidth); }
APInt maxBound() { return APInt::getMaxValue(64).zext(kBoundWidth); }

// Prints the two 64-bit ranges, whose bounds are long, as `!usize` and
// `!isize`. They are also u64 and i64: Pia's targets are all 64-bit. MLIR
// would add `_` to an alias ending in a digit, so the narrower types keep
// their short `<0, 255>` spelling instead of `!u8_`.
struct PiaOpAsmInterface : public OpAsmDialectInterface {
  using OpAsmDialectInterface::OpAsmDialectInterface;

  AliasResult getAlias(Type type, raw_ostream &os) const override {
    auto it = dyn_cast<IntType>(type);
    if (!it) return AliasResult::NoAlias;
    APInt lo = widen(it.getLo()), hi = widen(it.getHi());
    if (lo.isZero() && hi == maxBound()) {
      os << "usize";
      return AliasResult::FinalAlias;
    }
    if (lo == minBound() &&
        hi == APInt::getSignedMaxValue(64).sext(kBoundWidth)) {
      os << "isize";
      return AliasResult::FinalAlias;
    }
    return AliasResult::NoAlias;
  }
};

}  // namespace

//===----------------------------------------------------------------------===//
// Dialect
//===----------------------------------------------------------------------===//

void PiaDialect::initialize() {
  registerTypes();
  addInterfaces<PiaOpAsmInterface>();
  addOperations<
#define GET_OP_LIST
#include "dialect/Pia.cpp.inc"
      >();
}

Operation *PiaDialect::materializeConstant(OpBuilder &builder, Attribute value,
                                           Type type, Location loc) {
  auto intAttr = dyn_cast<IntegerAttr>(value);
  if (!intAttr) return nullptr;
#if LLVM_VERSION_MAJOR >= 21
  if (isa<IntType>(type)) return ConstantOp::create(builder, loc, type, intAttr);
  if (arith::ConstantOp::isBuildableWith(value, type))
    return arith::ConstantOp::create(builder, loc, type, cast<TypedAttr>(value));
#else
  if (isa<IntType>(type)) return builder.create<ConstantOp>(loc, type, intAttr);
  if (arith::ConstantOp::isBuildableWith(value, type))
    return builder.create<arith::ConstantOp>(loc, type, cast<TypedAttr>(value));
#endif
  return nullptr;
}

void PiaDialect::registerTypes() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "dialect/PiaTypes.cpp.inc"
      >();
}

// `{pia.modifiers = "borrowed in mutable"}`: ownership, access, mutability,
// each optional, in that order (docs/grammar.md, ADR 0005).
LogicalResult PiaDialect::verifyRegionArgAttribute(Operation *op, unsigned,
                                                   unsigned argIndex,
                                                   NamedAttribute attr) {
  if (attr.getName() != getModifiersAttrName())
    return op->emitError() << "unknown pia argument attribute '"
                           << attr.getName() << "'";
  auto str = dyn_cast<StringAttr>(attr.getValue());
  if (!str)
    return op->emitError() << "'" << getModifiersAttrName()
                           << "' on argument " << argIndex
                           << " must be a string";
  SmallVector<StringRef> words;
  llvm::SplitString(str.getValue(), words);
  static const SmallVector<SmallVector<StringRef>, 3> groups = {
      {"borrowed", "moved"}, {"in", "out", "inout"}, {"fixed", "mutable"}};
  size_t group = 0;
  for (StringRef w : words) {
    while (group < groups.size() && !llvm::is_contained(groups[group], w))
      ++group;
    if (group == groups.size())
      return op->emitError()
             << "invalid modifiers \"" << str.getValue() << "\" on argument "
             << argIndex
             << ": expected ownership, access, mutability, in that order";
    ++group;
  }
  return success();
}

//===----------------------------------------------------------------------===//
// IntType
//===----------------------------------------------------------------------===//

Type IntType::parse(AsmParser &parser) {
  SMLoc loc = parser.getCurrentLocation();
  APInt lo, hi;
  if (parser.parseLess())
    return {};
  OptionalParseResult r = parser.parseOptionalInteger(lo);
  if (!r.has_value() || failed(*r))
    return parser.emitError(parser.getCurrentLocation(),
                            "expected the lower bound"),
           Type();
  if (parser.parseComma())
    return {};
  r = parser.parseOptionalInteger(hi);
  if (!r.has_value() || failed(*r))
    return parser.emitError(parser.getCurrentLocation(),
                            "expected the upper bound"),
           Type();
  if (parser.parseGreater())
    return {};
  return parser.getChecked<IntType>(loc, parser.getContext(), widen(lo),
                                    widen(hi));
}

void IntType::print(AsmPrinter &printer) const {
  printer << "<";
  getLo().print(printer.getStream(), /*isSigned=*/true);
  printer << ", ";
  getHi().print(printer.getStream(), /*isSigned=*/true);
  printer << ">";
}

LogicalResult IntType::verify(function_ref<InFlightDiagnostic()> emitError,
                              APInt lo, APInt hi) {
  APInt l = widen(lo), h = widen(hi);
  if (l.sgt(h)) return emitError() << "range lower bound exceeds upper bound";
  if (l.slt(minBound()) || h.sgt(maxBound()))
    return emitError() << "range must lie within [-2^63, 2^64 - 1]";
  return success();
}

bool IntType::isSigned() const { return widen(getLo()).isNegative(); }

bool IntType::contains(const APInt &value) const {
  APInt v = widen(value);
  return widen(getLo()).sle(v) && v.sle(widen(getHi()));
}

unsigned IntType::getStorageWidth() const {
  APInt lo = widen(getLo()), hi = widen(getHi());
  for (unsigned bits : {8u, 16u, 32u, 64u}) {
    APInt min = isSigned() ? APInt::getSignedMinValue(bits).sext(kBoundWidth)
                           : APInt(kBoundWidth, 0);
    APInt max = isSigned() ? APInt::getSignedMaxValue(bits).sext(kBoundWidth)
                           : APInt::getMaxValue(bits).zext(kBoundWidth);
    if (min.sle(lo) && hi.sle(max)) return bits;
  }
  return 64;
}

//===----------------------------------------------------------------------===//
// Ops
//===----------------------------------------------------------------------===//

// `pia.constant 42 : !pia.int<0, 255>`
ParseResult ConstantOp::parse(OpAsmParser &parser, OperationState &result) {
  APInt value;
  OptionalParseResult r = parser.parseOptionalInteger(value);
  if (!r.has_value() || failed(*r))
    return parser.emitError(parser.getCurrentLocation(), "expected an integer");
  Type type;
  if (parser.parseOptionalAttrDict(result.attributes) || parser.parseColon() ||
      parser.parseType(type))
    return failure();
  Builder &b = parser.getBuilder();
  result.addAttribute("value", b.getIntegerAttr(b.getIntegerType(kBoundWidth),
                                                widen(value)));
  result.addTypes(type);
  return success();
}

void ConstantOp::print(OpAsmPrinter &printer) {
  printer << " ";
  getValue().print(printer.getStream(), /*isSigned=*/true);
  printer.printOptionalAttrDict((*this)->getAttrs(), {"value"});
  printer << " : " << getType();
}

LogicalResult ConstantOp::verify() {
  if (!getType().contains(getValue()))
    return emitOpError("value is outside the range of ") << getType();
  return success();
}

OpFoldResult ConstantOp::fold(FoldAdaptor) { return getValueAttr(); }

bool ConvertOp::isWidening() {
  auto in = getInput().getType(), out = getResult().getType();
  return widen(out.getLo()).sle(widen(in.getLo())) &&
         widen(in.getHi()).sle(widen(out.getHi()));
}

OpFoldResult LenOp::fold(FoldAdaptor) {
  if (auto array = dyn_cast<ArrayType>(getBuffer().getType()))
    return IntegerAttr::get(IndexType::get(getContext()), array.getLength());
  return {};
}

LogicalResult LoadOp::verify() {
  if (getResult().getType() != elementTypeOf(getBuffer().getType()))
    return emitOpError("result type must be the buffer's element type");
  return success();
}

LogicalResult StoreOp::verify() {
  if (getValue().getType() != elementTypeOf(getBuffer().getType()))
    return emitOpError("stored value must have the buffer's element type");
  return success();
}

static LogicalResult checkTag(Operation *op, DynType dyn, Type tag) {
  if (!llvm::is_contained(dyn.getTags(), tag))
    return op->emitOpError() << tag << " is not one of the tags of " << dyn;
  return success();
}

LogicalResult DynWrapOp::verify() {
  return checkTag(*this, getResult().getType(), getInput().getType());
}
LogicalResult DynIsOp::verify() {
  return checkTag(*this, getInput().getType(), getTag());
}
LogicalResult DynUnwrapOp::verify() {
  return checkTag(*this, getInput().getType(), getResult().getType());
}
