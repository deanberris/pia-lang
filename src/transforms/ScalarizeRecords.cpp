#include "transforms/ScalarizeRecords.h"

#include <string>
#include <vector>

#include "dialect/ContractDialect.h"
#include "dialect/PiaDialect.h"
#include "llvm/Config/llvm-config.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Func/Transforms/FuncConversions.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/SCF/Transforms/Patterns.h"
#include "mlir/IR/BuiltinAttributes.h"
#include "mlir/Transforms/DialectConversion.h"

namespace pia::transforms {

using mlir::Type;
using mlir::Value;

namespace {

// The record a buffer holds, if it holds records.
RecordType elementRecord(Type t) {
  if (auto a = mlir::dyn_cast<ArrayType>(t))
    return mlir::dyn_cast<RecordType>(a.getElementType());
  if (auto s = mlir::dyn_cast<SliceType>(t))
    return mlir::dyn_cast<RecordType>(s.getElementType());
  return {};
}

// The scalar fields of `t`, depth first: a record's fields, recursively,
// or `t` itself. A buffer of records becomes one buffer per field, struct
// of arrays: `[pixel; 8]` is `[u8; 8]` four times.
void leaves(Type t, llvm::SmallVectorImpl<Type> &out) {
  if (auto r = mlir::dyn_cast<RecordType>(t)) {
    for (Type f : r.getFieldTypes()) leaves(f, out);
    return;
  }
  if (RecordType r = elementRecord(t)) {
    llvm::SmallVector<Type> fields;
    leaves(r, fields);
    for (Type f : fields) {
      if (auto a = mlir::dyn_cast<ArrayType>(t))
        out.push_back(ArrayType::get(t.getContext(), a.getLength(), f));
      else
        out.push_back(SliceType::get(t.getContext(), f));
    }
    return;
  }
  out.push_back(t);
}

bool hasRecordLeaves(Type t) {
  return mlir::isa<RecordType>(t) || static_cast<bool>(elementRecord(t));
}

unsigned leafCount(Type t) {
  llvm::SmallVector<Type> out;
  leaves(t, out);
  return out.size();
}

// The names of `t`'s leaves under `prefix`: `p.r`, `p.g`, ...
void leafNames(Type t, const std::string &prefix,
               std::vector<std::string> &out) {
  auto r = mlir::dyn_cast<RecordType>(t);
  if (!r) r = elementRecord(t);
  if (!r) {
    out.push_back(prefix);
    return;
  }
  for (auto [name, ft] : llvm::zip(r.getFieldNames(), r.getFieldTypes()))
    leafNames(ft, prefix + "." + name.str(), out);
}

class RecordTypes : public mlir::TypeConverter {
 public:
  RecordTypes() {
    addConversion([](Type t) { return t; });
    addConversion([](RecordType r, llvm::SmallVectorImpl<Type> &out)
                      -> std::optional<mlir::LogicalResult> {
      leaves(r, out);
      return mlir::success();
    });
    auto buffer = [](Type t, llvm::SmallVectorImpl<Type> &out)
        -> std::optional<mlir::LogicalResult> {
      if (!elementRecord(t)) return std::nullopt;
      leaves(t, out);
      return mlir::success();
    };
    addConversion([buffer](ArrayType t, llvm::SmallVectorImpl<Type> &out) {
      return buffer(t, out);
    });
    addConversion([buffer](SliceType t, llvm::SmallVectorImpl<Type> &out) {
      return buffer(t, out);
    });
  }
};

// Ops are created with the builder API of the LLVM in use.
template <typename Op, typename... Args>
Op make(mlir::OpBuilder &b, mlir::Location loc, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
  return Op::create(b, loc, std::forward<Args>(args)...);
#else
  return b.create<Op>(loc, std::forward<Args>(args)...);
#endif
}

Type elementOf(Type buffer) {
  if (auto a = mlir::dyn_cast<ArrayType>(buffer)) return a.getElementType();
  return mlir::cast<SliceType>(buffer).getElementType();
}

llvm::SmallVector<Value> flatten(llvm::ArrayRef<mlir::ValueRange> ranges) {
  llvm::SmallVector<Value> out;
  for (mlir::ValueRange r : ranges) out.append(r.begin(), r.end());
  return out;
}

struct RecordLowering : mlir::OpConversionPattern<RecordOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      RecordOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.push_back(flatten(adaptor.getFields()));
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

struct FieldLowering : mlir::OpConversionPattern<FieldOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      FieldOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    RecordType rt = op.getInput().getType();
    unsigned index = op.getIndex(), offset = 0;
    for (unsigned i = 0; i < index; ++i)
      offset += leafCount(rt.getFieldTypes()[i]);
    unsigned count = leafCount(rt.getFieldTypes()[index]);
    mlir::ValueRange all = adaptor.getInput();
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.emplace_back(all.begin() + offset, all.begin() + offset + count);
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

// `old p` on a record is `old` of each field.
struct OldLowering : mlir::OpConversionPattern<contract::OldOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      contract::OldOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    llvm::SmallVector<Value> fields;
    for (Value v : flatten(adaptor.getOperands())) {
#if LLVM_VERSION_MAJOR >= 21
      fields.push_back(
          contract::OldOp::create(rw, op.getLoc(), v.getType(), v));
#else
      fields.push_back(
          rw.create<contract::OldOp>(op.getLoc(), v.getType(), v));
#endif
    }
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.push_back(std::move(fields));
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

// The field buffers of a buffer of records share one length, so a load,
// store or slice copied to each of them is in bounds exactly when the first
// copy is. The copies after the first are marked, and the verifier assumes
// their bound instead of reporting it again.
void shareBounds(mlir::ConversionPatternRewriter &rw, mlir::Operation *op) {
  op->setAttr(PiaDialect::getBoundsSharedAttrName(), rw.getUnitAttr());
}

// `xs[i]` on a buffer of records reads element i of each field's buffer.
struct LoadLowering : mlir::OpConversionPattern<LoadOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      LoadOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    if (!elementRecord(op.getBuffer().getType())) return mlir::failure();
    Value index = adaptor.getIndex().front();
    llvm::SmallVector<Value> fields;
    for (Value b : adaptor.getBuffer()) {
      auto load = make<LoadOp>(rw, op.getLoc(), elementOf(b.getType()), b, index);
      if (!fields.empty()) shareBounds(rw, load);
      fields.push_back(load);
    }
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.push_back(std::move(fields));
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

// `xs[i] <- v` writes each field of v to its own buffer.
struct StoreLowering : mlir::OpConversionPattern<StoreOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      StoreOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    if (!elementRecord(op.getBuffer().getType())) return mlir::failure();
    Value index = adaptor.getIndex().front();
    bool first = true;
    for (auto [v, b] : llvm::zip_equal(adaptor.getValue(), adaptor.getBuffer())) {
      // A field read back from the same place, as `xs.[i].r <- v` leaves
      // the other fields, needs no write.
      if (auto load = v.getDefiningOp<LoadOp>();
          load && load.getBuffer() == b && load.getIndex() == index)
        continue;
      // The first store written carries the bounds goal, whichever field
      // it is.
      auto store = make<StoreOp>(rw, op.getLoc(), v, b, index);
      if (!first) shareBounds(rw, store);
      first = false;
    }
    rw.eraseOp(op);
    return mlir::success();
  }
};

// A view of a buffer of records is the same view of each field's buffer.
struct SliceLowering : mlir::OpConversionPattern<SliceOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      SliceOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    if (!elementRecord(op.getBuffer().getType())) return mlir::failure();
    Value lo = adaptor.getLo().front(), hi = adaptor.getHi().front();
    llvm::SmallVector<Value> views;
    for (Value b : adaptor.getBuffer()) {
      auto view = make<SliceOp>(
          rw, op.getLoc(), SliceType::get(rw.getContext(), elementOf(b.getType())),
          b, lo, hi);
      if (!views.empty()) shareBounds(rw, view);
      views.push_back(view);
    }
    llvm::SmallVector<llvm::SmallVector<Value>> results;
    results.push_back(std::move(views));
    rw.replaceOpWithMultiple(op, std::move(results));
    return mlir::success();
  }
};

// Every field's buffer has the same length; the first one's is used.
struct LenLowering : mlir::OpConversionPattern<LenOp> {
  using OpConversionPattern::OpConversionPattern;
  mlir::LogicalResult matchAndRewrite(
      LenOp op, OneToNOpAdaptor adaptor,
      mlir::ConversionPatternRewriter &rw) const override {
    if (!elementRecord(op.getBuffer().getType())) return mlir::failure();
    Value len = make<LenOp>(rw, op.getLoc(), rw.getIndexType(),
                            adaptor.getBuffer().front());
    rw.replaceOp(op, len);
    return mlir::success();
  }
};

bool hasRecords(mlir::ModuleOp module) {
  bool found = false;
  module.walk([&](mlir::Operation *op) {
    auto isRecord = [](Type t) { return hasRecordLeaves(t); };
    if (llvm::any_of(op->getOperandTypes(), isRecord) ||
        llvm::any_of(op->getResultTypes(), isRecord))
      found = true;
    if (auto f = mlir::dyn_cast<mlir::func::FuncOp>(op))
      if (llvm::any_of(f.getFunctionType().getInputs(), isRecord) ||
          llvm::any_of(f.getFunctionType().getResults(), isRecord))
        found = true;
    return found ? mlir::WalkResult::interrupt() : mlir::WalkResult::advance();
  });
  return found;
}

// A block argument's source name, from the NameLoc IRGen gives parameters.
std::string argName(mlir::BlockArgument arg) {
  if (auto n = mlir::dyn_cast<mlir::NameLoc>(arg.getLoc()))
    return n.getName().str();
  return "";
}

}  // namespace

// A load or slice of a buffer of records becomes one copy per field, and
// a field nobody reads leaves its copy unused. An unused load would count
// as program code, with a bounds goal of its own, even when the record was
// read only by a contract, which raises none. So the unused copies of each
// group are erased. When the first copy, which carries the goal, is among
// them, the first copy still in use carries it instead. A group with no
// copy in use keeps its first, as a load of a scalar nobody reads keeps
// its goal.
static void pruneFieldCopies(mlir::ModuleOp module) {
  auto shared = [](mlir::Operation *op) {
    return op->hasAttr(PiaDialect::getBoundsSharedAttrName());
  };
  auto sameBounds = [](mlir::Operation *a, mlir::Operation *b) {
    if (a->getName() != b->getName()) return false;
    // Operand 0 is the field's buffer; the rest are the index or bounds.
    for (unsigned i = 1; i < a->getNumOperands(); ++i)
      if (a->getOperand(i) != b->getOperand(i)) return false;
    return true;
  };
  llvm::SmallVector<llvm::SmallVector<mlir::Operation *>> groups;
  module.walk([&](mlir::Operation *op) {
    if (!mlir::isa<LoadOp, SliceOp>(op) || shared(op)) return;
    llvm::SmallVector<mlir::Operation *> group{op};
    for (mlir::Operation *next = op->getNextNode();
         next && shared(next) && sameBounds(op, next);
         next = next->getNextNode())
      group.push_back(next);
    if (group.size() > 1) groups.push_back(std::move(group));
  });
  for (auto &group : groups) {
    mlir::Operation *carrier = nullptr;
    for (mlir::Operation *op : group)
      if (!op->use_empty()) {
        carrier = op;
        break;
      }
    if (!carrier) carrier = group.front();
    carrier->removeAttr(PiaDialect::getBoundsSharedAttrName());
    for (mlir::Operation *op : group)
      if (op != carrier && op->use_empty()) op->erase();
  }
}

mlir::LogicalResult scalarizeRecordsIn(mlir::ModuleOp module);

// A generic's proof over sorts keeps its stand-in types, which the
// verifier encodes as uninterpreted sorts (ADR 0043), so it is set aside
// while the rest of the module is converted.
mlir::LogicalResult scalarizeRecords(mlir::ModuleOp module) {
  std::vector<mlir::func::FuncOp> proofs;
  for (auto f : module.getOps<mlir::func::FuncOp>())
    if (f->hasAttr("pia.generic_proof")) proofs.push_back(f);
  if (proofs.empty()) return scalarizeRecordsIn(module);
  mlir::OpBuilder b(module.getContext());
  auto aside = mlir::ModuleOp::create(module.getLoc());
  for (auto f : proofs) {
    f->remove();
    aside.getBody()->push_back(f);
  }
  mlir::LogicalResult r = scalarizeRecordsIn(module);
  for (auto f : proofs) {
    f->remove();
    module.getBody()->push_back(f);
  }
  aside.erase();
  return r;
}

mlir::LogicalResult scalarizeRecordsIn(mlir::ModuleOp module) {
  if (!hasRecords(module)) return mlir::success();
  mlir::MLIRContext *ctx = module.getContext();

  // Remember each parameter's name and type, to name its fields after the
  // conversion: the signature conversion makes new block arguments.
  struct Named {
    std::string name;
    Type type;
    mlir::Location loc;
  };
  std::vector<std::pair<mlir::func::FuncOp, std::vector<Named>>> params;
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    // A generic's proof keeps its parameters (ADR 0043).
    if (f.isExternal() || f->hasAttr("pia.generic_proof")) continue;
    std::vector<Named> ps;
    for (mlir::BlockArgument a : f.getArguments()) {
      mlir::Location inner = a.getLoc();
      if (auto n = mlir::dyn_cast<mlir::NameLoc>(inner))
        inner = n.getChildLoc();
      ps.push_back({argName(a), a.getType(), inner});
    }
    params.emplace_back(f, std::move(ps));
  }
  // Argument attributes such as pia.modifiers belong to the whole record;
  // each field keeps them.
  std::vector<std::vector<mlir::DictionaryAttr>> argAttrs;
  for (auto &[f, ps] : params) {
    std::vector<mlir::DictionaryAttr> attrs;
    for (unsigned i = 0; i < ps.size(); ++i) attrs.push_back(f.getArgAttrDict(i));
    argAttrs.push_back(std::move(attrs));
  }

  // A function with a buffer of records gets one buffer per field, whose
  // facts the goal about one field never needs; the verifier slices its
  // goals.
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    bool buffers = llvm::any_of(f.getArgumentTypes(), elementRecord) ||
                   llvm::any_of(f.getResultTypes(), elementRecord);
    if (!buffers && !f.isExternal())
      f.walk([&](mlir::Operation *op) {
        if (llvm::any_of(op->getResultTypes(), elementRecord) ||
            llvm::any_of(op->getOperandTypes(), elementRecord)) {
          buffers = true;
          return mlir::WalkResult::interrupt();
        }
        return mlir::WalkResult::advance();
      });
    if (buffers)
      f->setAttr(PiaDialect::getRecordBuffersAttrName(),
                 mlir::UnitAttr::get(ctx));
  }

  RecordTypes types;
  mlir::ConversionTarget target(*ctx);
  target.addIllegalOp<RecordOp, FieldOp>();
  target.addDynamicallyLegalOp<LoadOp, StoreOp, SliceOp, LenOp>(
      [&](mlir::Operation *op) {
        auto f = op->getParentOfType<mlir::func::FuncOp>();
        return (f && f->hasAttr("pia.generic_proof")) || types.isLegal(op);
      });
  auto inGenericProof = [](mlir::Operation *op) {
    auto f = op->getParentOfType<mlir::func::FuncOp>();
    return f && f->hasAttr("pia.generic_proof");
  };
  target.markUnknownOpDynamicallyLegal([&](mlir::Operation *op) {
    return inGenericProof(op) || types.isLegal(op);
  });
  target.addDynamicallyLegalOp<mlir::func::FuncOp>([&](mlir::func::FuncOp f) {
    // A generic's proof over sorts keeps its stand-in types, which the
    // verifier encodes as uninterpreted sorts (ADR 0043).
    if (f->hasAttr("pia.generic_proof")) return true;
    return types.isSignatureLegal(f.getFunctionType()) &&
           types.isLegal(&f.getBody());
  });

  mlir::RewritePatternSet patterns(ctx);
  patterns.add<RecordLowering, FieldLowering, OldLowering, LoadLowering,
               StoreLowering, SliceLowering, LenLowering>(types, ctx);
  mlir::populateFunctionOpInterfaceTypeConversionPattern<mlir::func::FuncOp>(
      patterns, types);
  mlir::populateCallOpTypeConversionPattern(patterns, types);
  mlir::populateReturnOpTypeConversionPattern(patterns, types);
  mlir::scf::populateSCFStructuralTypeConversionsAndLegality(types, patterns,
                                                             target);

  if (mlir::failed(
          mlir::applyPartialConversion(module, target, std::move(patterns))))
    return mlir::failure();
  pruneFieldCopies(module);

  for (size_t k = 0; k < params.size(); ++k) {
    auto &[f, ps] = params[k];
    unsigned next = 0;
    llvm::SmallVector<mlir::DictionaryAttr> attrs;
    for (size_t i = 0; i < ps.size(); ++i) {
      std::vector<std::string> names;
      leafNames(ps[i].type, ps[i].name, names);
      // The field buffers of a slice of records share one length, which
      // pia.length_of records for the verifier and the C entry point.
      unsigned first = next;
      bool slice = mlir::isa<SliceType>(ps[i].type) &&
                   static_cast<bool>(elementRecord(ps[i].type));
      for (const std::string &name : names) {
        mlir::BlockArgument a = f.getArgument(next);
        a.setLoc(name.empty() ? ps[i].loc
                              : mlir::NameLoc::get(
                                    mlir::StringAttr::get(ctx, name),
                                    ps[i].loc));
        mlir::DictionaryAttr d = argAttrs[k][i];
        if (slice && next != first) {
          mlir::NamedAttrList list(d);
          list.set(PiaDialect::getLengthOfAttrName(),
                   mlir::IntegerAttr::get(mlir::IntegerType::get(ctx, 64), first));
          d = list.getDictionary(ctx);
        }
        attrs.push_back(d);
        ++next;
      }
    }
    f.setAllArgAttrs(attrs);
  }
  return mlir::success();
}

}  // namespace pia::transforms
