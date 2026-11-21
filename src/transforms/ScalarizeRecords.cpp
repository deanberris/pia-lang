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

// The scalar fields of `t`, depth first: a record's fields, recursively,
// or `t` itself.
void leaves(Type t, llvm::SmallVectorImpl<Type> &out) {
  if (auto r = mlir::dyn_cast<RecordType>(t)) {
    for (Type f : r.getFieldTypes()) leaves(f, out);
    return;
  }
  out.push_back(t);
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
  }
};

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

bool hasRecords(mlir::ModuleOp module) {
  bool found = false;
  module.walk([&](mlir::Operation *op) {
    auto isRecord = [](Type t) { return mlir::isa<RecordType>(t); };
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

mlir::LogicalResult scalarizeRecords(mlir::ModuleOp module) {
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
    if (f.isExternal()) continue;
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

  RecordTypes types;
  mlir::ConversionTarget target(*ctx);
  target.addIllegalOp<RecordOp, FieldOp>();
  target.markUnknownOpDynamicallyLegal(
      [&](mlir::Operation *op) { return types.isLegal(op); });
  target.addDynamicallyLegalOp<mlir::func::FuncOp>([&](mlir::func::FuncOp f) {
    return types.isSignatureLegal(f.getFunctionType()) &&
           types.isLegal(&f.getBody());
  });

  mlir::RewritePatternSet patterns(ctx);
  patterns.add<RecordLowering, FieldLowering, OldLowering>(types, ctx);
  mlir::populateFunctionOpInterfaceTypeConversionPattern<mlir::func::FuncOp>(
      patterns, types);
  mlir::populateCallOpTypeConversionPattern(patterns, types);
  mlir::populateReturnOpTypeConversionPattern(patterns, types);
  mlir::scf::populateSCFStructuralTypeConversionsAndLegality(types, patterns,
                                                             target);
  if (mlir::failed(
          mlir::applyPartialConversion(module, target, std::move(patterns))))
    return mlir::failure();

  for (size_t k = 0; k < params.size(); ++k) {
    auto &[f, ps] = params[k];
    unsigned next = 0;
    llvm::SmallVector<mlir::DictionaryAttr> attrs;
    for (size_t i = 0; i < ps.size(); ++i) {
      std::vector<std::string> names;
      leafNames(ps[i].type, ps[i].name, names);
      for (const std::string &name : names) {
        mlir::BlockArgument a = f.getArgument(next++);
        a.setLoc(name.empty() ? ps[i].loc
                              : mlir::NameLoc::get(
                                    mlir::StringAttr::get(ctx, name),
                                    ps[i].loc));
        attrs.push_back(argAttrs[k][i]);
      }
    }
    f.setAllArgAttrs(attrs);
  }
  return mlir::success();
}

}  // namespace pia::transforms
