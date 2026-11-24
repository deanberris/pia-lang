#include "codegen/ArrayResults.h"

#include <map>
#include <vector>

#include "dialect/PiaDialect.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Config/llvm-config.h"

namespace pia::codegen {

using mlir::Type;
using mlir::Value;

namespace {

template <typename Op, typename... Args>
Op make(mlir::OpBuilder &b, mlir::Location loc, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
  return Op::create(b, loc, std::forward<Args>(args)...);
#else
  return b.create<Op>(loc, std::forward<Args>(args)...);
#endif
}

// The positions of a function type's array results.
std::vector<unsigned> arrayResults(mlir::FunctionType ft) {
  std::vector<unsigned> out;
  for (unsigned i = 0; i < ft.getNumResults(); ++i)
    if (mlir::isa<ArrayType>(ft.getResult(i))) out.push_back(i);
  return out;
}

} // namespace

mlir::LogicalResult arrayResultsToBuffers(mlir::ModuleOp module) {
  // The functions to change, with the positions of their array results.
  std::map<std::string, std::vector<unsigned>> changed;
  bool failed = false;
  module.walk([&](mlir::func::FuncOp f) {
    std::vector<unsigned> at = arrayResults(f.getFunctionType());
    if (at.empty()) return;
    if (f.isExternal()) {
      f.emitError("a foreign function cannot return an array yet");
      failed = true;
      return;
    }
    changed[f.getSymName().str()] = at;
  });
  if (failed) return mlir::failure();
  if (changed.empty()) return mlir::success();

  // Each function takes one output buffer per array result, after its
  // own parameters, and each return copies into them.
  module.walk([&](mlir::func::FuncOp f) {
    auto it = changed.find(f.getSymName().str());
    if (it == changed.end()) return;
    const std::vector<unsigned> &at = it->second;
    mlir::FunctionType ft = f.getFunctionType();
    mlir::Block &entry = f.getBody().front();
    std::vector<Value> outs;
    llvm::SmallVector<unsigned> argIndices;
    llvm::SmallVector<Type> argTypes;
    llvm::SmallVector<mlir::DictionaryAttr> argAttrs;
    llvm::SmallVector<mlir::Location> argLocs;
    for (unsigned r : at) {
      argIndices.push_back(ft.getNumInputs());
      argTypes.push_back(ft.getResult(r));
      argAttrs.push_back(mlir::DictionaryAttr::get(f.getContext()));
      argLocs.push_back(f.getLoc());
    }
    (void)f.insertArguments(argIndices, argTypes, argAttrs, argLocs);
    for (unsigned k = 0; k < at.size(); ++k)
      outs.push_back(entry.getArgument(ft.getNumInputs() + k));
    llvm::BitVector drop(ft.getNumResults());
    for (unsigned r : at) drop.set(r);
    f.walk([&](mlir::func::ReturnOp ret) {
      mlir::OpBuilder b(ret);
      llvm::SmallVector<Value> keep;
      for (unsigned i = 0; i < ret.getNumOperands(); ++i) {
        if (!drop.test(i)) {
          keep.push_back(ret.getOperand(i));
          continue;
        }
        unsigned k = 0;
        while (at[k] != i) ++k;
        make<CopyOp>(b, ret.getLoc(), ret.getOperand(i), outs[k]);
      }
      make<mlir::func::ReturnOp>(b, ret.getLoc(), keep);
      ret.erase();
    });
    (void)f.eraseResults(drop);
  });

  // Each call makes the buffers in its caller's frame and reads the
  // arrays from them.
  module.walk([&](mlir::func::CallOp call) {
    auto it = changed.find(call.getCallee().str());
    if (it == changed.end()) return;
    const std::vector<unsigned> &at = it->second;
    mlir::OpBuilder b(call);
    llvm::SmallVector<Value> args(call.getOperands().begin(),
                                  call.getOperands().end());
    std::vector<Value> bufs;
    for (unsigned r : at) {
      Value buf = make<RegionOp>(b, call.getLoc(), call.getResult(r).getType());
      bufs.push_back(buf);
      args.push_back(buf);
    }
    llvm::SmallVector<Type> types;
    for (unsigned i = 0; i < call.getNumResults(); ++i) {
      bool isArray = false;
      for (unsigned r : at) isArray |= r == i;
      if (!isArray) types.push_back(call.getResult(i).getType());
    }
    auto next = make<mlir::func::CallOp>(b, call.getLoc(), call.getCallee(),
                                         types, args);
    next->setAttrs(call->getAttrs());
    unsigned kept = 0;
    for (unsigned i = 0; i < call.getNumResults(); ++i) {
      unsigned k = 0;
      bool isArray = false;
      for (; k < at.size(); ++k)
        if (at[k] == i) { isArray = true; break; }
      call.getResult(i).replaceAllUsesWith(isArray ? bufs[k]
                                                   : next.getResult(kept++));
    }
    call.erase();
  });
  return mlir::success();
}

} // namespace pia::codegen
