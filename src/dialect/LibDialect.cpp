#include "dialect/LibDialect.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"

using namespace mlir;
using namespace pia::lib;

#include "dialect/LibDialect.cpp.inc"

#define GET_OP_CLASSES
#include "dialect/Lib.cpp.inc"

void LibDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "dialect/Lib.cpp.inc"
      >();
}

// The callee is a function in the module with the op's types, so the op
// can always be expanded into a call of it.
LogicalResult CallOp::verifySymbolUses(SymbolTableCollection &symbolTable) {
  auto fn =
      symbolTable.lookupNearestSymbolFrom<func::FuncOp>(*this, getCalleeAttr());
  if (!fn)
    return emitOpError() << "'" << getCallee()
                         << "' is not a function in the module";
  FunctionType type = fn.getFunctionType();
  if (type.getInputs() != getArgs().getTypes() ||
      type.getResults() != getResultTypes())
    return emitOpError() << "has the types " << getArgs().getTypes() << " -> "
                         << getResultTypes() << ", but '" << getCallee()
                         << "' has " << type;
  return success();
}

void CallOp::getEffects(
    SmallVectorImpl<SideEffects::EffectInstance<MemoryEffects::Effect>>
        &effects) {
  if (getPure())
    return;
  effects.emplace_back(MemoryEffects::Allocate::get());
  effects.emplace_back(MemoryEffects::Free::get());
  effects.emplace_back(MemoryEffects::Read::get());
  effects.emplace_back(MemoryEffects::Write::get());
}
