#include "dialect/ParDialect.h"

#include "llvm/ADT/TypeSwitch.h"
#include "mlir/IR/DialectImplementation.h"

using namespace mlir;
using namespace pia::par;

#include "dialect/ParDialect.cpp.inc"
#include "dialect/ParEnums.cpp.inc"

#define GET_TYPEDEF_CLASSES
#include "dialect/ParTypes.cpp.inc"

#define GET_OP_CLASSES
#include "dialect/Par.cpp.inc"

void ParDialect::initialize() {
  registerTypes();
  addOperations<
#define GET_OP_LIST
#include "dialect/Par.cpp.inc"
      >();
}

void ParDialect::registerTypes() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "dialect/ParTypes.cpp.inc"
      >();
}

LogicalResult SpreadOp::verify() {
  Block &body = getBody().front();
  if (body.getNumArguments() != 1)
    return emitOpError("body must take exactly one argument, the tile");
  TiledType grid = getGrid().getType();
  auto tile = dyn_cast<TileType>(body.getArgument(0).getType());
  if (!tile || tile.getElementType() != grid.getElementType() ||
      tile.getTileRows() != grid.getTileRows() ||
      tile.getTileCols() != grid.getTileCols() || tile.getHalo() != grid.getHalo())
    return emitOpError("body argument must be a !pia_par.tile matching the grid");
  if (getPrefer() && getPlacement() != Placement::auto_)
    return emitOpError("'prefer' only refines place(auto)");
  return success();
}
