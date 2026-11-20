#include "dialect/ContractDialect.h"

using namespace mlir;
using namespace pia::contract;

#include "dialect/ContractDialect.cpp.inc"
#include "dialect/ContractEnums.cpp.inc"

#define GET_OP_CLASSES
#include "dialect/Contract.cpp.inc"

void ContractDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "dialect/Contract.cpp.inc"
      >();
}

static LogicalResult verifyQuantifier(Operation *op, Region &body) {
  if (body.front().getNumArguments() == 0)
    return op->emitOpError("must bind at least one variable");
  return success();
}

LogicalResult ForallOp::verify() { return verifyQuantifier(*this, getBody()); }
LogicalResult ExistsOp::verify() { return verifyQuantifier(*this, getBody()); }
