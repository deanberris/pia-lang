// The pia_contract dialect: contracts, quantifiers and proof obligations.

#ifndef PIA_DIALECT_CONTRACTDIALECT_H
#define PIA_DIALECT_CONTRACTDIALECT_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

#include "dialect/ContractDialect.h.inc"
#include "dialect/ContractEnums.h.inc"

#define GET_OP_CLASSES
#include "dialect/Contract.h.inc"

#endif  // PIA_DIALECT_CONTRACTDIALECT_H
