// The pia dialect: range-typed integers, arrays, slices, dyn and scalar ops.

#ifndef PIA_DIALECT_PIADIALECT_H
#define PIA_DIALECT_PIADIALECT_H

#include "llvm/ADT/APInt.h"
#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

#include "dialect/PiaDialect.h.inc"
#include "dialect/PiaEnums.h.inc"

#define GET_TYPEDEF_CLASSES
#include "dialect/PiaTypes.h.inc"

#define GET_OP_CLASSES
#include "dialect/Pia.h.inc"

#endif  // PIA_DIALECT_PIADIALECT_H
