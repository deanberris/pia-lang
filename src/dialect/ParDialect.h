// The pia_par dialect: tiled grids, spread loops, collectives, placement.

#ifndef PIA_DIALECT_PARDIALECT_H
#define PIA_DIALECT_PARDIALECT_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

#include "dialect/ParDialect.h.inc"
#include "dialect/ParEnums.h.inc"

#define GET_TYPEDEF_CLASSES
#include "dialect/ParTypes.h.inc"

#define GET_OP_CLASSES
#include "dialect/Par.h.inc"

#endif  // PIA_DIALECT_PARDIALECT_H
