// The pia_lib dialect: `pia_lib.call`, a call of a Pia library function
// with a lowering rule (ADR 0078).

#ifndef PIA_DIALECT_LIBDIALECT_H
#define PIA_DIALECT_LIBDIALECT_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

#include "dialect/LibDialect.h.inc"

#define GET_OP_CLASSES
#include "dialect/Lib.h.inc"

#endif // PIA_DIALECT_LIBDIALECT_H
