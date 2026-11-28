//===- Lib.td - The pia_lib dialect -------------------------------*- tablegen -*-===//
//
// Calls to library functions that have a lowering rule (ADR 0078). One op,
// `pia_lib.call`, names the Pia function whose body is its meaning, so a
// library adds no op of its own. `pia-lib-lower` turns each one into the
// rule's upstream form or into a call of the body.
//
//===----------------------------------------------------------------------===//

#ifndef PIA_DIALECT_LIB_TD
#define PIA_DIALECT_LIB_TD

include "mlir/IR/DialectBase.td"
include "mlir/IR/OpBase.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

def Lib_Dialect : Dialect {
  let name = "pia_lib";
  let summary = "Calls to Pia library functions with lowering rules";
  let cppNamespace = "::pia::lib";
}

def Lib_CallOp : Op<Lib_Dialect, "call", [
    DeclareOpInterfaceMethods<SymbolUserOpInterface>,
    DeclareOpInterfaceMethods<MemoryEffectsOpInterface>]> {
  let summary = "a call of a Pia function whose body is the op's meaning";
  let description = [{
    `%r = pia_lib.call @sqrt(%x) : (f64) -> f64` calls the function `@sqrt`,
    whose `@lower` is a rule that `pia-lib-lower` may substitute, and whose
    body it calls otherwise. The function stays in the module, so the op can
    always be expanded. With `pure`, the call has no memory effects, so CSE
    and hoisting treat it like any pure op; without it, it may read and
    write anything, as a call does.
  }];
  let arguments = (ins FlatSymbolRefAttr:$callee, Variadic<AnyType>:$args,
                       UnitAttr:$pure);
  let results = (outs Variadic<AnyType>:$results);
  let assemblyFormat = [{
    $callee `(` $args `)` attr-dict `:` functional-type($args, results)
  }];
}

#endif // PIA_DIALECT_LIB_TD
