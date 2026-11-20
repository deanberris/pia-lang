//===- Pia.td - The pia dialect: Pia's types and values ----------*- tablegen -*-===//
//
// Range-typed integers, fixed arrays and slices, tagged `dyn` values, and the
// arithmetic, comparison and memory ops IRGen lowers Pia's scalar subset to.
// See docs/architecture.md, "Dialects", and ADR 0018.
//
//===----------------------------------------------------------------------===//

#ifndef PIA_DIALECT_PIA_TD
#define PIA_DIALECT_PIA_TD

include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/DialectBase.td"
include "mlir/IR/EnumAttr.td"
include "mlir/IR/OpBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

def Pia_Dialect : Dialect {
  let name = "pia";
  let summary = "Pia's types and values";
  let cppNamespace = "::pia";
  let useDefaultTypePrinterParser = 1;
  let extraClassDeclaration = [{
    void registerTypes();

    /// The argument attribute that carries a parameter's modifiers, e.g.
    /// `{pia.modifiers = "borrowed in mutable"}` (docs/grammar.md).
    static constexpr ::llvm::StringLiteral getModifiersAttrName() {
      return ::llvm::StringLiteral("pia.modifiers");
    }
  }];
  let hasRegionArgAttrVerify = 1;
  // Folded `index` values become `arith.constant`; folded Pia integers become
  // `pia.constant`.
  let hasConstantMaterializer = 1;
  let dependentDialects = ["::mlir::arith::ArithDialect"];
}

//===----------------------------------------------------------------------===//
// Types
//===----------------------------------------------------------------------===//

class Pia_Type<string name, string typeMnemonic> : TypeDef<Pia_Dialect, name> {
  let mnemonic = typeMnemonic;
}

def Pia_IntType : Pia_Type<"Int", "int"> {
  let summary = "an integer constrained to the closed range [lo, hi]";
  let description = [{
    `!pia.int<0, 255>` is `u8`; `!pia.int<0, 255>` from `int{0..255}` is the
    same type. Bounds are stored as 128-bit signed integers so every range
    from i64 and u64 fits. `lo <= hi` is checked by the verifier.
  }];
  let parameters = (ins APIntParameter<"lower bound">:$lo,
                        APIntParameter<"upper bound">:$hi);
  let hasCustomAssemblyFormat = 1;
  let genVerifyDecl = 1;
  let extraClassDeclaration = [{
    /// The number of bits a machine representation needs: 8, 16, 32 or 64.
    unsigned getStorageWidth() const;
    /// Whether any value in the range is negative.
    bool isSigned() const;
    /// Whether `value` (any width) lies in [lo, hi].
    bool contains(const ::llvm::APInt &value) const;
  }];
}

def Pia_ArrayType : Pia_Type<"Array", "array"> {
  let summary = "a fixed-length array whose length the prover knows";
  let parameters = (ins "uint64_t":$length, "::mlir::Type":$elementType);
  let assemblyFormat = "`<` $length `x` $elementType `>`";
}

def Pia_SliceType : Pia_Type<"Slice", "slice"> {
  let summary = "a view of contiguous elements carrying its length at run time";
  let parameters = (ins "::mlir::Type":$elementType);
  let assemblyFormat = "`<` $elementType `>`";
}

def Pia_DynType : Pia_Type<"Dyn", "dyn"> {
  let summary = "a tagged value whose tag is one of the listed types";
  let description = [{
    `!pia.dyn<[!pia.int<0, 255>, f32]>`. Lowering may erase the tag once the
    prover has fixed it; the verifier keeps it (ADR 0003).
  }];
  let parameters = (ins ArrayRefParameter<"::mlir::Type", "tag types">:$tags);
  let assemblyFormat = "`<` `[` $tags `]` `>`";
}

def Pia_AnyInt : Type<CPred<"::llvm::isa<::pia::IntType>($_self)">,
                      "Pia range-typed integer", "::pia::IntType">;
def Pia_Buffer : Type<CPred<"::llvm::isa<::pia::ArrayType, ::pia::SliceType>($_self)">,
                      "Pia array or slice">;
def Pia_Dyn : Type<CPred<"::llvm::isa<::pia::DynType>($_self)">,
                   "Pia dyn value", "::pia::DynType">;

//===----------------------------------------------------------------------===//
// Enums
//===----------------------------------------------------------------------===//

def Pia_OverflowMode : I32EnumAttr<"OverflowMode",
    "what happens when an integer result leaves its type's range", [
      // The default: the verifier must prove it cannot happen (ADR 0004).
      I32EnumAttrCase<"proof", 0>,
      I32EnumAttrCase<"wrap", 1>,
      I32EnumAttrCase<"saturate", 2>,
      I32EnumAttrCase<"trap", 3>,
    ]> {
  let cppNamespace = "::pia";
}

def Pia_CmpPredicate : I32EnumAttr<"CmpPredicate", "an integer comparison", [
      I32EnumAttrCase<"eq", 0>, I32EnumAttrCase<"ne", 1>,
      I32EnumAttrCase<"lt", 2>, I32EnumAttrCase<"le", 3>,
      I32EnumAttrCase<"gt", 4>, I32EnumAttrCase<"ge", 5>,
    ]> {
  let cppNamespace = "::pia";
}

//===----------------------------------------------------------------------===//
// Ops
//===----------------------------------------------------------------------===//

class Pia_Op<string mnemonic, list<Trait> traits = []>
    : Op<Pia_Dialect, mnemonic, traits>;

def Pia_ConstantOp : Pia_Op<"constant", [Pure, ConstantLike]> {
  let summary = "an integer constant of a range type";
  let description = [{
    `%c = pia.constant 42 : !pia.int<0, 255>`. The value must lie in range.
  }];
  let arguments = (ins APIntAttr:$value);
  let results = (outs Pia_AnyInt:$result);
  let hasCustomAssemblyFormat = 1;
  let hasVerifier = 1;
  let hasFolder = 1;
}

class Pia_ArithOp<string mnemonic, list<Trait> traits = []>
    : Pia_Op<mnemonic, !listconcat(traits, [Pure])> {
  let arguments = (ins Pia_AnyInt:$lhs, Pia_AnyInt:$rhs,
                       DefaultValuedAttr<Pia_OverflowMode,
                                         "::pia::OverflowMode::proof">:$overflow);
  let results = (outs Pia_AnyInt:$result);
  let assemblyFormat = [{
    $lhs `,` $rhs (`overflow` `(` $overflow^ `)`)? attr-dict
    `:` type($lhs) `,` type($rhs) `->` type($result)
  }];
}

def Pia_AddOp : Pia_ArithOp<"add", [Commutative]> {
  let summary = "integer addition with an overflow mode";
  let description = [{
    Under `overflow(proof)`, the default, the verifier must prove the exact
    sum lies in the result type. `wrap`, `saturate` and `trap` are the
    opt-in weaker modes (`@overflow(...)`).
  }];
}
def Pia_SubOp : Pia_ArithOp<"sub"> { let summary = "integer subtraction"; }
def Pia_MulOp : Pia_ArithOp<"mul", [Commutative]> { let summary = "integer multiplication"; }

def Pia_CmpOp : Pia_Op<"cmp", [Pure]> {
  let summary = "compare two range-typed integers by value";
  let arguments = (ins Pia_CmpPredicate:$predicate, Pia_AnyInt:$lhs, Pia_AnyInt:$rhs);
  let results = (outs I1:$result);
  let assemblyFormat = "$predicate $lhs `,` $rhs attr-dict `:` type($lhs) `,` type($rhs)";
}

def Pia_ConvertOp : Pia_Op<"convert", [Pure]> {
  let summary = "convert between range types";
  let description = [{
    Widening (the source range lies inside the result range) always holds.
    Narrowing is a proof obligation under the default overflow mode.
  }];
  let arguments = (ins Pia_AnyInt:$input,
                       DefaultValuedAttr<Pia_OverflowMode,
                                         "::pia::OverflowMode::proof">:$overflow);
  let results = (outs Pia_AnyInt:$result);
  let assemblyFormat = [{
    $input (`overflow` `(` $overflow^ `)`)? attr-dict `:` type($input) `->` type($result)
  }];
  let extraClassDeclaration = [{
    /// True when every source value is representable in the result type.
    bool isWidening();
  }];
}

def Pia_LenOp : Pia_Op<"len", [Pure]> {
  let summary = "the length of an array or slice";
  let arguments = (ins Pia_Buffer:$buffer);
  let results = (outs Index:$result);
  let assemblyFormat = "$buffer attr-dict `:` type($buffer)";
  let hasFolder = 1;
}

def Pia_LoadOp : Pia_Op<"load", [MemoryEffects<[MemRead]>]> {
  let summary = "read an element; the index must be proved in bounds";
  let arguments = (ins Pia_Buffer:$buffer, Index:$index);
  let results = (outs AnyType:$result);
  // The result type is the buffer's element type, so the format leaves it
  // out; custom<ElementType> recovers it when parsing.
  let assemblyFormat = [{
    $buffer `[` $index `]` attr-dict `:` type($buffer)
    custom<ElementType>(ref(type($buffer)), type($result))
  }];
  let hasVerifier = 1;
}

def Pia_StoreOp : Pia_Op<"store", [MemoryEffects<[MemWrite]>]> {
  let summary = "write an element; the index must be proved in bounds";
  let arguments = (ins AnyType:$value, Pia_Buffer:$buffer, Index:$index);
  let assemblyFormat = [{
    $value `,` $buffer `[` $index `]` attr-dict `:` type($buffer)
    custom<ElementType>(ref(type($buffer)), type($value))
  }];
  let hasVerifier = 1;
}

def Pia_DynWrapOp : Pia_Op<"dyn.wrap", [Pure]> {
  let summary = "tag a value as dyn";
  let arguments = (ins AnyType:$input);
  let results = (outs Pia_Dyn:$result);
  let assemblyFormat = "$input attr-dict `:` type($input) `->` type($result)";
  let hasVerifier = 1;
}

def Pia_DynIsOp : Pia_Op<"dyn.is", [Pure]> {
  let summary = "test a dyn value's tag";
  let arguments = (ins Pia_Dyn:$input, TypeAttr:$tag);
  let results = (outs I1:$result);
  let assemblyFormat = "$input `,` $tag attr-dict `:` type($input)";
  let hasVerifier = 1;
}

def Pia_DynUnwrapOp : Pia_Op<"dyn.unwrap", [Pure]> {
  let summary = "extract the payload; the tag must be proved to match";
  let arguments = (ins Pia_Dyn:$input);
  let results = (outs AnyType:$result);
  let assemblyFormat = "$input attr-dict `:` type($input) `->` type($result)";
  let hasVerifier = 1;
}

#endif // PIA_DIALECT_PIA_TD
