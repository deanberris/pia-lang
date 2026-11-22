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
include "mlir/Interfaces/SideEffectInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"

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

    /// The argument attribute on a field buffer of a slice of records
    /// naming the argument whose length it shares: `{pia.length_of = 0}`
    /// (docs/irgen.md, "Records").
    static constexpr ::llvm::StringLiteral getLengthOfAttrName() {
      return ::llvm::StringLiteral("pia.length_of");
    }

    /// The unit attribute on a field buffer's load, store or slice after
    /// the first, when a buffer of records is split into one buffer per
    /// field: every copy has the same index and the same length, so the
    /// first carries the bounds goal and the verifier only assumes it for
    /// the others (docs/irgen.md, "Records").
    static constexpr ::llvm::StringLiteral getBoundsSharedAttrName() {
      return ::llvm::StringLiteral("pia.bounds_shared");
    }

    /// The unit attribute on a function whose signature or body had a
    /// buffer of records before it was split into one buffer per field.
    /// The verifier slices its goals automatically (docs/verifier.md,
    /// "Slicing").
    static constexpr ::llvm::StringLiteral getRecordBuffersAttrName() {
      return ::llvm::StringLiteral("pia.record_buffers");
    }

    /// The string attribute on a function that a module exports through
    /// an interface (ADR 0039). Only exported functions get C entry points
    /// when a program is compiled as modules. The value is the module's
    /// path, `"Pixels"`, or empty for a file with no module header. Its C
    /// entry point is mangled `pia$Pixels$blend` unless it has `pia.abi_c`,
    /// and a module's function also keeps its Pia calling convention under
    /// the link symbol `__pia$Pixels$blend`, which importers call.
    static constexpr ::llvm::StringLiteral getExportAttrName() {
      return ::llvm::StringLiteral("pia.export");
    }

    /// The unit attribute on an exported function whose C entry point keeps
    /// its plain name: it is in an `@abi(c)` interface, or it is `main`.
    static constexpr ::llvm::StringLiteral getAbiCAttrName() {
      return ::llvm::StringLiteral("pia.abi_c");
    }

    /// The module path on a function imported from another module's
    /// interface (ADR 0039). Its body is the interface's contract around a
    /// `pia.arbitrary` result, for the verifier; codegen replaces it with
    /// a declaration of the module's link symbol, `__pia$Pixels$blend`.
    static constexpr ::llvm::StringLiteral getImportAttrName() {
      return ::llvm::StringLiteral("pia.import");
    }

    /// The unit attribute on a spec function (`let spec`): pure and total,
    /// usable in contracts, and given to the solver as its definition
    /// (docs/verifier.md, "Spec functions and lemmas").
    static constexpr ::llvm::StringLiteral getSpecAttrName() {
      return ::llvm::StringLiteral("pia.spec");
    }

    /// The unit attribute on a lemma (`let lemma`): proved once, erased
    /// from code; a call adds its postcondition.
    static constexpr ::llvm::StringLiteral getLemmaAttrName() {
      return ::llvm::StringLiteral("pia.lemma");
    }

    /// `@fuel(n)` on a recursive spec function: how many times the
    /// verifier unfolds a recursive call. One by default.
    static constexpr ::llvm::StringLiteral getFuelAttrName() {
      return ::llvm::StringLiteral("pia.fuel");
    }

    // A theory's members (ADR 0036): an abstract spec function has no
    // body, and an axiom is a fact its parameters are quantified over.
    static constexpr ::llvm::StringLiteral getAbstractAttrName() {
      return ::llvm::StringLiteral("pia.abstract");
    }

    static constexpr ::llvm::StringLiteral getAxiomAttrName() {
      return ::llvm::StringLiteral("pia.axiom");
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

def Pia_UnboundedIntType : Pia_Type<"UnboundedInt", "integer"> {
  let summary = "a mathematical integer, with no bounds: Pia's spec-only `int`";
  let description = [{
    `int` without a range (ADR 0036). It may appear only in specifications:
    spec functions, lemmas, contracts and quantifiers. The verifier encodes
    it as the SMT `Int` sort, and codegen never sees it.
  }];
}

def Pia_RealType : Pia_Type<"Real", "real"> {
  let summary = "a mathematical real number: Pia's spec-only `real`";
  let description = [{
    `real` (ADR 0036). Spec-only like `int`; the verifier encodes it as the
    SMT `Real` sort. It is not a floating-point type.
  }];
}

def Pia_SortType : Pia_Type<"Sort", "sort"> {
  let summary = "an uninterpreted sort a theory declares (ADR 0036)";
  let description = [{
    `let theory Lip = sig let sort layer ... end` declares
    `!pia.sort<"Lip.layer">`. Values of a sort are spec-only: the verifier
    encodes it as an uninterpreted SMT sort, and nothing else sees it.
  }];
  let parameters = (ins StringRefParameter<"the sort's qualified name">:$name);
  let assemblyFormat = "`<` $name `>`";
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

def Pia_RecordType : Pia_Type<"Record", "record"> {
  let summary = "a named record of fields, a value like an integer";
  let description = [{
    `!pia.record<"pixel", r : !pia.int<0, 255>, g : !pia.int<0, 255>>` is
    `let pixel = type { r : u8; g : u8 }`. Records are compared by name, so
    two declarations with the same fields are different types.
  }];
  let parameters = (ins StringRefParameter<"the record's name">:$name,
                        ArrayRefParameter<"::mlir::StringAttr", "field names">:$fieldNames,
                        ArrayRefParameter<"::mlir::Type", "field types">:$fieldTypes);
  let hasCustomAssemblyFormat = 1;
  let genVerifyDecl = 1;
  let extraClassDeclaration = [{
    /// The position of the field called `name`, if there is one.
    std::optional<unsigned> fieldIndex(::llvm::StringRef name) const;
  }];
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
def Pia_Record : Type<CPred<"::llvm::isa<::pia::RecordType>($_self)">,
                       "Pia record", "::pia::RecordType">;
def Pia_Exact : Type<CPred<"::llvm::isa<::pia::UnboundedIntType, ::pia::RealType>($_self)">,
                     "Pia spec-only int or real">;
def Pia_Comparable : Type<CPred<"::llvm::isa<::pia::UnboundedIntType, ::pia::RealType, ::pia::SortType>($_self)">,
                          "Pia spec-only int, real or sort value">;
def Pia_IntOrExact : Type<CPred<"::llvm::isa<::pia::IntType, ::pia::UnboundedIntType, ::pia::RealType>($_self)">,
                          "Pia integer, int or real">;
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

def Pia_DivOp : Pia_ArithOp<"div"> {
  let summary = "integer division, rounding toward zero";
  let description = [{
    The divisor must be proved non-zero, whatever the overflow mode.
  }];
}
def Pia_RemOp : Pia_ArithOp<"rem"> {
  let summary = "the remainder of division, with the sign of the dividend";
  let description = [{
    Pia's `%` and `mod`. The divisor must be proved non-zero.
  }];
}

def Pia_BAndOp : Pia_ArithOp<"band", [Commutative]> {
  let summary = "bitwise and";
  let description = [{
    Bitwise operations act on the two's-complement form of the exact
    integers, as if it extended forever to the left, so the exact result
    never depends on a machine width. The result type is checked like any
    other arithmetic result.
  }];
}
def Pia_BOrOp : Pia_ArithOp<"bor", [Commutative]> { let summary = "bitwise or"; }
def Pia_BXorOp : Pia_ArithOp<"bxor", [Commutative]> { let summary = "bitwise exclusive or"; }

def Pia_ShlOp : Pia_ArithOp<"shl"> {
  let summary = "shift left: `lhs * 2^rhs`";
  let description = [{
    The amount must be proved to lie in [0, w), w the storage width of the
    left operand's type, whatever the overflow mode. Under `overflow(proof)`
    the exact product must also fit the result type, so no bit is lost.
  }];
}
def Pia_ShrOp : Pia_ArithOp<"shr"> {
  let summary = "arithmetic shift right: `floor(lhs / 2^rhs)`";
  let description = [{
    The amount must be proved to lie in [0, w) as for `shl`. Unsigned
    values shift in zeros and signed ones copy the sign bit.
  }];
}

// Bit counting, byte swapping and rotation (docs/stdlib.md, group 2). Each
// works on the storage bits of an unsigned operand, whose width w is that
// of its type's machine integer (8, 16, 32 or 64), and its result type is
// exact, so none can overflow.
class Pia_BitOp<string mnemonic> : Pia_Op<mnemonic, [Pure]> {
  let arguments = (ins Pia_AnyInt:$input);
  let results = (outs Pia_AnyInt:$result);
  let assemblyFormat = [{
    $input attr-dict `:` type($input) `->` type($result)
  }];
}

def Pia_ClzOp : Pia_BitOp<"clz"> {
  let summary = "count leading zero bits: w for zero; result in [0, w]";
}
def Pia_CtzOp : Pia_BitOp<"ctz"> {
  let summary = "count trailing zero bits: w for zero; result in [0, w]";
}
def Pia_PopcountOp : Pia_BitOp<"popcount"> {
  let summary = "count set bits; result in [0, w]";
}
def Pia_BSwapOp : Pia_BitOp<"bswap"> {
  let summary = "reverse the order of the w / 8 bytes; result in [0, 2^w)";
}

class Pia_RotateOp<string mnemonic> : Pia_Op<mnemonic, [Pure]> {
  let arguments = (ins Pia_AnyInt:$value, Pia_AnyInt:$amount);
  let results = (outs Pia_AnyInt:$result);
  let assemblyFormat = [{
    $value `,` $amount attr-dict `:` type($value) `,` type($amount) `->` type($result)
  }];
}

def Pia_RotlOp : Pia_RotateOp<"rotl"> {
  let summary = "rotate the w storage bits left";
  let description = [{
    The amount must be proved to lie in [0, w), as for `shl`. The result is
    in [0, 2^w).
  }];
}
def Pia_RotrOp : Pia_RotateOp<"rotr"> {
  let summary = "rotate the w storage bits right";
  let description = [{
    The amount must be proved to lie in [0, w), as for `shr`.
  }];
}

def Pia_ToIndexOp : Pia_Op<"to_index", [Pure]> {
  let summary = "use a range-typed integer as an index";
  let description = [{
    Indices are MLIR `index` values. The input must be proved non-negative
    when its type allows negative values.
  }];
  let arguments = (ins Pia_AnyInt:$input);
  let results = (outs Index:$result);
  let assemblyFormat = "$input attr-dict `:` type($input)";
}

def Pia_FromIndexOp : Pia_Op<"from_index", [Pure]> {
  let summary = "read an index as a range-typed integer";
  let description = [{
    The index must be proved to lie in the result type's range, which is
    immediate for `usize`.
  }];
  let arguments = (ins Index:$input);
  let results = (outs Pia_AnyInt:$result);
  let assemblyFormat = "$input attr-dict `:` type($result)";
}

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

def Pia_ConstArrayOp : Pia_Op<"const_array", [Pure]> {
  let summary = "an array of constant integers, placed in read-only data";
  let description = [{
    `[1; 2; 3]` where an array is expected, and module-level constant
    arrays such as `let crc_table : [u32; 256] = [...]`. Each value is an
    integer attribute; `label`, when present, is the constant's Pia name.
  }];
  let arguments = (ins ArrayAttr:$values, OptionalAttr<StrAttr>:$label);
  let results = (outs Pia_ArrayType:$result);
  let assemblyFormat = "$values (`label` $label^)? attr-dict `:` type($result)";
  let hasVerifier = 1;
}

def Pia_SliceOp : Pia_Op<"slice", [Pure]> {
  let summary = "a view of elements [lo, hi) of a buffer";
  let description = [{
    `xs.[lo .. hi]`. The view shares the buffer's storage, so a write
    through it is a write to the buffer. The bounds must be proved:
    `0 <= lo <= hi <= len xs`, in every mode.
  }];
  let arguments = (ins Pia_Buffer:$buffer, Index:$lo, Index:$hi);
  let results = (outs Pia_SliceType:$result);
  let assemblyFormat = [{
    $buffer `[` $lo `,` $hi `]` attr-dict `:` type($buffer) `->` type($result)
  }];
  let hasVerifier = 1;
}

def Pia_EmptyOp : Pia_Op<"empty", [Pure]> {
  let summary = "a slice with no elements";
  let description = [{
    The value of a slice that nothing reads: an unused payload of a variant,
    such as the `Ok` field of `Err e` in `result [u8] e`. It has length 0,
    so every load or store through it is out of bounds.
  }];
  let results = (outs Pia_SliceType:$result);
  let assemblyFormat = "attr-dict `:` type($result)";
}

def Pia_RegionOp : Pia_Op<"region"> {
  let summary = "a fresh array of zeroed elements: a `with_arena`'s memory";
  let description = [{
    `with_arena 256 (let (a) => body)` (#70): storage of a fixed size that
    lives until `body` ends, and that nothing allocated in it outlives.
    Each time it is reached it is a new array, distinct from every other
    buffer, with every element zero. It lowers to stack memory.
  }];
  let results = (outs Pia_ArrayType:$result);
  let assemblyFormat = "attr-dict `:` type($result)";
}

def Pia_ViewOp : Pia_Op<"view"> {
  let summary = "a slice of foreign memory: `unsafe view addr n`";
  let description = [{
    The `n` elements at the address `addr`, such as pages a foreign `mmap`
    returned. Nothing proves that the memory is there, or that it overlaps
    no other buffer: `unsafe` says the caller vouches for both, and the
    trust report lists it. The verifier sees a new buffer of `n` elements
    whose contents it does not know.
  }];
  let arguments = (ins Pia_AnyInt:$address, Index:$length);
  let results = (outs Pia_SliceType:$result);
  let assemblyFormat = [{
    $address `,` $length attr-dict `:` type($address) `->` type($result)
  }];
}

def Pia_AbortOp : Pia_Op<"abort"> {
  let summary = "stop the program; proved unreachable in proof mode";
  let description = [{
    `abort ()`. Its precondition is `false`, so the verifier proves that no
    path reaches it. Reached anyway (through `--allow-unproved`), it traps.
    Its result, when the context wants one, is never produced.
  }];
  let results = (outs Variadic<AnyType>:$results);
  let assemblyFormat = "attr-dict (`:` type($results)^)?";
}

def Pia_ArbitraryOp : Pia_Op<"arbitrary"> {
  let summary = "a value the verifier knows nothing about";
  let description = [{
    The result of an imported function (ADR 0039), whose body lives in
    another module: between the interface's `requires` and `ensures`, it
    stands for whatever that body returns. Only the verifier sees it, since
    codegen replaces an imported function's body with a declaration.
  }];
  let results = (outs AnyType:$result);
  let assemblyFormat = "attr-dict `:` type($result)";
}

def Pia_ForeignOp : Pia_Op<"foreign"> {
  let summary = "call a C function: the body of an `extern` declaration";
  let description = [{
    `%r = pia.foreign "crc32_z"(%crc, %buf, %n) : (...) -> ...` is the whole
    body of `let crc32_z ... = extern "crc32_z"` (#55). The verifier never
    looks inside: callers rely on the declaration's contract, which is
    trusted. Codegen calls the C symbol, passing a buffer as its data
    pointer.
  }];
  let arguments = (ins StrAttr:$symbol, Variadic<AnyType>:$args);
  let results = (outs Variadic<AnyType>:$results);
  let assemblyFormat = [{
    $symbol `(` $args `)` attr-dict `:` functional-type($args, $results)
  }];
}

def Pia_RecordOp : Pia_Op<"record", [Pure]> {
  let summary = "build a record from its fields, in declaration order";
  let description = [{
    `%p = pia.record(%r, %g : !pia.int<0, 255>, !pia.int<0, 255>) : !pia.record<...>`
  }];
  let arguments = (ins Variadic<AnyType>:$fields);
  let results = (outs Pia_Record:$result);
  let assemblyFormat = [{
    `(` ($fields^ `:` type($fields))? `)` attr-dict `:` type($result)
  }];
  let hasVerifier = 1;
}

def Pia_FieldOp : Pia_Op<"field", [Pure]> {
  let summary = "read a field of a record";
  let description = [{ `%r = pia.field %p, "r" : !pia.record<...> -> !pia.int<0, 255>` }];
  let arguments = (ins Pia_Record:$input, StrAttr:$field);
  let results = (outs AnyType:$result);
  let assemblyFormat = [{
    $input `,` $field attr-dict `:` type($input) `->` type($result)
  }];
  let hasVerifier = 1;
  let hasFolder = 1;
  let extraClassDeclaration = [{
    /// The field's position in the record type.
    unsigned getIndex();
  }];
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

//===----------------------------------------------------------------------===//
// Spec-only arithmetic on int and real (ADR 0036, step 1)
//===----------------------------------------------------------------------===//

def Pia_ExactConstantOp : Pia_Op<"exact.constant", [Pure]> {
  let summary = "a constant of the spec-only int or real";
  let description = [{
    `%c = pia.exact.constant "3/2" : !pia.real`. The value is an exact
    rational in lowest terms, written `n` or `n/d` with `d > 1`. An `int`
    constant has no denominator.
  }];
  let arguments = (ins StrAttr:$value);
  let results = (outs Pia_Exact:$result);
  let assemblyFormat = "$value attr-dict `:` type($result)";
  let hasVerifier = 1;
}

class Pia_ExactArithOp<string mnemonic, list<Trait> traits = []>
    : Pia_Op<"exact." # mnemonic, !listconcat(traits, [Pure, SameOperandsAndResultType])> {
  let arguments = (ins Pia_Exact:$lhs, Pia_Exact:$rhs);
  let results = (outs Pia_Exact:$result);
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` type($result)";
}

def Pia_ExactAddOp : Pia_ExactArithOp<"add", [Commutative]> {
  let summary = "exact addition of ints or reals; it cannot overflow";
}
def Pia_ExactSubOp : Pia_ExactArithOp<"sub"> {
  let summary = "exact subtraction of ints or reals";
}
def Pia_ExactMulOp : Pia_ExactArithOp<"mul", [Commutative]> {
  let summary = "exact multiplication of ints or reals";
}
def Pia_ExactDivOp : Pia_ExactArithOp<"div"> {
  let summary = "real division; the divisor must be proved non-zero";
  let hasVerifier = 1;
}

def Pia_ExactCmpOp : Pia_Op<"exact.cmp", [Pure, SameTypeOperands]> {
  let summary = "compare two ints or two reals, or two values of a sort for equality";
  let arguments = (ins Pia_CmpPredicate:$predicate, Pia_Comparable:$lhs, Pia_Comparable:$rhs);
  let hasVerifier = 1;
  let results = (outs I1:$result);
  let assemblyFormat = "$predicate $lhs `,` $rhs attr-dict `:` type($lhs)";
}

def Pia_ExactConvertOp : Pia_Op<"exact.convert", [Pure]> {
  let summary = "an integer as an int or a real, exactly";
  let description = [{
    A range-typed integer to `int` or `real`, or an `int` to `real`. Every
    such conversion is exact, so it raises no goal.
  }];
  let arguments = (ins Pia_IntOrExact:$input);
  let results = (outs Pia_Exact:$result);
  let assemblyFormat = "$input attr-dict `:` type($input) `->` type($result)";
  let hasVerifier = 1;
}

#endif // PIA_DIALECT_PIA_TD
