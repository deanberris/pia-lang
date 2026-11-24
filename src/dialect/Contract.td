//===- Contract.td - The pia_contract dialect --------------------*- tablegen -*-===//
//
// Contracts and proof obligations as ops, so they can reference SSA values
// and be verified, transformed and erased by ordinary passes (ADR 0018). The
// dialect lives from IRGen to the end of verification, then is erased.
//
// MLIR dialect namespaces cannot contain '.', so the docs' `pia.contract` is
// spelled `pia_contract` in IR.
//
//===----------------------------------------------------------------------===//

#ifndef PIA_DIALECT_CONTRACT_TD
#define PIA_DIALECT_CONTRACT_TD

include "mlir/IR/DialectBase.td"
include "mlir/IR/EnumAttr.td"
include "mlir/IR/OpBase.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

def Contract_Dialect : Dialect {
  let name = "pia_contract";
  let summary = "Pia contracts, quantifiers and proof obligations";
  let cppNamespace = "::pia::contract";
}

class Contract_Op<string mnemonic, list<Trait> traits = []>
    : Op<Contract_Dialect, mnemonic, traits>;

// Clauses. Each takes an i1 predicate computed from SSA values in scope.

def Contract_RequiresOp : Contract_Op<"requires"> {
  let summary = "a precondition: callers must prove it, the body may assume it";
  let arguments = (ins I1:$predicate);
  let assemblyFormat = "$predicate attr-dict";
}

def Contract_ReadsOp : Contract_Op<"reads"> {
  let summary = "a spec function's footprint: the cells lo up to hi of a buffer";
  let description = [{
    `reads xs.[lo .. hi]` on a spec function (ADR 0060, section 3). Where a
    buffer's contents change only outside the footprint, a call on the new
    contents equals the call on the old; the generated frame lemma
    `f'frame` proves it.
  }];
  // With an owner, the footprint is the cells c with owner[c] = lo, and
  // hi is unused: `reads xs.[c] where owner.[c] = v`.
  let arguments = (ins AnyType:$buffer, AnyType:$lo, AnyType:$hi,
                       Optional<AnyType>:$owner);
  let assemblyFormat = "$buffer `[` $lo `,` $hi `]` (`by` $owner^)? attr-dict `:` type($buffer) `,` type($lo) `,` type($hi) (`,` type($owner)^)?";
}

def Contract_EnsuresOp : Contract_Op<"ensures"> {
  let summary = "a postcondition the body must establish at every return";
  let arguments = (ins I1:$predicate);
  let assemblyFormat = "$predicate attr-dict";
}

def Contract_InvariantOp : Contract_Op<"invariant"> {
  let summary = "a loop invariant: holds on entry and is preserved by each iteration";
  let arguments = (ins I1:$predicate);
  let assemblyFormat = "$predicate attr-dict";
}

def Contract_DecreasesOp : Contract_Op<"decreases"> {
  let summary = "a termination measure that strictly decreases and is bounded below";
  let arguments = (ins AnyType:$measure);
  let assemblyFormat = "$measure attr-dict `:` type($measure)";
}

def Contract_TriggerOp : Contract_Op<"trigger"> {
  let summary = "a trigger of the enclosing axiom: the terms that instantiate it";
  let description = [{
    `@trigger(seq f g)` on a theory's axiom (ADR 0036). Its terms form one
    pattern, which together must mention every parameter of the axiom.
  }];
  let arguments = (ins Variadic<AnyType>:$terms);
  let assemblyFormat = "$terms attr-dict `:` type($terms)";
}

def Contract_AssertOp : Contract_Op<"assert"> {
  let summary = "a goal the verifier must prove at this point";
  let arguments = (ins I1:$predicate);
  let assemblyFormat = "$predicate attr-dict";
}

def Contract_HavocOthersOp : Contract_Op<"havoc_others"> {
  let summary = "forget the cells of a buffer that another iteration owns";
  let description = [{
    At the end of a `spread` iteration (ADR 0060): every cell of `buffer`
    that iteration `iv` does not own takes an unknown value, so that the
    `spread`'s `ensures` is proved whatever the other iterations write.
    Iteration `iv` owns cell `c` when `owner[c] = iv`, or, without an
    owner, when `c = iv`.
  }];
  let arguments = (ins AnyType:$buffer, AnyType:$iv, Optional<AnyType>:$owner);
  let assemblyFormat = "$buffer `,` $iv (`by` $owner^)? attr-dict `:` type($buffer) `,` type($iv) (`,` type($owner)^)?";
}

def Contract_AssumeOp : Contract_Op<"assume"> {
  let summary = "a fact the verifier may use without proof";
  let arguments = (ins I1:$predicate);
  let assemblyFormat = "$predicate attr-dict";
}

def Contract_OldOp : Contract_Op<"old", [Pure, SameOperandsAndResultType]> {
  let summary = "the value of an SSA value on function entry";
  let arguments = (ins AnyType:$value);
  let results = (outs AnyType:$result);
  let assemblyFormat = "$value attr-dict `:` type($value)";
}

// Quantifiers. The body region takes the bound variables as block arguments
// and yields the i1 predicate. The yield carries that predicate, so it is
// always written out: SingleBlock, not SingleBlockImplicitTerminator, which
// needs a terminator it can build with no operands.

class Contract_QuantifierOp<string mnemonic>
    : Contract_Op<mnemonic, [Pure, SingleBlock, RecursiveMemoryEffects]> {
  let arguments = (ins);
  let results = (outs I1:$result);
  let regions = (region SizedRegion<1>:$body);
  let assemblyFormat = "$body attr-dict";
  let hasVerifier = 1;
}

def Contract_ForallOp : Contract_QuantifierOp<"forall"> {
  let summary = "universal quantification over the body's block arguments";
}

def Contract_ExistsOp : Contract_QuantifierOp<"exists"> {
  let summary = "existential quantification over the body's block arguments";
}

def Contract_YieldOp : Contract_Op<"yield", [Pure, Terminator,
    ParentOneOf<["ForallOp", "ExistsOp"]>]> {
  let summary = "yield a quantifier body's predicate";
  let arguments = (ins I1:$predicate);
  let assemblyFormat = "$predicate attr-dict";
}

// Obligations: one op per proof goal, implicit or explicit, so the verifier
// has a single kind of goal to discharge (docs/architecture.md, "Verifier").

def Contract_ObligationKind : I32EnumAttr<"ObligationKind", "where a proof goal came from", [
      I32EnumAttrCase<"requires_", 0, "requires">, // a callee's precondition at a call site
      I32EnumAttrCase<"ensures", 1>,    // a postcondition at a return
      I32EnumAttrCase<"invariant", 2>,
      I32EnumAttrCase<"decreases", 3>,
      I32EnumAttrCase<"assert_", 4, "assert">,
      I32EnumAttrCase<"inbounds", 5>,   // an index is within its buffer
      I32EnumAttrCase<"nooverflow", 6>, // an `overflow(proof)` result fits its type
      I32EnumAttrCase<"exhaustive", 7>, // a match covers every tag
      I32EnumAttrCase<"outwritten", 8>, // an `out` parameter is fully written
      I32EnumAttrCase<"law", 9>,        // a concept law for one instance
      I32EnumAttrCase<"nonzero", 10>,   // a divisor is not zero
      I32EnumAttrCase<"shift", 11>,     // a shift amount is below the width
      I32EnumAttrCase<"emptyslot", 12>, // an owning element written over owns nothing
    ]> {
  let cppNamespace = "::pia::contract";
}

def Contract_ObligationOp : Contract_Op<"obligation"> {
  let summary = "a proof goal tied to its source location";
  let description = [{
    `pia_contract.obligation nooverflow %ok loc("pixels.pia":3:42)`. The
    verifier proves `%ok` or reports a counterexample at the op's location.
  }];
  let arguments = (ins Contract_ObligationKind:$kind, I1:$goal);
  let assemblyFormat = "$kind $goal attr-dict";
}

#endif // PIA_DIALECT_CONTRACT_TD
