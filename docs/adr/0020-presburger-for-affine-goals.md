# 20. Decide affine aliasing and dependence goals with MLIR's Presburger library

Date: 2026-11-21

Status: Accepted

## Context

Several proof goals are about integer sets defined by linear constraints. Examples:

- Two `mutable` borrows must not alias ([design.md](../design.md#function-parameters)). When both are slices of one buffer, this means their index ranges are disjoint.
- A `spread` loop ([ADR 0014](0014-concurrency-model.md)) is legal only if no iteration writes an element that another iteration reads or writes.
- Auto-vectorisation ([ADR 0013](0013-auto-vectorisation.md)) needs the loop-carried dependence distances.
- Loop goals in the verifier often include bounds on affine subscripts such as `xs.[2*i + 1]`.

Each of these asks whether a system of linear equalities and inequalities over integers has a solution. The variables are loop indices, sizes, offsets and lengths, and the system often comes with existential quantifiers. Z3 can decide such systems, but its bit-vector encoding is heavy for this kind of goal. Pairs of loop iterations double the number of variables, and quantifier alternation makes the solver slow or unpredictable.

MLIR ships the Fast Presburger Library (FPL), in `mlir/Analysis/Presburger`. It decides the emptiness of integer sets and relations exactly, using simplex with generalised basis reduction, and computes with arbitrary-precision integers. It can also produce an integer sample point, eliminate variables, and compute unions, intersections and complements. It is part of `@llvm-project//mlir:Analysis`, which the build already depends on.

## Decision

The verifier gets a Presburger stage between interval analysis and SMT. A goal goes to FPL when every term in it is affine in integer variables. Affine means:

- sums of variables
- multiplication by constants
- floor division and modulo by constants
- comparisons

The goal must also have no other side conditions. Examples are aliasing, dependence and affine bounds goals. The stage builds an `IntegerRelation` whose constraints are the following:

- the path condition
- each variable's type range
- the goal's negation

An empty relation means the goal is proved, and the goal is marked `pia.proved = "presburger"`. A non-empty relation gives a sample point, which becomes the counterexample just as a Z3 model would.

Goals outside the affine fragment still go to Z3, as do goals where FPL hits a resource limit. Examples are products of two variables, data-dependent indices, `wrap` arithmetic and anything involving array contents. The stages are tried in a fixed order: intervals, then Presburger, then SMT. The stage that proves a goal is recorded, so certificates and reports say how each goal was proved.

Dependence analysis for `spread` and the vectoriser uses the same relations. The access relations of two iterations are intersected under `i != j`. An empty intersection proves independence. Otherwise the vectoriser reads the distance set from the relation.

## Consequences

- Aliasing and dependence proofs become exact and predictable, with no solver timeouts on the common affine cases.
- The verifier has two decision procedures, so it needs one shared lowering of affine terms. Both stages must also agree on goal semantics. Tests run selected affine goals through both stages and check that they agree.
- FPL works over unbounded integers. Type ranges must therefore always be added as constraints, and `wrap` or `saturate` arithmetic is never sent to FPL.
- No new external dependency is needed. FPL's API is less stable than SMT-LIB, so upgrading the pinned LLVM may require changes in the Presburger stage.
