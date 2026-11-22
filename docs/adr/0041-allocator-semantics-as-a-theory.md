# 41. Allocator semantics are a theory, and allocators prove they refine it through ghost state

Date: 2026-11-22

Status: Proposed

## Context

Dean asked whether allocator-specific semantics can be set up as a theory ([ADR 0036](0036-library-theories.md)).

What exists today ([ADR 0026](0026-memory-manager.md), issue #88):

- **Three allocators are proved Pia:** a bump allocator (tests/verify/bump.pia), `with_arena` regions (#70), and a pool of slots with a free stack (tests/verify/pool.pia).
- **Each states its promises in terms of its own representation.** The pool, for example, says "slot `s` is live" as `p.pos.[s] = 65535`, and says the free stack is distinct as `forall j. p.pos.[p.free.[j]] = j`.
- **Every user carries those quantified facts through every call.** Proving pool.pia showed the cost: Z3 would not compose two quantified frame postconditions of `put` until they were restated as one.
- **The usual promises are the same for every allocator:**
  - a block handed out was not live;
  - two live blocks do not overlap;
  - a block given back is dead;
  - a block goes back only to the allocator that handed it out (`owns`).

A theory can state those promises once, as facts about an abstract heap. docs/theories.md, "Allocators", is a working first step: a theory `Alloc` with a bitmask model proves `fresh_apart` and `reuse` from four axioms, and catches a use after give.

What is missing is the link to running code. A theory's sorts are spec-only (ADR 0036), so a pool cannot hold an `Alloc.heap`, and `take` cannot say how it changes one.

Prior art:

- **Dafny and Verus** keep ghost fields and ghost variables that the compiler erases.
- **Verus's `tracked` permissions and Iris's resource algebras** model ownership of memory as ghost resources.
- **VeriFast and the separation-logic tools** describe an allocator by an abstract predicate that its implementation proves it refines.
- **seL4's allocator proofs** relate an abstract heap to concrete free lists through a refinement relation.

## Decision

### 1. `Pia.Mem.Alloc` is a theory with a proved model

The theory has these parts:

- **Sorts and functions:** a sort `heap`, plus `none`, `live`, `take`, `give`, `base` and `size`.
- **Axioms:** none of them quantify over a heap's contents.
  - `take` makes one block live, and `give` makes one block dead.
  - Distinct blocks are `apart`.
  - A size class (step 4) bounds `size`.
- **A model** proves every axiom, as for every entry in docs/theories.md, so nothing is trusted.

### 2. Ghost state: fields and parameters the verifier sees and codegen erases

- **Declaring it:** `ghost` is a new modifier, `(h : ghost Alloc.heap)` or `{ ...; heap : ghost Alloc.heap }`. A ghost place may have a spec-only type.
- **Writing it:** code may assign a spec expression to a ghost place, as in `p.heap <- Alloc.take p.heap s`.
- **The one-way rule:** nothing that is not ghost may read a ghost place. So erasing ghost state cannot change what a program computes.
- **Codegen drops ghost fields and parameters.** The C ABI and the layout ([ADR 0030](0030-published-object-layouts.md)) do not include them.

### 3. Each allocator proves, privately, that it refines `Alloc`

The pool, for example, adds `heap : ghost Alloc.heap` and proves a coupling invariant inside its module: `forall s. Alloc.live p.heap s <==> p.pos.[s] = 65535`.

Its exported contracts mention only the heap:

- `take` ensures `p.heap = Alloc.take (old p.heap) b.i` and `Alloc.live (old p.heap) b.i = false`.
- `give` requires `Alloc.live p.heap b.i`.

The coupling invariant is module state ([ADR 0006](0006-contracts-and-module-state.md)), so it is not in the interface ([ADR 0039](0039-module-and-interface-syntax.md)). Users reason with `Alloc`'s axioms, with no quantifiers.

### 4. A block carries its allocator as a ghost `owner`

A block is `{ i : u16; owner : ghost Alloc.id }`, and `give` requires `b.owner = p.id`. So reuse cannot cross allocators: this is the `owns` fact of ADR 0026.

### 5. `Allocator` the concept refers to `Alloc` the theory

The `Allocator` concept of [ADR 0034](0034-concepts-and-overload-resolution.md) states its requirements with `Alloc`'s functions. So generic code such as `Vec<t, a : Allocator>` is proved once against the theory, not once per allocator.

## Implementation order

1. The theory and the bitmask model in docs/theories.md (done with this ADR).
2. `ghost` parameters and fields: Sema, IRGen, the verifier, and codegen erasure, with an error when code reads a ghost place.
3. pool.pia refines `Alloc` through a ghost heap, and `reuse` proves using only the theory.
4. Owners, then size classes and `general` (the rest of #88).
5. `Allocator` refers to `Alloc`, and Vec stores its allocator (Dean's choice of 2026-11-22).

## Consequences

- Users of every allocator get the same small facts, and proofs get cheaper, because no user quantifies over an allocator's arrays.
- Ghost state is a language feature with uses beyond allocators: lock levels (docs/theories.md, "Lock levels") and units of measure already describe a "ghost argument" that code cannot pass today.
- The one-way rule is enforced by the compiler. Getting it wrong would let erased state change behaviour, so it gets its own error tests.

## Open questions for Dean

1. Should `ghost` be a modifier word like `borrowed` and `mutable`, or an attribute, `@ghost`?
2. Should the coupling invariant be module state, as proposed? The other option is a `requires`/`ensures` pair that every allocator function repeats.
3. Should `Alloc` have one theory with an `id` sort for owners? The other option is one theory instance per allocator, generated by a metaprogram as `machine` is in docs/theories.md.
