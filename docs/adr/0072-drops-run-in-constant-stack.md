# 72. A drop never grows the stack: every drop is one walk, proved against the recursive drop, with a fixed stack bound per type

Date: 2026-11-27

Status: Proposed

## Context

Dean (2026-11-27): "I want to think about the recursive drop case where we can get stack overflows. Independent of whether or not there's recursion actually happening, for deep enough drop calls we need to be mindful of the stack usage. We should figure out whether we need to do some sort of mark-sweep instead of the naive calls to drop recursively."

And, after a first cut that bounded drop depth by a lint: "If we are guarding for stack overflow, we need to make drop never be the cause of it. I'd like us to use a proof to maintain that a drop never causes a stack overflow with a theory, and make sure the implementation is correct. ... Local reasoning in a function's scope cannot be a proxy for global reasoning during runtime. So let's avoid that trap. What I do want to know is whether there's ever a case when we need to do this stack-based drop, or whether we can always rely on the mark and sweep approach."

A naive drop calls the drop of each field, which calls the drop of each of its fields, one stack frame per level of nesting. How deep that goes depends on the value:

- A value of a type that is not recursive nests as deeply as its type does. A `box (box (box u8))` is three levels, whatever is in it.
- A value of a recursive type ([ADR 0047](0047-recursive-sum-types-and-shared-references.md)) nests as deeply as it was built: a list a million long is a million levels.
- A `box c` ([ADR 0046](0046-box-over-a-type-or-a-concept.md)) hides its type. If a type that meets `c` holds a `box c`, as a node of a heterogeneous list does, `box c` is recursive through the concept, though no `let rec` says so.
- A `ref t` drops its value when its last strong reference goes (ADR 0047, section 5), so a chain of last references is a recursive drop too.

ADR 0047's section 4 says the generated drop of a recursive type runs in constant stack, by a loop and a worklist kept in the memory of the nodes being freed. This ADR answers Dean's question, that no drop ever needs to recurse, and says what is proved and how.

### Prior art

- **Rust** drops recursively, so dropping a long `Box`-linked list overflows the stack; the fix is a hand-written `Drop` that loops with `take()`, and a tree needs an explicit stack. **C++**'s `unique_ptr` chains have the same problem.
- **Garbage collectors** mark with an explicit stack or by **Deutsch–Schorr–Waite pointer reversal** (1967), which walks a graph in constant extra space by turning each pointer it follows around to point back where it came from, and restoring it on the way out. Its correctness is a classic of verification: Bornat (2000) proved it in Jape, Mehta and Nipkow (2003) in Isabelle/HOL, and Hubert and Marché (2005) in Why/Caduceus.
- **Swift** and **Koka** release counted references iteratively where the compiler can see the chain.

## Decision

### 1. What is claimed, and what is not

The claim is about drop alone, so it is local and decidable: **for every type `t` there is a number of bytes `S(t)`, fixed when `t` is compiled, such that dropping any value of `t` uses at most `S(t)` bytes of stack beyond the frame of the code that drops it, whatever the value holds.** Dropping a list of ten nodes and one of ten million uses the same stack.

Nothing is claimed about the whole program's stack. Whether a program overflows depends on how deep its calls go at run time, which no check in one function's scope can bound, and this ADR does not try. What it guarantees is that a drop is never the cause: a program that has `S(t)` bytes left where it drops a `t` cannot overflow in that drop, and `S(t)` is small and known. A whole-program stack bound, if one is wanted later, would be a cost bound on a `stack` counter ([ADR 0062](0062-cost-bounds-in-contracts.md)), proved by the program's own contracts, and is outside this ADR.

### 2. Every drop is a walk; no drop recurses

There is never a case that needs a recursive drop. Every drop, of every type, is one walk: a loop over a fixed-size state that visits the value's parts in order, drops each part's own fields, and frees each slot. Each way a value can hold another is covered:

- **An owned child out of line**, through `box`, the last `ref`, or a `box c`: the walk descends by **pointer reversal**. It turns the child's pointer in the parent around to point to the parent's parent, keeps which child it took in the pointer's low bits, and restores nothing on the way up, since the parent is being freed. A slot that holds a pointer is aligned to at least eight bytes on both targets ([ADR 0049](0049-targets-are-theories.md)), so three low bits are always free; a node with more out-of-line children than they can count keeps its cursor in the pointer slot of a child it has already dropped, which exists once the cursor is past the first child, whose number the low bits can hold.
- **A buffer of owned children**, `vec t` or a slice of boxes ([ADR 0048](0048-buffers-whose-elements-hold-slices.md)): the cursor is the buffer's own length, counted down as its elements are dropped, so it needs no extra room.
- **A child inline**, a record field or a fixed array of records: its place is a fixed offset in its parent, so the walk's state for it is a position in the type, not in the value. The type's own nesting is fixed, so this state has a fixed size, and in practice it compiles to the same straight-line code a nested drop would.
- **A variant**: its tag says which payload to walk.
- **A hand-written `drop`**: a step of the walk (section 4).
- **A `box c`**: its table's drop entry (ADR 0071, section 6) is a step of the walk, which hands back the boxes of `c` it finds instead of dropping them (section 5).

A type with no recursive indirection compiles to straight-line code, as today, because every position its walk can reach is known; reversal appears only at an indirection that can lead back to the same type. So the uniform walk costs nothing where the naive drop was already fine, and it is the only drop, so there is no second implementation to keep in step.

### 3. Order

The walk drops children in declaration order, depth first, and a node's own fields after its children, as the recursive drop would. A value whose fields close files or release locks does so in the same order however deep it is, and slots are freed after everything in them is dropped. Section 6 proves this order.

### 4. Hand-written drops

A type may have its own `drop` (#85). Its body is ordinary Pia, run as one step of the walk:

- It sees the node's fields other than the owned children the walk descends into, which the compiler drops after it.
- Its call graph may not cycle. A call that can reach itself from a `drop`, directly or through other functions, is an error, `drop_recursion`. This is a check of which functions call which, not of whether a loop terminates, so it asks nothing undecidable: loops are fine, and they cost no stack. Every value the body drops is dropped by its own walk.
- With no cycle, the body's stack is the largest sum of frames along a path in its call graph, which codegen reads from LLVM's frame sizes. That is part of `S(t)`.
- A drop that is an `extern` ([ADR 0057](0057-posix-module-per-target-behind-one-interface.md)'s bindings, a C destructor) runs C code whose stack Pia cannot see. It must state its bound, `@stack(256)`, which is trusted and listed in the trust report, like every `extern` contract.

### 5. Through `box c` and `ref`

- **`box c`.** When a type that meets `c` can hold a `box c`, its table's drop entry drops the object's fields that are not boxes of `c`, and returns each `box c` it finds to the walk, which descends into it by reversal. The table stays out of reach of Pia (ADR 0071), so this protocol is the compiler's own.
- **`ref t`.** Releasing a reference that is not the last only decrements its count. Releasing the last one is a descent into the value, so a chain of last references unwinds in the same walk.

### 6. The theory and the proof

The claim is a theorem in a library theory, `Pia.Drop` ([ADR 0036](0036-library-theories.md)), proved as follows:

- **The meaning.** The theory's spec `drops t v` is the recursive drop, written as the obvious recursive spec function over a value's shape: the sequence of hand-written drop steps it runs and slots it frees, in order. It is never compiled; it is what the walk must equal.
- **The walk, once.** The generic walk is a transition system over a value's shape: a current node, a cursor, and the reversed path. Its invariant is the one the Schorr–Waite proofs use: the reversed path, read back, is exactly the continuation the recursion would hold on its stack. Its measure is the number of parts not yet visited. From these, the walk terminates, runs exactly `drops t v`, frees each slot once, and keeps a state of fixed size. This proof is done once, in Lean ([ADR 0061](0061-lean-proved-facts.md)), for every shape the type grammar allows, and its statement hash is recorded in the compiler's certificate.
- **Each type.** For each type, the compiler emits its walk's step function as Pia, against the type's layout, and Z3 proves that it refines the generic step for that shape: the same next state for every state. These are small, quantifier-free goals, one per kind of position in the type.
- **The bound.** `S(t)` is the walk's frame plus the largest stack of any step it calls (section 4). The walk has no call cycle and no dynamically sized frame, which codegen checks after LLVM has fixed the frames, and refuses to emit otherwise. The machine fact it rests on, that a call graph with no cycle and fixed frames uses at most its largest path's frames, is an axiom of the `Pia.Target` theory, true of both targets' calling conventions.

What the verifier sees of a drop in an ordinary program does not change: it is still the type's `drop` contract, and each node is still dropped exactly once.

### 7. What programs see

- `--verify-stats` reports `S(t)` for every type a module drops, and the largest in each function.
- The lint `deep_drop` remains for one case only, a hand-written drop whose own body's stack is more than an eighth of the target's task stack (`task_stack_bytes` in `Pia.Target`: 512 KiB on arm64 macOS, 8 MiB on x86_64 Linux). It names the call path. No other drop can be large.
- Nothing about drop depends on how large a value is, so there is no depth limit and no flag for one.

## Implementation order

Each step is a PR with tests in `tests/codegen` run from C, and the skills updated as features land.

1. **The theory.** `Pia.Drop` with `drops t v`, the generic walk, and the Lean proof of section 6, with its certificate entry.
2. **The walk for every shape.** Lists, trees, buffers, inline fields and variants; the per-type refinement goals; `S(t)` in `--verify-stats`; codegen's check that drops have no cycle and fixed frames. Tests: a list of a million nodes and a left-leaning tree of a million nodes dropped on a thread with a 64 KiB stack, with the order of their drops checked, under the sanitizers ([ADR 0025](0025-sanitizers.md)).
3. **Hand-written drops** as steps, `drop_recursion`, `@stack` on `extern` drops, and the `deep_drop` lint.
4. **`box c` and `ref`**, after ADR 0071's tables: a heterogeneous list of `box Shape` a million long, and a chain of last references.

## Consequences

- No drop can overflow the stack because a value is large, and no drop allocates, so dropping never fails.
- There is one drop implementation, proved once against the recursive meaning and refined per type, rather than a fast recursive drop and a safe iterative one.
- Drops run in the order a programmer reads from the recursive definition.
- A hand-written drop of a recursive type sees less than it would in Rust or C++: its owned children are the compiler's to drop, and it may not recurse.
- Pointer reversal writes into the value being dropped. That is safe because it is owned uniquely and about to be freed, and ADR 0042's loan rules already forbid dropping a value another task borrows.
- The claim stops at drop. A program can still overflow its stack by calling too deep, which is a property of the program's own calls, as it is in every language.

## Questions for Dean

1. **Lean for the generic proof.** Section 6 proves the generic walk once in Lean, since its invariant is an induction over the reversed path that Z3 does not do well, and per-type refinements in Z3. Is Lean acceptable here (recommended), or should the generic proof also be in Z3, at the cost of bounding the shapes it covers?
