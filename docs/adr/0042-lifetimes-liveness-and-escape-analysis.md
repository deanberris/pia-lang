# 42. Lifetimes are checked by liveness, marked where values cross boundaries, and escape analysis places memory

Date: 2026-11-22

Status: Proposed

## Context

Dean (2026-11-22): the language should have liveness checks for lifetime analysis, and grow explicit lifetime markers on values that cross boundaries. Escape analysis can then decide stack space reuse and generational arena allocation and reuse.

The rules today ([ADR 0026](0026-memory-manager.md), docs/irgen.md, "Bindings and mutation"):

- **Borrows are lexical.** A borrow lasts to the end of the scope of the local that holds it, even after its last use. So a lender stays locked for longer than it needs to be. For example, an allocator cannot be reset after the last use of a buffer taken from it if that buffer's local is still in scope.
- **A lifetime is named by its lender.** `borrowed(m)` on a result or an `inout` parameter says the value may hold a loan from parameter `m`. That is a lifetime marker already, but it exists only in function signatures. A record cannot hold a loan whose lender lives outside it. This is why `Vec` cannot yet store its allocator (ADR 0041, step 5).
- **Moves are checked by flow, and linear values by paths.** These rules (the moved map and `@linear`) already track, per path, whether a value is still usable. That is a liveness question asked in a different form.
- **Memory placement is explicit and fixed.** `with_arena` regions are stack memory made once per function entry. Locals, records and coroutine frames are placed by LLVM alone. Nothing tells LLVM which stack slots are dead, so two `with_arena`s in sequence use two regions of stack.

Prior art:

- **Rust's non-lexical lifetimes (NLL) and Polonius** end a loan at its last use, computed by liveness over the control-flow graph. They also name lifetimes in signatures and in types (`'a`).
- **Cyclone, the ML Kit and Tofte–Talpin regions** pass region parameters explicitly at boundaries and infer them inside bodies.
- **Go and HotSpot** use escape analysis to place an allocation on the stack when it does not escape. **LLVM's stack colouring** reuses slots between `llvm.lifetime.start` and `llvm.lifetime.end`.
- **Generational arenas** come from game engines and from Rust's `generational-arena` and `slotmap` crates. An arena is reset per frame or per request, and each handle carries a generation so that a stale handle can be told apart from a live one.

## Decision

### 1. Liveness ends loans and checks uses

A loan ends at the last use of every value that holds it, not at the end of its scope. A liveness pass over each function's control flow decides this. It treats the following as uses:

- a read, a call argument, a `match`, or a return;
- a scope-end `drop` or `defer` that touches the value, so a value with `Drop` lives until its cleanup runs ([ADR 0028](0028-error-propagation-and-cleanup.md));
- every path out of a handler arm that can still reach the value.

The lexical checks in IRGen become liveness checks, with the same errors. Each error points at the later use that keeps the loan alive. For example:

```
error: 'm' is reset here while 'b' still borrows it
note: 'b' is used later, here
```

Moves and `@linear` values join the same pass. Using a value after it is moved, after its loan ends, or after its generation ends (section 4) is one kind of error: a use of a dead value. Contracts are exempt, as they are today, because they describe values rather than use them.

### 2. Lifetime markers appear only where values cross boundaries

Inside a function body, lifetimes are inferred and never written. A value that crosses a boundary carries an explicit marker, so each boundary can be checked on its own. That keeps modules separately verifiable ([ADR 0039](0039-module-and-interface-syntax.md)).

The boundaries are these:

| Boundary | Marker |
| --- | --- |
| a function's result or `inout`/`out` parameter | `borrowed(m)`, naming the lender parameter (exists) |
| a record or variant field | a region parameter of the type: `let vec (t : type) (r : region) = type { alloc : borrowed(r) inout mutable bump; ... }` |
| a task, `spread` worker or channel send | `borrowed(r)` on what is sent; it must name a region that encloses the task ([ADR 0027](0027-coroutines-and-race-freedom.md)) |
| a coroutine suspension point | inferred, but checked against the frame's region |
| an interface | as in the function or type it lists |

`region` is a builtin type name, like `type`, not a keyword. A region parameter is deduced from the arguments, as a type parameter is ([ADR 0034](0034-concepts-and-overload-resolution.md)), so users write `vec u8 m` or simply `vec`. It is spec-only state ([ADR 0041](0041-allocator-semantics-as-a-theory.md)): codegen erases it, and it costs nothing at run time.

### 3. Escape analysis places the memory the compiler owns

Escape analysis is modular. It reads only signatures and the markers of section 2, and never looks across function bodies. A value escapes its scope if one of these holds:

- it is returned;
- it is stored in a place that outlives the scope;
- it is sent to a task;
- it is passed where a marker lets the callee keep it.

The compiler uses this only for memory it owns: locals, records, `with_arena` regions and coroutine frames. Allocation through an allocator stays explicit (ADR 0026). The compiler never quietly moves an `alloc` call onto the stack, because the call's failure is part of what the program handles.

- **Stack reuse.** Each stack slot gets `llvm.lifetime.start` and `llvm.lifetime.end` at the ends of its live range, so LLVM shares one slot between values that are never live together. That includes `with_arena` regions in sequence.
- **Frame size.** A coroutine frame keeps only the values live across a suspension point, which makes the frame size the compiler proves smaller.
- **Advice.** A lint (ADR 0037) reports an allocation from a long-lived allocator whose result never escapes a loop iteration or a scope. It suggests `with_arena` or a generational arena instead.

### 4. Generational arenas

A generational arena is a `Pia.Mem` allocator for memory whose lifetime is one generation: one loop iteration, one request, one frame or one task run.

- **Reset is O(1).** `next a` ends a generation and starts the next one. It reuses the arena's pages without returning them, so a steady-state loop allocates nothing from the page heap.
- **Generations are spec-only state.** Each loan carries its generation as a spec-only field. Liveness proves that no loan is used after `next`, so no generation check runs in proved code.
- **Run-time generations only where the verifier cannot see.** A handle that leaves proved code, such as one given to C, kept in a REPL session ([ADR 0031](0031-verified-repl-and-live-environment.md)) or sent through an untyped channel, carries a real generation counter. It is checked on the way back in.
- **Escape analysis picks the generation.** The lint in section 3 points at the innermost generation that encloses every use of an allocation. `Alloc` (ADR 0041) states generational arenas as a refinement, so `next` gives back every block live in the old generation.

## Implementation order

1. Liveness-based loan ends in place of the lexical borrow check, with moves and `@linear` in the same pass, and the new error notes.
2. `region` parameters on records and variants, with `borrowed(r)` fields. With this, Vec can store its allocator (ADR 0041, step 5).
3. Markers at task, channel and coroutine boundaries.
4. Stack slot lifetimes in codegen, with a stack-size test of `with_arena`s in sequence.
5. The generational arena in `Pia.Mem`, with its spec-only generations and its `Alloc` refinement.
6. The escape lint, then run-time generations at FFI and REPL boundaries.

## Consequences

- Loans end where they are last used, so fewer correct programs are rejected. A lender is free again as soon as its borrowers are dead.
- The only lifetime syntax is at boundaries: `borrowed(m)` (existing) and region parameters on types. Function bodies stay unannotated.
- Stack use falls without new syntax, and coroutine frames shrink.
- Liveness errors are harder to explain than scope errors, because the cause can be a later use. So each error names that use.

## Questions for Dean

1. **Marker syntax.** Name lifetimes by values (`borrowed(m)`) and by `region` parameters on types, rather than Rust-style `'a`? It adds no keyword, and `'` already means "primed name".
2. **Generations.** Spec-only in proved code, with run-time counters only at FFI and REPL boundaries?
3. **Stack placement.** Should escape analysis place only compiler-owned memory, and advise (through a lint) rather than rewrite `alloc` calls? This keeps allocation explicit and its failures handled.
