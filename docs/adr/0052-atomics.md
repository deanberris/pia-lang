# 52. Atomics are a core cell type with checked memory orders, proved as if any task may write between two accesses, and lowered per target by a proved table

Date: 2026-11-23

Status: Proposed

## Context

Pia has no atomics. [ADR 0027](0027-coroutines-and-race-freedom.md) designs them as `atomic<T>` in `Pia.Sync`, with every operation taking a memory order, `seq_cst`, `acquire`, `release` and `acq_rel` checked from the start, and `relaxed` unproved until the model checker has an RC11 mode, except where the value read orders nothing. [stdlib.md](../stdlib.md#10-simd-floats-and-atomics) lists the operations as core builtins for milestone M12. Neither says how the verifier sees an atomic, how the orders are checked, or what each target emits.

Three pieces of accepted or proposed work are waiting on them:

- **ADR 0049, section 4.** Dean accepted that `@target(x86_64_linux)` code may rely on TSO, provided it is proved at compile time: after optimisation, every atomic access in such an item must still be an acquire or release access. Step 3d of that ADR cannot be built without atomics to check. The same section asks for per-target lemmas proving that the instructions chosen for each order give every happens-before edge the language model promises.
- **ADR 0047, `shared_ref`.** Its counts and its lease word are atomic.
- **ADR 0050, io_uring.** Ring heads and tails live in memory shared with the kernel, read with acquire loads and written with release stores.

ADR 0027's primitives (`mutex`, `chan`, `once`, the work-stealing deque) are written over atomics too, but they also need tasks and the model checker, which this ADR does not build.

C and C++ get three things wrong that Pia can do better. A memory order that is wrong for the operation (a `release` load, a `compare_exchange` failure order of `release`) is undefined behaviour in C and quietly strengthened by compilers. An atomic object that is not lock-free silently becomes a lock in `libatomic`. And `memory_order` may be a run-time value, which compilers treat as `seq_cst`.

## Decision

### 1. `atomic t` is a core cell type

`atomic t` holds one value of `t`, which is an integer type (`u8` to `u64`, `i8` to `i64`, `usize`, `isize`) or `bool`, or a refinement of one (section 3). There are no atomic records, floats or 128-bit cells in this ADR.

- **Always lock-free.** Every allowed `t` is 1, 2, 4 or 8 bytes, and both targets do every operation on those widths in one instruction or one `ldxr`/`stxr` loop. `piac` never emits a call to `libatomic`. A future cell type that would need one is a compile error, not a hidden lock.
- **Layout.** Size and alignment are those of `t`, so an `atomic u32` is 4 bytes at 4-byte alignment. A cell that tasks contend for can be padded with `Pia.Sync.padded`, aligned and sized to `Target.cache_line` (128 bytes on Apple silicon, 64 on x86_64), which makes its published layout per target ([ADR 0030](0030-published-object-layouts.md), [ADR 0049](0049-targets-are-theories.md) section 3).
- **A place, not a value.** An atomic cell is reached by borrowing it. Copying one is not atomic, so `atomic t` is not copyable. Moving one is allowed, because a moved value has a single owner and no other task can be touching it.
- **Concepts.** `atomic t` is `sendable` and `shareable` ([ADR 0027](0027-coroutines-and-race-freedom.md)), and it is the only built-in type with interior mutability that is shareable. Two tasks may borrow one cell at once, even both `mutable`, because no access to it is a data race (ADR 0027's rule 5).
- **Creation.** `atomic_new v` makes a cell holding `v`. It is a plain store, since nothing else can see the cell yet.

### 2. Operations are builtins, and their orders are checked

The operations are core builtins, as [stdlib.md](../stdlib.md#10-simd-floats-and-atomics) already lists, with the order first:

| Builtin | Meaning | Orders allowed |
| --- | --- | --- |
| `atomic_load o c` | read | `relaxed`, `acquire`, `seq_cst` |
| `atomic_store o c v` | write | `relaxed`, `release`, `seq_cst` |
| `atomic_swap o c v` | write `v`, return the old value | all five |
| `atomic_cas ok fail c expected desired` | if the value is `expected`, write `desired`; return the old value either way | `ok`: all five. `fail`: `relaxed`, `acquire` or `seq_cst`, and no stronger than `ok` |
| `atomic_add o c v`, `atomic_sub`, `atomic_and`, `atomic_or`, `atomic_xor`, `atomic_min`, `atomic_max` | read, modify, write; return the old value | all five |
| `fence o` | order the surrounding atomics | `acquire`, `release`, `acq_rel`, `seq_cst` |

`atomic_cas` returns the old value, and it succeeded exactly when that equals `expected`, so it needs no tuple. It is the strong form: it never fails spuriously. A weak form is left until a loop needs the difference, which on arm64 with LSE (every Apple silicon CPU) it does not, since `cas` is one instruction.

The five orders are the constants `relaxed`, `acquire`, `release`, `acq_rel` and `seq_cst` of the core type `order`. They are names in the prelude, like `true`, not keywords. An order must be a compile-time constant. An order the table does not allow is a compile error that says which orders the operation takes, so the cases C leaves undefined cannot be written.

**Overflow.** `atomic_add` and `atomic_sub` wrap, like the hardware instructions, so they are written under `@overflow(wrap)`, as `+` would be. Under the default `@overflow(proof)` they are compile errors, since the old value is whatever another task left there and no proof can bound it. A cell that must not wrap is a refined cell, updated with `atomic_update` (section 3).

### 3. The verifier treats every access as if any task wrote just before it

Within one function, the verifier models a cell as a value that another task may change between any two accesses. So:

- `atomic_load` returns a fresh value of `t`, about which the verifier knows only its type.
- `atomic_swap`, `atomic_cas` and the read-modify-writes return a fresh old value. After `atomic_cas`, the verifier knows that it succeeded exactly when the old value equals `expected`, and nothing about the cell afterwards.
- `atomic_store` has no result.

This is sound under every interleaving, because it assumes nothing about other tasks, and it is cheap: no event structure, no new sorts, and no quantifiers. It is also the most a single function can know. Anything that relates the values seen by two tasks (a counter that only grows, a flag that publishes data) is a claim about the whole program, and it belongs to ADR 0027's model checker and to the `Order` theory ([docs/theories.md](../theories.md#happens-before-and-memory-orders)). Code that wants exact values in one task should use a plain `mutable`.

**Refined cells.** When `t` is a refinement, every value stored is a goal: `atomic_store`, `atomic_swap` and the `desired` of `atomic_cas` must be proved to meet the refinement, and every value read may be assumed to meet it. The refinement is then an invariant of the cell that holds across all tasks, proved one store at a time, just as a lock invariant is the refinement of a `mutex`'s data (ADR 0027). The bitwise and arithmetic read-modify-writes are not allowed on a refined cell, since their result is never known. `Pia.Sync.atomic_update o c f` is the replacement: a compare-and-swap loop in the library that calls `f` on the old value and stores its result, and `f`'s result must meet the refinement:

```ocaml
let slots = type { n : u32 | n <= 64 }

let take (c : borrowed atomic slots) : bool
= let old = atomic_update acq_rel c (let (n) => if n > 0 then n - 1 else n) in
  old > 0
```

**`relaxed`.** ADR 0027 accepts `relaxed` only where the value read orders nothing, and otherwise makes it an unproved goal until the RC11 mode. In this ADR's first steps, nothing yet takes a happens-before edge from atomics: without tasks and the model checker, the race prover justifies plain data only by ownership, disjointness and locks. So no `relaxed` access can yet be the thing that orders other data, and every `relaxed` access is accepted. When the race prover starts using happens-before edges from atomics (step 5 below), it must check that no edge it uses rests on a `relaxed` access, and ADR 0027's rule applies from then on.

### 4. Each target lowers the orders by a table that is proved against its hardware model

`piac` emits LLVM `load atomic`, `store atomic`, `atomicrmw`, `cmpxchg` and `fence` with the matching LLVM ordering, and LLVM's backends pick the instructions. Those choices are the standard mappings from C11 to each architecture:

| Order | arm64 (Apple silicon: LSE and RCpc) | x86_64 |
| --- | --- | --- |
| `relaxed` load / store | `ldr` / `str` | `mov` / `mov` |
| `acquire` load | `ldapr` | `mov` |
| `release` store | `stlr` | `mov` |
| `seq_cst` load / store | `ldar` / `stlr` | `mov` / `xchg` |
| read-modify-write, `cas` | `ldadd`, `swp`, `cas` and so on, with `a`, `l` or `al` | `lock xadd`, `xchg`, `lock cmpxchg`; a loop of `lock cmpxchg` for `and`, `or`, `xor`, `min`, `max` when the old value is used |
| `fence acquire`, `release`, `acq_rel` | `dmb ishld` for acquire, `dmb ish` otherwise | nothing (compiler barrier only) |
| `fence seq_cst` | `dmb ish` | `mfence` |

Since Pia trusts LLVM for instruction selection, the table is checked in two halves:

1. **The table is what LLVM emits.** A codegen test per target compiles one function per (operation, order) pair and checks the instructions with FileCheck. A change in the pinned LLVM that picks other instructions fails that test.
2. **The table is proved against the hardware model.** Each target model in `Pia.Target` gains its hardware memory model, as [ADR 0049](0049-targets-are-theories.md) section 4 says: x86-TSO (Owens, Sarkar and Sewell) for x86_64, and the Armv8 axiomatic model (Pulte, Flur, Deacon and others, the one Arm publishes in its herd cat file) for arm64, written as theories of the same shape as `Order`. A compiler lemma per target states that the instructions the table chooses give every happens-before edge the language model promises. The lemmas are proved over the litmus shapes that generate those edges: message passing (MP), store buffering (SB, for `seq_cst`), load buffering (LB), write-read causality (WRC), IRIW and 2+2W, each with every order the table allows, including the fence forms. The general theorem, that these mappings are correct for every program, is the published result of Lahav, Vafeiadis and others for RC11 and of Podkopaev, Lahav and Vafeiadis for Armv8, and Pia cites it rather than reproving it. The lemmas are what catch a wrong entry in Pia's table.

The lemmas live in `src/irgen/Target.pia` beside the models, so the build proves them, as it already proves the models' axioms (`tests/verify/target_theory.pia`).

### 5. On x86_64, code may rely on TSO, and each program proves it did not lose it

This builds ADR 0049 section 4.2 as Dean accepted it.

- **Which code.** The model `x86_64_linux` gains two axioms, `store_releases` (every atomic store releases) and `load_acquires` (every atomic load acquires). Like every model fact, they are visible only inside `@target(x86_64_linux)` items. Target-generic code sees only the `Pia.Target` theory, so it never relies on them.
- **The lowering.** Inside `@target(x86_64_linux)` items, `relaxed` loads are emitted as LLVM `acquire` and `relaxed` stores as `release`. On x86_64 they are the same `mov` instructions, so the only cost is that LLVM may no longer reorder them, which is what the axioms need. Relaxed read-modify-writes are already `lock`-prefixed full barriers on x86_64, so they are emitted as `acq_rel`. Outside `@target(x86_64_linux)`, `relaxed` stays LLVM `monotonic` on both targets, since no proof there can depend on more.
- **The check.** Each atomic access emitted for a `@target(x86_64_linux)` item carries `!pia.tso` metadata naming its source location. After LLVM's optimisation pipeline, and before instruction selection, `piac` checks two things. First, every instruction with `!pia.tso` is still `acquire`, `release`, `acq_rel` or `seq_cst`. Second, every source location tagged before optimisation still has at least one tagged instruction afterwards, so an access the optimiser deleted or merged away is noticed. Inlining and unrolling may copy an access, which is fine, since every copy is checked. A failure is a compile error at the source location, saying that the optimiser weakened or removed an access the proof relied on. A goal that the axioms did not prove would have been proved without them, so the check can be stricter than necessary, never weaker.

With this, `publish_relaxed` from [docs/theories.md](../theories.md#happens-before-and-memory-orders), the message-passing idiom with a `relaxed` flag, proves inside `@target(x86_64_linux)` and fails everywhere else, which is the hardware's behaviour.

### 6. Atomics on foreign memory are `unsafe` views

io_uring's rings and other memory shared with the kernel or another process are not Pia cells. An `unsafe view` of such memory ([stdlib.md](../stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)) can be viewed as atomic cells with `unsafe Pia.Sync.atomic_at v offset : borrowed atomic u32` (and the other widths), with a goal that `offset` is in bounds and aligned to the cell's size. What the other side does is outside Pia's proof, so each such view is a trust item with the citation the module gives, such as io_uring(7) for the ring heads and tails ([ADR 0050](0050-senders-and-receivers.md) section 3).

### 7. Build order

1. **Cells and operations.** `atomic t`, `atomic_new`, the builtins and order checks (section 2), the verifier's view (section 3), refined cells and `atomic_update`, and lowering with LLVM's orderings. Tests: proved uses in `tests/verify/atomics.pia`, order and overflow errors in `tests/irgen`, and the instruction tables for both targets in `tests/codegen`.
2. **The x86_64 TSO lowering and check** (section 5), which is ADR 0049 step 3d.
3. **The hardware models and lowering lemmas** (section 4.2), in `src/irgen/Target.pia`.
4. **Foreign atomic views** (section 6), when `Pia.Io.Uring` needs them, and `padded` with the per-target layout.
5. **Happens-before from atomics for plain data**, with ADR 0027's rule for `relaxed`. This needs tasks (issue #75 onwards) and the model checker, so it is planned there, not here.

## Questions for Dean

1. **`relaxed` lowered to acquire and release only inside `@target(x86_64_linux)`.** ADR 0049 section 4.2 says x86_64 lowers every `relaxed` access that way. Section 5 limits it to the items that may rely on TSO, so target-generic code keeps LLVM's freedom to reorder `relaxed` accesses on x86_64. The instructions are the same either way. The recommendation is to limit it, since only those items can use the axioms.
2. **Overflow of `atomic_add` and `atomic_sub`.** The recommendation is that they wrap and must be written under `@overflow(wrap)`, with refined cells and `atomic_update` for counters that must not wrap. The alternative is a saturating form, which no target has as one instruction and which would be a compare-and-swap loop.
3. **No happens-before from atomics yet.** Until tasks and the model checker exist, atomics give single-function facts only (section 3), and plain data is still published only through ownership and locks. The recommendation is to build sections 1 to 4 now and leave happens-before to the concurrency work, since nothing can yet run two tasks.

## Consequences

- ADR 0049 step 3d can be built: the TSO check has atomics to check, and the lowering lemmas have a table to prove.
- ADR 0047's `shared_ref` and ADR 0050's io_uring rings have the cells and orders they name.
- A wrong memory order, a hidden lock and a run-time order cannot be written.
- The verifier's view of an atomic is weak on purpose: a function proves nothing about values other tasks write. That keeps atomics as cheap to prove as plain code, and leaves cross-task facts to the model checker.
- Refined cells give cross-task invariants with one goal per store, without the model checker.
- Pia trusts LLVM's instruction selection for atomics, but a change in what it emits fails a test, and the table it emits is proved against each hardware model.
- Writing x86-TSO and the Armv8 model as theories is new work, and the litmus lemmas are a cost in compiler build time, tracked by the proof bench ([ADR 0032](0032-parallel-sliced-cached-proving.md)).
