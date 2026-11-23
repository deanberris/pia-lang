# 52. Atomics are a core cell type with checked orders and stated overflow, modelled by RC11 with a litmus battery before tasks exist, and lowered per target by a table proved against each hardware model

Date: 2026-11-23

Status: Accepted (Dean, 2026-11-23), with his answers folded in: `relaxed` becomes acquire and release only inside `@target(x86_64_linux)` items; atomic arithmetic always states its overflow handling, and the lowering uses what each target does; and the memory model is modelled now, with a battery of litmus tests, so that tasks have it ready when they land.

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
| `atomic_add o c v`, `atomic_sub` (each with its overflow mode, below), `atomic_and`, `atomic_or`, `atomic_xor`, `atomic_min`, `atomic_max` | read, modify, write; return the old value | all five |
| `fence o` | order the surrounding atomics | `acquire`, `release`, `acq_rel`, `seq_cst` |

`atomic_cas` returns the old value, and it succeeded exactly when that equals `expected`, so it needs no tuple. It is the strong form: it never fails spuriously. A weak form is left until a loop needs the difference, which on arm64 with LSE (every Apple silicon CPU) it does not, since `cas` is one instruction.

The five orders are the constants `relaxed`, `acquire`, `release`, `acq_rel` and `seq_cst` of the core type `order`. They are names in the prelude, like `true`, not keywords. An order must be a compile-time constant. An order the table does not allow is a compile error that says which orders the operation takes, so the cases C leaves undefined cannot be written.

**Overflow.** `atomic_add` and `atomic_sub` never take an overflow mode from anywhere else: each one states its own, as `@wrap (atomic_add o c v)` or the other three forms ([design.md](../design.md)), and one without a mode is a compile error, even inside an `@overflow(...)` function. Nothing is assumed about what the hardware does on overflow. The four modes keep their ordinary meanings, and each target lowers them by what its instructions do:

| Mode | Meaning | arm64 | x86_64 |
| --- | --- | --- | --- |
| `wrap` | modular | `ldadd` | `lock xadd` |
| `trap` | the program traps when the result does not fit; the cell already holds the wrapped value, and other tasks may read it before the program stops, so `trap` is for counters whose overflow is a bug | `ldadd`, then the overflow is computed from the old value it returns (`old > max - v`) | `lock xadd` or `lock add`, then `jo` or `jc` on the flags the instruction set |
| `saturate` | the result is clamped, and no wrapped value is ever stored | a compare-and-swap loop | a compare-and-swap loop |
| `proof` | the result must be proved to fit for every value the cell's type allows | `ldadd` | `lock xadd` |

The target model says which of these a target has: `x86_64_linux` sets `rmw_flags = true`, because a `lock`-prefixed add sets the overflow and carry flags, and `arm64_macos` sets it to `false`, because LSE's `ldadd` sets none. The verifier sees the same meaning on both targets, so no proof depends on the value. Codegen reads it, and the lowering lemmas of section 5 prove each entry. `proof` mode is rarely provable on a cell of a plain integer type, since another task may have left any value there. It is meant for refined cells (section 3), where the refinement bounds the old value.

### 3. The verifier treats every access as if any task wrote just before it

Within one function, the verifier models a cell as a value that another task may change between any two accesses. So:

- `atomic_load` returns a fresh value of `t`, about which the verifier knows only its type.
- `atomic_swap`, `atomic_cas` and the read-modify-writes return a fresh old value. After `atomic_cas`, the verifier knows that it succeeded exactly when the old value equals `expected`, and nothing about the cell afterwards.
- `atomic_store` has no result.

This is sound under every interleaving, because it assumes nothing about other tasks, and it is cheap: no event structure, no new sorts, and no quantifiers. It is also the most a single function can know. Anything that relates the values seen by two tasks (a counter that only grows, a flag that publishes data) is a claim about the whole program, and it belongs to ADR 0027's model checker and to the `Order` theory ([docs/theories.md](../theories.md#happens-before-and-memory-orders)). Code that wants exact values in one task should use a plain `mutable`.

**Refined cells.** When `t` is a refinement, every value stored is a goal: `atomic_store`, `atomic_swap` and the `desired` of `atomic_cas` must be proved to meet the refinement, and every value read may be assumed to meet it. The refinement is then an invariant of the cell that holds across all tasks, proved one store at a time, just as a lock invariant is the refinement of a `mutex`'s data (ADR 0027). The bitwise read-modify-writes are not allowed on a refined cell, since their result is never known. `atomic_add` and `atomic_sub` are allowed only in `proof` mode, with a goal that for every value the refinement allows, the result fits and meets the refinement. `Pia.Sync.atomic_update o c f` is the replacement: a compare-and-swap loop in the library that calls `f` on the old value and stores its result, and `f`'s result must meet the refinement:

```ocaml
let slots = type { n : u32 | n <= 64 }

let take (c : borrowed atomic slots) : bool
= let old = atomic_update acq_rel c (let (n) => if n > 0 then n - 1 else n) in
  old > 0
```

**Across tasks**, the verifier needs a memory model, and section 4 gives one now.

### 4. The language memory model is a theory now, with a battery of litmus tests

Dean (2026-11-23): model it now, so that when tasks land there is a battery of tests ready for them.

**The theory.** `Pia.Memory` is a built-in theory of executions, extending the `Order` theory in [docs/theories.md](../theories.md#happens-before-and-memory-orders) to the whole of RC11 (Lahav, Vafeiadis, Kang, Hur and Dreyer, 2017), the repaired C11 model:

- **Events**: atomic loads, stores, read-modify-writes and fences, each with its order, and plain loads and stores, each with its location and value.
- **Relations**: program order `po`; reads-from `rf`; the modification order `mo`, a total order of the stores to each location; `rmw`, linking the read and write halves of a read-modify-write; synchronises-with `sw`, built from release sequences and fences as RC11 defines it; happens-before `hb = (po ∪ sw)+`; and the `seq_cst` order `psc`.
- **Axioms**: coherence (`hb ; eco?` irreflexive, where `eco` is `rf`, `mo` and from-reads closed), atomicity of read-modify-writes, `psc` acyclic, and no thin-air values (`po ∪ rf` acyclic). That last axiom is what lets RC11 give `relaxed` a meaning without out-of-thin-air results.
- **Races**: two accesses to one location race when at least one is plain, at least one writes, and neither happens before the other. That is ADR 0027's definition, and a race is a compile error.

With RC11 in place, `relaxed` is modelled from the start, not left unproved: ADR 0027's model checker reasons about every order under the same axioms, and the "value orders nothing" rule is no longer needed.

**Litmus tests.** A litmus test is a small concurrent program, with a few threads and a few locations, and the outcomes it may or may not have. Tasks are not built yet, so the tests are written with a `litmus` metaprogram in the prelude, beside `machine` ([docs/theories.md](../theories.md)). Each thread is a block of atomic and plain accesses to named cells, and the result says whether an outcome is `allowed` or `forbidden`, or that the test has a `race`:

```ocaml
litmus "MP+rel+acq"
  cells (data : u32) (flag : atomic u32)
  thread (data <- 1; atomic_store release flag 1)
  thread (let r1 = atomic_load acquire flag in let r2 = data in ())
  forbidden (r1 = 1 && r2 = 0)

litmus "MP+rlx"
  cells (data : u32) (flag : atomic u32)
  thread (data <- 1; atomic_store relaxed flag 1)
  thread (let r1 = atomic_load acquire flag in let r2 = data in ())
  race
```

The metaprogram expands a test into the test's events and a goal over `Pia.Memory`. A `forbidden` outcome is proved when no consistent execution has it. An `allowed` outcome is proved by a witness execution, which the solver finds and `piac` prints. A `race` is proved by an execution with two racing accesses. The tests are finite, so each one is a small, decidable query: relations become Boolean matrices over the test's events, and acyclicity becomes a ranking of them.

**The battery** is `tests/memory/`, one file per family, with each expected result taken from the published tables for RC11 and checked against `herd7` ([diy and herd](https://github.com/herd/herdtools7), the tool most memory-model papers use) where they give one:

- the classic shapes: MP, SB, LB, S, R, 2+2W, WRC, ISA2, IRIW, CoRR, CoRW, CoWR and CoWW, each under every combination of orders the operations allow, with fences in place of orders as well;
- read-modify-write atomicity, release sequences, and `seq_cst` fences;
- thin-air shapes (LB with dependencies), which RC11 forbids;
- races: plain accesses published by `relaxed`, by `release` and `acquire`, and by fences.

**When tasks land**, each test also becomes a program of `spawn`ed tasks, with the same outcomes as contracts on `join`. The model checker must agree with the battery, the deterministic replay mode can run each witness schedule, and on hardware a stress run of each test must never show a forbidden outcome. So tasks arrive with their memory model already proved against a few hundred tests, and with the tests ready to run as programs.

### 5. Each target lowers the orders by a table that is proved against its hardware model

`piac` emits LLVM `load atomic`, `store atomic`, `atomicrmw`, `cmpxchg` and `fence` with the matching LLVM ordering, and LLVM's backends pick the instructions. Those choices are the standard mappings from C11 to each architecture:

| Order | arm64 (Apple silicon: LSE and RCpc) | x86_64 |
| --- | --- | --- |
| `relaxed` load / store | `ldr` / `str` | `mov` / `mov` |
| `acquire` load | `ldapr` | `mov` |
| `release` store | `stlr` | `mov` |
| `seq_cst` load / store | `ldar` / `stlr` | `mov` / `xchg` |
| read-modify-write, `cas` | `ldadd`, `swp`, `cas` and so on, with `a`, `l` or `al` | `lock xadd`, `xchg`, `lock cmpxchg`; a loop of `lock cmpxchg` for `and`, `or`, `xor`, `min`, `max` when the old value is used |
| `fence acquire`, `release`, `acq_rel` | `dmb ishld` for acquire, `dmb ish` otherwise | nothing (compiler barrier only) |
| `fence seq_cst` | `dmb ish` | `lock or` of zero to the stack, which LLVM prefers to `mfence` as a full barrier |

Since Pia trusts LLVM for instruction selection, the table is checked in two halves:

1. **The table is what LLVM emits.** A codegen test per target compiles one function per (operation, order) pair and checks the instructions with FileCheck. A change in the pinned LLVM that picks other instructions fails that test.
2. **The table is proved against the hardware model.** Each target model in `Pia.Target` gains its hardware memory model, as [ADR 0049](0049-targets-are-theories.md) section 4 says: x86-TSO (Owens, Sarkar and Sewell) for x86_64, and the Armv8 axiomatic model (Pulte, Flur, Deacon and others, the one Arm publishes in its herd cat file) for arm64, written as theories of the same shape as `Order`. A compiler lemma per target states that the instructions the table chooses give every happens-before edge the language model promises. The lemmas are the battery of section 4 run a second time, against each hardware model: for every test, each outcome the hardware allows for the compiled instructions must be an outcome `Pia.Memory` allows for the source. The battery's file for each family runs against all three models. That includes the overflow lowerings of section 2: a `trap` on x86_64 reads the flags of the same `lock` instruction, so the check cannot see another task's update. The general theorem, that these mappings are correct for every program, is the published result of Lahav, Vafeiadis and others for RC11 and of Podkopaev, Lahav and Vafeiadis for Armv8, and Pia cites it rather than reproving it. The lemmas are what catch a wrong entry in Pia's table.

The lemmas live in `src/irgen/Target.pia` beside the models, so the build proves them, as it already proves the models' axioms (`tests/verify/target_theory.pia`).

### 6. On x86_64, code may rely on TSO, and each program proves it did not lose it

This builds ADR 0049 section 4.2 as Dean accepted it, limited, by his answer to this ADR, to the items that may rely on TSO.

- **Which code.** The model `x86_64_linux` gains two axioms, `store_releases` (every atomic store releases) and `load_acquires` (every atomic load acquires). Like every model fact, they are visible only inside `@target(x86_64_linux)` items. Target-generic code sees only the `Pia.Target` theory, so it never relies on them.
- **The lowering.** Inside `@target(x86_64_linux)` items, `relaxed` loads are emitted as LLVM `acquire` and `relaxed` stores as `release`. On x86_64 they are the same `mov` instructions, so the only cost is that LLVM may no longer reorder them, which is what the axioms need. Relaxed read-modify-writes are already `lock`-prefixed full barriers on x86_64, so they are emitted as `acq_rel`. Outside `@target(x86_64_linux)`, `relaxed` stays LLVM `monotonic` on both targets, since no proof there can depend on more.
- **The check.** Each atomic access emitted for a `@target(x86_64_linux)` item carries `!pia.tso` metadata naming its source location. After LLVM's optimisation pipeline, and before instruction selection, `piac` checks two things. First, every instruction with `!pia.tso` is still `acquire`, `release`, `acq_rel` or `seq_cst`. Second, every source location tagged before optimisation still has at least one tagged instruction afterwards, so an access the optimiser deleted or merged away is noticed. Inlining and unrolling may copy an access, which is fine, since every copy is checked. A failure is a compile error at the source location, saying that the optimiser weakened or removed an access the proof relied on. A goal that the axioms did not prove would have been proved without them, so the check can be stricter than necessary, never weaker.

With this, `publish_relaxed` from [docs/theories.md](../theories.md#happens-before-and-memory-orders), the message-passing idiom with a `relaxed` flag, proves inside `@target(x86_64_linux)` and fails everywhere else, which is the hardware's behaviour. The battery has both versions of `publish_relaxed`: as a source test under `Pia.Memory`, where the outcome is allowed, and under `x86_64_linux`'s axioms, where it is forbidden.

### 7. Atomics on foreign memory are `unsafe` views

io_uring's rings and other memory shared with the kernel or another process are not Pia cells. An `unsafe view` of such memory ([stdlib.md](../stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)) can be viewed as atomic cells with `unsafe Pia.Sync.atomic_at v offset : borrowed atomic u32` (and the other widths), with a goal that `offset` is in bounds and aligned to the cell's size. What the other side does is outside Pia's proof, so each such view is a trust item with the citation the module gives, such as io_uring(7) for the ring heads and tails ([ADR 0050](0050-senders-and-receivers.md) section 3).

### 8. Build order

1. **Cells and operations.** `atomic t`, `atomic_new`, the builtins, the order checks and the overflow modes (section 2), the verifier's view (section 3), refined cells and `atomic_update`, and lowering with LLVM's orderings. Tests: proved uses in `tests/verify/atomics.pia`, order and overflow errors in `tests/irgen`, and the instruction tables for both targets in `tests/codegen`.
2. **`Pia.Memory` and the litmus battery** (section 4): the theory with a model proving it consistent, the `litmus` metaprogram, and `tests/memory/`.
3. **The hardware models and lowering lemmas** (section 5): x86-TSO and Armv8 in `src/irgen/Target.pia`, and the battery run against each.
4. **The x86_64 TSO lowering and check** (section 6), which is ADR 0049 step 3d.
5. **Foreign atomic views** (section 7), when `Pia.Io.Uring` needs them, and `padded` with the per-target layout.
6. **Tasks** (ADR 0027, issue #75 onwards) then connect: spawned code produces `Pia.Memory` events, the model checker and race prover use the theory, and the battery runs as programs.

## Notes from step 1 (2026-11-23)

Building step 1 changed four details, none of which changes the design:

- **Refined cells are range types.** Sema does not resolve a scalar refinement such as `{ n : u32 | n <= 64 }` yet, so a refined cell is written with a range type, `atomic int{0..64}`, which is the same invariant. Its storage is the range's, a byte here, not a `u32`.
- **`atomic_update` retries a bounded number of times.** A compare-and-swap loop that can lose every race cannot be proved to end, and a `while` without a measure is not proved. The version in `tests/verify/atomics.pia` takes a number of tries and returns the old value it last saw. `Pia.Sync` will need the same, or a measure that tasks can supply.
- **`fence seq_cst` on x86_64 is `lock or`,** which is what LLVM emits; the table above is corrected, since the codegen test checks what LLVM emits.
- **`trap` reads the old value on both targets for now.** `rmw_flags` is in the target models, but no lowering reads the flags yet, so on x86_64 the overflow is recomputed from the old value, as on arm64.

## Answers (Dean, 2026-11-23)

1. **`relaxed` as acquire and release on x86_64:** yes, only inside `@target(x86_64_linux)` items (section 6). Elsewhere it stays LLVM `monotonic`.
2. **Overflow of `atomic_add` and `atomic_sub`:** "Do not assume, but use the target theory based on what we know the platform does... the simplest thing is to always require the overflow handling/expectations." Each operation states its mode, and the target model records what the hardware gives (`rmw_flags`), which the lowering uses (section 2).
3. **Happens-before from atomics:** "No, let's model it now so that when we implement tasks (ASAP) we have a battery of tests we can use." `Pia.Memory` and the litmus battery are step 2 (section 4).

## Consequences

- ADR 0049 step 3d can be built: the TSO check has atomics to check, and the lowering lemmas have a table to prove.
- ADR 0047's `shared_ref` and ADR 0050's io_uring rings have the cells and orders they name.
- A wrong memory order, a hidden lock, a run-time order and an atomic add without stated overflow handling cannot be written.
- The verifier's view of an atomic within one function is weak on purpose: a function proves nothing about values other tasks write. Cross-task facts go through `Pia.Memory`, which exists before tasks do, with a battery of litmus tests that tasks, the model checker and both targets must pass.
- `relaxed` is modelled by RC11 from the start, which replaces ADR 0027's plan to leave it unproved.
- Refined cells give cross-task invariants with one goal per store, without the model checker.
- Pia trusts LLVM's instruction selection for atomics, but a change in what it emits fails a test, and the table it emits is proved against each hardware model.
- Writing RC11, x86-TSO and the Armv8 model as theories is new work. The battery runs three times, once per model, and its cost is tracked by the proof bench ([ADR 0032](0032-parallel-sliced-cached-proving.md)).
