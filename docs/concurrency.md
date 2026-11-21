# Coroutines, tasks and race freedom

Status: proposal, 2026-11-21 ([ADR 0027](adr/0027-coroutines-and-race-freedom.md)). Nothing here is implemented yet. Code blocks show designed syntax.

[ADR 0014](adr/0014-concurrency-model.md) made Pia concurrent by default, with `spread` loops, collectives, task graphs and futures. It settled one question about safety: tiles are `moved` to workers, so they cannot race. This page designs the rest:

1. **Coroutines and lightweight tasks**, so a program can have many thousands of concurrent activities, such as I/O, pipelines and the task graph for flow accumulation, without one OS thread each.
2. **Locking, synchronisation and communication primitives**: mutexes, atomics, channels, barriers and friends.
3. **A prover that answers "could access to this resource race?"** for every piece of shared state, and refuses to compile the program when it cannot prove "no".
4. **How the answers reach proof certificates** ([ADR 0024](adr/0024-published-proof-certificates.md)), so a library's concurrency guarantees cross module and binary boundaries.

The rule from [ADR 0004](adr/0004-strongest-guarantee-by-default.md) applies throughout. An unproved race is an unproved obligation, so it is a compile error unless `--allow-unproved` names it.

## Summary of the choices

Each choice has a recommendation. The alternatives are below in each section.

| # | Question | Recommendation |
| --- | --- | --- |
| 1 | Stackless coroutines or stackful green threads? | **Stackless**: compiler-built state machines with frames of known size. "Green threads" are tasks on a scheduler written in Pia |
| 2 | Structured or detached tasks? | **Structured**: a task handle is `@linear` and must be joined inside the `scope` that spawned it |
| 3 | How is suspension visible? | **`@suspends` effect**, inferred inside a module and written in exported interfaces. Two keywords: `wait` and `yield` |
| 4 | How is race freedom proved? | **Permissions first**: ownership and borrows in the type checker, disjointness by Presburger (FPL) and Z3, and the **model checker** only for what types cannot express (the primitives themselves, protocols, deadlock) |
| 5 | How do locks work? | **A lock owns its data** (`mutex<T>`), with a **lock invariant** and a **static level**. Levels must increase, which rules out lock-order deadlocks at compile time |
| 6 | Which memory orders for atomics? | **`seq_cst`, `acquire`, `release` and `acq_rel`** are checked from day one. `relaxed` is an unproved obligation until the model checker supports RC11 |
| 7 | What does an unproved race do? | **Compile error**, with the two accesses and a witness. `--allow-unproved=race:...` accepts it, records it in the certificate as trusted, and recommends a TSan build |

## 1. Coroutines: stackless

A **coroutine** is a function that can suspend and later resume. A **task** is a coroutine that a scheduler runs. Pia's "green threads" are tasks: many of them run on a few OS worker threads.

There are two ways to build them:

| | Stackless (C++20, Rust `async`, Kotlin, Swift) | Stackful (Go, Erlang, Java virtual threads, Lua) |
| --- | --- | --- |
| What suspends | one function frame, which the compiler turns into a state machine | a whole call stack, switched by the runtime |
| Memory per task | the frame: a size known at compile time | a stack: guessed, grown, or segmented |
| Calling a suspending function | only from another suspending one ("function colouring") | from anywhere |
| Foreign code on the stack | never across a suspension | possible, and unsafe if foreign code keeps pointers into the stack |
| For the verifier | every suspension point is a visible state; the frame is a value with a type | suspension hides inside any call; stack size is a proof goal Pia cannot discharge in general |

**Recommendation: stackless.** It suits a language whose compiler must prove things:

- **No stack-size guess.** A stackful task needs a stack big enough for its deepest call chain. Proving that bound is hard once there are function values, recursion or foreign calls, and an overflowed green-thread stack is exactly the kind of run-time failure Pia exists to remove. A stackless frame's size is computed by the compiler. A suspending function cannot recurse through a suspension except by `spawn`ing, which allocates the child frame explicitly.
- **Suspension points are states.** The model checker (section 4) explores tasks as state machines whose transitions are the code between two suspension points. Stackless lowering produces exactly that machine. Module-state contracts ([ADR 0006](adr/0006-contracts-and-module-state.md)) and the protocol checker ([ADR 0014](adr/0014-concurrency-model.md)) read the same states.
- **Borrows across suspension are checkable.** A frame that holds a borrow across `wait` is a value holding a borrow, and the ordinary borrow rules apply to it.
- **Foreign code stays outside.** No foreign frame is ever suspended, so foreign code never sees a stack move or a thread change under it.
- **Lowering exists.** LLVM's coroutine intrinsics (`llvm.coro.*`, switched-resume lowering) build the frame and elide its allocation when the coroutine does not outlive its caller. MLIR's `async` dialect lowers to them already.

The cost is colouring: a function that suspends can only be called by one that also suspends, or handed to a scheduler. Pia makes the colour cheap instead of hiding it (section 2). It also stays honest: the colour is a fact the verifier and importers need anyway.

### Syntax

Two keywords, both single imperative words: `wait` suspends until a task or operation completes, and `yield` suspends a generator with a value. Everything else is library code.

```ocaml
import Pia.Task { scope, spawn, join }
import Pia.Io   { conn, read }

(* A suspending function. @suspends is inferred inside the module, and must
   be written when the function is exported. *)
let read_exact (c : borrowed inout conn) (dst : borrowed out mutable [u8; n]) : result<unit, io_error> @suspends
= let mutable got = 0 in
  while got < n
    invariant 0 <= got && got <= n
    decreases n - got
  do
    match wait (read c dst.[got .. n]) with
    | Ok 0   -> return (Err Eof)
    | Ok k   -> got <- got + k
    | Err e  -> return (Err e)
  done;
  Ok ()

(* A generator: yields each row, suspends between them. *)
let rows (img : borrowed in [u8; w * h]) : gen<[u8; w]> =
  for y in 0..h do yield img.[y * w .. (y + 1) * w] done
```

### Tasks are structured

`scope` opens a region. `spawn s f` starts `f` as a task in scope `s` and returns a `task<T>`, which is `@linear` ([stdlib.md](stdlib.md#7-linear-resources-and-memory)). It must be consumed by `join` (or `wait`) before the scope ends, so no task outlives the scope that started it. This is structured concurrency, as in Trio's nurseries, Kotlin's `coroutineScope`, Swift's task groups and Rust's `thread::scope`.

```ocaml
let total (xs : borrowed in [i64; n]) : i64 @suspends
  requires n >= 2
= scope (let (s) =>
    let lo = spawn s (let () => sum xs.[0 .. n / 2]) in
    let hi = spawn s (let () => sum xs.[n / 2 .. n]) in
    join lo + join hi)
```

Structure buys two things for proofs:

- **Tasks may borrow from their parent.** Both tasks above borrow `xs`, because the scope cannot end while they run. Without structure, everything a task touches would have to be `moved` or reference-counted.
- **Arenas and regions nest.** An arena region ([stdlib.md](stdlib.md#7-linear-resources-and-memory)) that encloses a scope encloses all its tasks, so a coroutine may hold arena borrows across suspension points.

Detached ("fire and forget") tasks are not in the first version. A long-lived service is a scope at the top of `main`. If they are added later, a detached task must own everything it touches (`moved`, no borrows) and is a `sendable` value (section 3).

**Cancellation** is cooperative and explicit in the first version: a scope can be given a `cancel` token, and operations that take one return `Err Cancelled`. Implicit cancellation at every `wait` interacts with `@linear` resources (a cancelled task must still consume its file descriptors), so it waits for experience with the explicit form.

### Errors and cleanup in tasks

Error propagation and scope cleanup are designed separately (ADR 0028, in review). The design here relies on four of its rules:

- `?` never crosses a task boundary. Inside a spawned closure it ends that task, and the error comes back from `join`.
- Inside a `lock` body, `?` leaves the closure, the lock is released, and the error is the closure's result.
- A `scope` that exits early first joins (or cancels, then joins) every child still running, and only then runs the parent's defers, because children may borrow from the parent.
- Drops and defers never suspend and never acquire a lock, so they cannot break the lock-level order.

### Calling suspending code from ordinary code

`Pia.Task.run (f : () -> T @suspends) : T` starts a scheduler, runs `f` to completion, and returns. `main` may itself be `@suspends`, in which case the runtime calls `run` for it. A non-suspending function cannot `wait`.

Generic code that takes a function, such as `map`, should work for both colours. That needs effect polymorphism over `@suspends` in generics ([ADR 0009](adr/0009-generics-concepts-adapters.md)), which is designed with M9. Until then, the library has `map` and `map_wait`.

### Blocking calls

A foreign call that blocks, such as `read` on a pipe or a long `fsync`, would stall a worker thread and every task queued on it. Foreign declarations ([stdlib.md](stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)) say so with `@blocking`. Calling a `@blocking` function from `@suspends` code is an error unless it goes through `Pia.Task.offload`, which runs it on a separate blocking pool and suspends until it returns. This is Tokio's `spawn_blocking` and Go's handoff of a blocked `M`, made a compile-time rule.

### The scheduler is Pia

The scheduler lives in `Pia.Task`, written in Pia over the core ([ADR 0023](adr/0023-minimal-core-self-hosted-stdlib.md)):

- **Workers**: one OS thread per performance core (`sysctlbyname`), from `Pia.Sys.Thread`.
- **Queues**: a work-stealing deque per worker (Chase-Lev), written in Pia over `atomic<T>` and proved by the model checker (section 4).
- **I/O**: `Pia.Io` wraps `kqueue`/`kevent` on macOS (epoll or io_uring on a later Linux port). A task that waits on a descriptor parks until `kevent` reports it ready.
- **Timers**: a timer wheel driven by the same `kevent` call.
- **Frames**: a task frame's size is known, and it comes from the allocator the scope was given. Allocators are explicit `@linear` values, so a scope takes one, as any allocating function does ([stdlib.md](stdlib.md#7-linear-resources-and-memory)).
- **Deterministic mode**: `Pia.Task.run_deterministic seed f` runs every task on one thread in an order chosen by `seed`. It is for tests, for replaying a counterexample trace from the model checker, and for the doc examples.

`spread` and the collectives move onto the same scheduler. A `spread` loop is a `scope` that spawns one task per chunk, and a collective is a synchronisation operation among those tasks. There is one runtime, not a worker pool beside a task scheduler. Device placement ([ADR 0015](adr/0015-device-placement.md)) adds device queues: a GPU kernel is a task whose completion is a Metal event, and the buffers it uses are `moved` to it. Apple Silicon's unified memory means no copy, but ownership still moves, so the CPU cannot touch a buffer the GPU is writing.

## 2. Synchronisation and communication primitives

Every primitive lives in the library, in `Pia.Sync` and `Pia.Chan`. Each has a contract the race prover relies on, and its implementation is proved against that contract (section 4).

| Primitive | Type | What it guarantees |
| --- | --- | --- |
| Mutex | `mutex<T>` | owns a `T`; the only access is inside `lock`; the lock invariant holds whenever it is unlocked |
| Reader-writer lock | `rwlock<T>` | many `read` borrows or one `write` borrow |
| Atomic cell | `atomic<T>` | `T` is an integer, `bool` or `addr`; every operation takes a memory order ([stdlib.md](stdlib.md#10-simd-floats-and-atomics)) |
| Channel | `chan<T, cap>` | `send` takes `moved T`, `recv` returns it; bounded by `cap` |
| One-shot | `once<T>`, `promise<T>` | written exactly once, then shareable read-only |
| Barrier | `barrier n` | releases when exactly `n` tasks arrive; the protocol checker proves all `n` arrive |
| Semaphore | `semaphore n` | at most `n` holders |
| Notify | `event` | wakes waiters; the replacement for condition variables |

There are no bare condition variables. A condition variable's meaning (which predicate a waiter is waiting for) lives in comments, and its spurious wake-ups make every waiter a loop. `event` plus a lock invariant, or a channel, says the same thing in a form the prover reads.

### A lock owns its data

A `mutex<T>` holds a `T`. The only way to reach the `T` is `lock`, which passes a scoped `mutable` borrow to a closure. The borrow cannot escape the closure, so the data cannot be touched without the lock. Rust's `Mutex<T>` works the same way.

```ocaml
let pool = type { free : usize; used : usize } where free + used = cap

let slots : mutex<pool> @level(2) = mutex { free = cap; used = 0 }

let take () : bool @suspends =
  lock slots (let (p : borrowed inout mutable pool) =>
    if p.free > 0 then (p.free <- p.free - 1; p.used <- p.used + 1; true)
    else false)
```

- **Lock invariant.** `pool`'s refinement `free + used = cap` holds whenever the mutex is unlocked. Inside the closure it is assumed on entry and proved on exit, just as a loop invariant is. This is the "monitor invariant" of Chalice and VeriFast, and it is free in Pia: the refinement type already says it.
- **The body may not suspend.** A `lock` closure must not `wait`. Critical sections stay short, a worker never parks while holding a lock, and lock-order checking only has to look at straight-line code. Allocation inside a lock body is allowed. Waiting for a lock does suspend the task, not the worker.
- **Two flavours.** `mutex` is task-aware: a task that finds it held suspends. `spin_mutex` busy-waits and is for very short sections inside the runtime itself, such as the scheduler's queues.

### Lock levels rule out lock-order deadlocks

Every lock has a static level, written `@level(n)`. A task may only acquire a lock whose level is greater than every lock it already holds. The type checker tracks the set of held levels through `lock` bodies and across calls. A function's interface records the highest level it may acquire, as `@acquires(n)`, inferred inside a module and written in exported interfaces. A call to a function that acquires level 2 while holding level 3 is a compile error.

Acquiring in a fixed order is the classic lock-ordering argument, and it makes lock-order cycles impossible. Linux's lockdep checks it at run time; Pia checks it at compile time. Levels are numbers, not a declared lattice, which keeps the check simple. Locks of equal level may not be nested. Two locks of the same level that must be held together, such as two accounts in a transfer, are taken with `lock2`, which orders them by address and is proved once in the library.

Deadlocks through channels, joins and barriers cannot be ruled out by levels. They go to the protocol checker and the model checker (section 4).

### Channels move ownership

`send` takes its value `moved`, so the sender cannot touch it afterwards, and the receiver owns it. Nothing sent through a channel can be raced on, whatever it contains. A channel's two ends are separate values: `sender<T>` is `shareable` (many producers), and `receiver<T>` is `@linear` (one consumer). `select` waits on several channels and returns the first ready one.

```ocaml
let pipeline (src : moved receiver<tile>) (dst : moved sender<tile>) : unit @suspends =
  for t in src do                        (* each t is owned here *)
    smooth t;                            (* so it can be mutated without a lock *)
    wait (send dst t)                    (* and handed on: t is dead after this *)
  done
```

## 3. Proving that resources cannot race

### What a race is

Two accesses to the same resource **race** if they come from different tasks, at least one of them writes, at least one of them is not atomic, and neither happens before the other. That is the C++ and LLVM definition of a data race, applied to memory, and Pia applies it to other resources too (below).

The prover must show that for every pair of accesses that could run concurrently, one of these holds:

1. **Ownership.** Only one task can reach the resource: it was `moved` to that task, or sent through a channel.
2. **Shared reading.** Both accesses are reads through `fixed` borrows. A `fixed` value has no interior mutability, so any number of tasks may read it.
3. **Disjointness.** Both tasks reach the same buffer, but through slices or index sets that are proved not to overlap.
4. **Protection.** The resource is inside a `mutex`, `rwlock` or other primitive, and the accesses are inside its `lock`.
5. **Atomicity.** Both accesses are atomic operations on an `atomic<T>`. They do not race, though whether the program is right is a separate goal (section 4).
6. **Ordering.** A happens-before edge separates them: a `join`, a channel send and its receive, a barrier, or an acquire that reads a release.

### Who proves what

Each rule is discharged by the cheapest stage that can, in the verifier's fixed order ([ADR 0020](adr/0020-presburger-for-affine-goals.md)). The stage is recorded with the goal, as for every other goal.

| Stage | Proves | How |
| --- | --- | --- |
| Types | rules 1, 2, 4, 6 for joins and channels | ownership and borrow checking, extended with the `sendable` and `shareable` concepts and with task boundaries |
| Presburger (FPL) | rule 3 when the indices are affine | the access relations of two tasks, intersected; an empty intersection is a proof |
| Z3 | rule 3 when they are not | data-dependent indices, as for any non-affine goal; a model is a counterexample |
| Model checker | rules 5 and 6 for atomics, the primitives' own implementations, protocols, and deadlock | explores the interleavings of tasks as state machines |

Most programs never reach the model checker. They use ownership, `spread` over disjoint tiles, locks that own their data and channels that move values. The type checker settles those quickly and predictably. The model checker is for the library's primitives, which are proved once, and for programs that build their own synchronisation from atomics.

### Types: `sendable` and `shareable`

Two concepts ([ADR 0009](adr/0009-generics-concepts-adapters.md)) say which values may cross a task boundary. They are Rust's `Send` and `Sync`, named as Pia names things.

- **`sendable T`**: a `T` may be `moved` to another task. True unless `T` holds a borrow that the receiving task could outlive. Inside a `scope`, borrows of the parent's data are fine.
- **`shareable T`**: a `T` may be borrowed by several tasks at once. True for any `fixed` data, since `fixed` has no interior mutability. Of the types with interior mutability, only the primitives are shareable: `atomic<T>`, `mutex<T>`, `rwlock<T>`, `sender<T>`, `once<T>` and so on.

Both are derived by a metaprogram over a type's fields, as `@derive(eq)` is, so user types get them without writing anything. A `@linear` allocator is `sendable` but not `shareable`. `spawn` requires its closure's captures to be `sendable` if moved and `shareable` if borrowed. That one rule is what turns the existing borrow checker into a race checker.

Module-level mutable state is shared by every task in the program, so it must be `shareable`. A module-level `let mutable` of a plain type is a compile error when the module is used from more than one task. The fix is to wrap it in a `mutex` or make it `atomic`, or to keep it inside a task.

### Disjointness: FPL first

`spread`, and tasks that are spawned in a loop, are the main source of shared buffers. For each pair of tasks the verifier builds the relation "task `i` writes element `e`" and "task `j` reads or writes element `e`", adds `i != j`, and asks FPL whether the relation is empty. This is the same dependence relation `spread` legality and the vectoriser already use ([ADR 0020](adr/0020-presburger-for-affine-goals.md)). The same check covers slices handed to separately spawned tasks, as in `total` above, where `0 .. n/2` and `n/2 .. n` are disjoint.

When an index depends on data, such as a histogram whose bin comes from a pixel, the goal goes to Z3. If Z3 finds a model, it is the counterexample:

```console
$ piac --verify hist.pia
hist.pia:12:7: error: possible data race on `counts.[b]`
  spread iterations i = 3 and j = 4 both write counts.[7]
  witness (z3): px.[3] = 200, px.[4] = 201, b = px / 32 = 7 in both
  help: give each task its own `counts` and merge with `all_reduce add`,
        or make the bins `atomic<u32>` and use `atomic_add relaxed`
```

The second suggestion leads to the next rule.

### Atomics and memory orders

Atomic accesses never race in the data-race sense, but code built from atomics can still be wrong. The usual mistake is to publish data with a flag that is written `relaxed`, so the reader sees the flag but not the data. Pia's rule is that a happens-before edge from atomics only counts if the orders create one, as C++ defines it: a `release` store read by an `acquire` load.

The model checker supports sequential consistency and release/acquire from the start. `relaxed` is harder: reasoning about it needs a weak memory model such as RC11, with the out-of-thin-air problem that comes with it. So the plan is:

- `relaxed` operations whose results never create an ordering, such as a statistics counter or the histogram bins above, are accepted by the type checker. The rule is that the value read is not used to decide whether to touch other shared data.
- Any other use of `relaxed` is an unproved obligation, so it is an error by default, until the model checker gains an RC11 mode. GenMC and CDSChecker show it can be done.

### Resources other than memory

"Resource" means more than memory. Foreign declarations may give a **footprint**, a named abstract resource with an optional range, and the race prover treats it like a buffer.

- **File descriptors.** An `fd` is `@linear`, so one task owns it, and two tasks cannot `write` to it at once. A `shared<fd>` is shareable, but it only offers positioned operations: `pread` and `pwrite`, whose footprint is `fd[offset .. offset + len]`. Two tasks writing to one file are race-free when FPL proves their ranges disjoint. That is how the flagship demo can write tiles of one output image in parallel.
- **Process-wide resources.** Standard output, the working directory, the environment and signal dispositions are module state of `Pia.Sys`, behind primitives. `print` from two tasks locks `stdout`, so lines never interleave mid-line.
- **Out of scope.** Pia cannot see other processes, so races on the file system between processes (one program renames a file another opens) are not proved. Advisory locks (`flock`) can be wrapped, but what another process does is not a Pia proof.

### Foreign code

A foreign function is opaque. Its declaration says whether it may be called concurrently: `@threadsafe` means calls from several tasks may overlap, `@serial` means the library wraps it in a lock, and a declaration with neither may only be called from one task, as if it were `@linear` module state. A wrong `@threadsafe` is a trust item, like any other foreign contract, and it is listed in the trust report. This is also where TSan earns its keep (the sanitizer design, ADR 0025, in review): it instruments both sides, so a race between Pia and C code shows up in a `--config=tsan` run.

## 4. The model checker

The model checker pass, already planned in [ADR 0014](adr/0014-concurrency-model.md), covers what the type system cannot. It runs on the `pia_par` dialect after coroutine lowering, so each task is a state machine and each transition is the code between two synchronisation points.

**What it checks:**

1. **The primitives.** `mutex`, `rwlock`, `chan`, `barrier`, `once` and the work-stealing deque are written in Pia over `atomic<T>` and the scheduler. Each is proved against its contract: mutual exclusion, the lock invariant, no lost wake-ups, FIFO delivery, the barrier releasing exactly when `n` tasks arrive. These proofs run once, when the library builds, and every program then relies on the contracts.
2. **Protocols and deadlock.** Every `wait` eventually completes: no cycle of tasks waiting on each other's channels, joins or barriers. The protocol metaprogram from ADR 0014 settles the regular cases, such as every `spread` worker issuing the same collectives. The model checker takes the rest.
3. **User code built from atomics**, under the memory orders it uses.

**How it works:**

- **Exhaustive, never bounded.** It explores every interleaving, using dynamic partial-order reduction (DPOR, as in Nidhugg, GenMC and Rust's Loom) and symmetry between identical tasks. A search that hits its state limit is *unproved*, not proved. A bounded check is a test, and Pia does not count tests as proofs.
- **Small models, parametric results.** Checking a mutex for 2 or 3 tasks proves it for any number of tasks only when a cutoff argument justifies it. For the library primitives that argument is written once as a lemma. For user code, a parametric claim the checker cannot justify is unproved.
- **Abstraction.** The data inside tasks is abstracted to what the protocol reads, the rest being havoc, with contracts carried over as assumptions. Without that, the state space is the product of every task's variables.
- **Counterexamples are schedules.** A failure is a sequence of task steps. `piac` prints it with source locations, the language server shows it in the editor, and `Pia.Task.run_deterministic` replays it.

Writing a model checker is real work, so it comes after the type-level checks. The first programs, `spread` over tiles with collectives, need only types and FPL. The library primitives can start as trusted wrappers around `os_unfair_lock` and pthreads (both already in [stdlib.md](stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)), and are replaced by proved Pia implementations when the checker lands. The trust report shows the difference.

## 5. Unproved races

An unproved race goal is like any other unproved goal: `piac` refuses to compile ([codegen.md](codegen.md)). The error names both accesses, the tasks they come from, the stage that tried, and a witness: an FPL sample point, a Z3 model, or a model-checker schedule.

To compile anyway, `--allow-unproved` accepts race goals by kind:

| Flag | Accepts |
| --- | --- |
| `--allow-unproved=race:hist.pia:12` | the race goals on line 12 |
| `--allow-unproved=deadlock:pipeline` | the deadlock goals in function `pipeline` |
| `--allow-unproved=relaxed:Stats` | `relaxed` uses in module `Stats` that need RC11 |

An accepted race is a trust item in the module's certificate (below), and `piac` says that a `--config=tsan` build would check it at run time.

## 6. Interfaces and proof certificates

Modules are verified separately ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)), so every fact a caller's race proof needs must be in the interface. These join the interface, and so the interface hash and the witness symbols ([ADR 0024](adr/0024-published-proof-certificates.md)):

| Fact | Example | Why callers need it |
| --- | --- | --- |
| Suspension | `@suspends` | the caller must be `@suspends` or use `run` |
| Blocking | `@blocking` | the caller must `offload` it |
| Lock levels | `@acquires(3)` | the caller's held levels must be below 3 |
| Concurrency of calls | `@threadsafe`, `@serial` | whether two tasks may call it at once |
| Concepts of exported types | `sendable`, `shareable` | whether a value may cross a task boundary |
| Module-state footprint | which shared primitives a function touches | rules 4 and 6 across modules |

A change to any of these changes the interface hash, so a library whose function starts acquiring a higher-level lock, or stops being `@threadsafe`, no longer loads against a binary built for the old one. The ABI evolution rules apply as before. Interfaces refine safely when a function acquires lower levels (or none), suspends where it used to block, or becomes `@threadsafe` where it was `@serial`.

The certificate records each race and deadlock goal with its stage: `types`, `presburger`, `smt` or `mc`. Model-checker results also record the state count and the reduction used, and are only recorded when the search was exhaustive. The trust section gains:

- race, deadlock and `relaxed` goals accepted with `--allow-unproved`;
- `@threadsafe` claims on foreign declarations;
- primitives that are still trusted wrappers rather than proved Pia.

The loader checks nothing new at run time. The concurrency facts are part of the interfaces it already matches. `pia-cert audit` and `piac --trust-report` show them alongside the other trust items.

## Prior art

| System | What Pia takes |
| --- | --- |
| Rust (`Send`, `Sync`, `Mutex<T>`, `thread::scope`, `async`) | ownership-based race freedom; locks that own data; scoped tasks; stackless coroutines |
| C++20 coroutines, LLVM `llvm.coro.*` | the stackless lowering and frame elision |
| Trio, Kotlin, Swift structured concurrency | tasks joined inside the scope that started them |
| Go, Erlang, Java virtual threads | the case for stackful green threads, and why Pia does not take it |
| Pony (reference capabilities) | race freedom from capabilities checked by the type system |
| Chalice, VeriFast, Iris and RustBelt | lock invariants; the theory for proving primitives built from atomics |
| Linux lockdep, Fuchsia lock levels | static lock ordering |
| GenMC, CDSChecker, Nidhugg, Loom | exhaustive checking with DPOR under C11-style memory models |
| SPIN, TLA+ and TLC | explicit-state model checking of protocols |
| Eraser, RacerD, TSan | lockset and happens-before race detection, which is dynamic or unsound, so Pia uses TSan only for the trusted boundary |

Two alternatives were considered and set aside. **Lockset analysis** (RacerD, Eraser) finds many races cheaply but is not sound, so it cannot discharge a proof goal. **Full separation-logic annotations** (Iris, VerCors, Viper) are sound and very expressive, but ask every user to write permissions by hand. Pia's types infer the common cases, and the heavier reasoning is kept for the library primitives, which are written once.

## Implementation plan

The order follows what the flagship demo needs, then general programs:

1. **Race checks in the type checker**: `sendable` and `shareable`, task boundaries, module-level state. `spread` over `moved` tiles needs only this.
2. **Disjointness goals** for concurrent slices and footprints, through FPL then Z3, with counterexamples.
3. **Coroutine lowering**: `wait`, `yield`, `@suspends` inference, frames of known size, lowering to `llvm.coro.*`.
4. **`Pia.Task`**: `scope`, `spawn`, `join`, the work-stealing scheduler, the deterministic mode, and moving `spread` onto it.
5. **`Pia.Io`**: kqueue, timers, `offload` and `@blocking`.
6. **`Pia.Sync` and `Pia.Chan`**: primitives as trusted wrappers first, with lock invariants, lock levels and `@acquires`.
7. **The model checker**: DPOR, SC and release/acquire, deadlock, schedule counterexamples. Then proved Pia implementations of the primitives replace the trusted wrappers.
8. **Certificates**: the concurrency facts in interfaces and hashes, race goal kinds, trust items, `--allow-unproved=race:...`.
9. **RC11 mode** for `relaxed` atomics.

Each step is a GitHub issue under the tracking issue [#74](https://github.com/deanberris/pia-lang/issues/74): #75 to #83, in this order.
