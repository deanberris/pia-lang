# Coroutines, tasks and race freedom

Status: accepted design, 2026-11-21 ([ADR 0027](adr/0027-coroutines-and-race-freedom.md)). Nothing here is implemented yet. Code blocks show designed syntax.

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
| 7 | How are deadlocks in channel communication (CSP) found? | **A deadlock goal for every scope**: a forest-shaped channel topology is proved by a lemma, protocols inferred per channel end are checked for compatibility and matched against proved patterns (pipeline, worker pool, request and reply), and the model checker searches the rest for any set of tasks blocked forever |
| 8 | What does an unproved race or deadlock do? | **Compile error**, with the accesses or blocked tasks and a witness. `--allow-unproved=race:...` or `deadlock:...` accepts it, records it in the certificate as trusted, and recommends a TSan build |

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

The cost is colouring: a function that suspends can only be called by one that also suspends, or handed to a scheduler. Pia makes the colour cheap instead of hiding it (below). It also stays honest: the colour is a fact the verifier and importers need anyway.

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

Deadlocks through channels, joins and barriers cannot be ruled out by levels. They have their own checks (section 5).

### Channels move ownership

`send` takes its value `moved`, so the sender cannot touch it afterwards, and the receiver owns it. Nothing sent through a channel can be raced on, whatever it contains. A channel's two ends are separate values, and both are `@linear`. `receiver<T>` has one consumer. `sender<T>` can be `clone`d for more producers, every copy must be consumed, and the channel closes when the last one is. A borrowed `sender<T>` is `shareable`. `select` waits on several channels and returns the first ready one.

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
2. **Protocols and deadlock.** No set of tasks is ever blocked forever on each other's channels, joins or barriers (section 5). The topology check, the protocol metaprogram and the library's patterns settle the regular cases. The model checker takes the rest.
3. **User code built from atomics**, under the memory orders it uses.

**How it works:**

- **Exhaustive, never bounded.** It explores every interleaving, using dynamic partial-order reduction (DPOR, as in Nidhugg, GenMC and Rust's Loom) and symmetry between identical tasks. A search that hits its state limit is *unproved*, not proved. A bounded check is a test, and Pia does not count tests as proofs.
- **Small models, parametric results.** Checking a mutex for 2 or 3 tasks proves it for any number of tasks only when a cutoff argument justifies it. For the library primitives that argument is written once as a lemma. For user code, a parametric claim the checker cannot justify is unproved.
- **Abstraction.** The data inside tasks is abstracted to what the protocol reads, the rest being havoc, with contracts carried over as assumptions. Without that, the state space is the product of every task's variables.
- **Counterexamples are schedules.** A failure is a sequence of task steps. `piac` prints it with source locations, the language server shows it in the editor, and `Pia.Task.run_deterministic` replays it.

Writing a model checker is real work, so it comes after the type-level checks. The first programs, `spread` over tiles with collectives, need only types and FPL. The library primitives can start as trusted wrappers around `os_unfair_lock` and pthreads (both already in [stdlib.md](stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)), and are replaced by proved Pia implementations when the checker lands. The trust report shows the difference.

## 5. Deadlock freedom for channel communication

Programs in the style of CSP (Hoare's Communicating Sequential Processes, as in occam and Go) build concurrency out of tasks that share nothing and talk only through channels. They cannot race, because `send` moves ownership. They can still deadlock: a set of tasks each blocked on a `send` or `recv` that only another task in the same set could complete. Lock levels do not help here. So every `scope` that uses channels gets a **deadlock goal**: no reachable state leaves a set of tasks blocked forever. Like any other goal, it is a compile error when it is unproved.

### What counts as a deadlock

In any state, every blocked task is waiting for someone:

| Blocked on | Can be woken by |
| --- | --- |
| `recv` on an empty channel | any holder of a sender, or the last sender being consumed, which closes the channel |
| `send` on a full channel, or any `send` on a rendezvous channel (`cap = 0`, CSP's synchronous send) | the holder of the receiver, or the receiver being consumed, which makes `send` return `Err Closed` |
| `join` | the child task |
| `barrier`, `event`, `promise` | the tasks that have not arrived yet, or the holders of the notifier or the writer |
| `select` | anyone who can wake any of its arms |

A state is **deadlocked** when there is a non-empty set `D` of blocked tasks such that every task that could wake a member of `D` is itself in `D`. This covers partial deadlocks too, such as two workers stuck waiting on each other while a server keeps running, not only "every task has stopped". The condition is about a single state, so checking it needs no fairness assumptions.

Three rules from earlier sections keep the waits-for relation small and computable:

- **Who can wake a task is known.** A `receiver<T>` is `@linear`, and a `sender<T>` is `@linear` too: more producers come from `clone`, and every copy must be consumed on every path. The holders of each end are therefore values the compiler tracks. A channel closes exactly when its last sender is consumed, so "forgot to close the channel" is a type error rather than a hang.
- **Mutexes are not in the relation.** A `lock` body cannot suspend, so a task holding a mutex always makes progress, and waiting for a mutex always ends. Lock levels already rule out cycles among locks.
- **Channels are bounded.** `chan<T, cap>` always has a capacity. There are no unbounded channels, which would hide memory exhaustion and give the model checker infinite states.

### Three stages, cheapest first

**Stage 1: topology.** The compiler extracts each scope's **channel topology** from ownership. The nodes are the tasks spawned in the scope and the parent. There is an edge wherever a task holds one end of a channel and another task holds the other, and from each child to the parent that joins it. Structured scopes make this graph static for most programs. If the graph is a **forest**, so that no two tasks are linked by two different paths, and every task drains its inputs (it receives until they close, then consumes its senders), then the scope is deadlock-free. A lemma proved once in the library covers this. Pipelines, broadcast trees and fan-in through one shared channel are all forests, and they cover most stream programs, including the flagship demo's tile pipeline.

A graph that only avoids directed cycles (a DAG) is not enough with bounded channels. In the diamond below, every channel points downstream, yet the program can deadlock:

```ocaml
let diamond (items : moved receiver<job>) (out : moved sender<res>) : unit @suspends =
  let (l_in, l_inr)   = chan 1 in
  let (r_in, r_inr)   = chan 1 in
  let (l_out, l_outr) = chan 1 in
  let (r_out, r_outr) = chan 1 in
  scope (let (s) =>
    let split = spawn s (let () => alternate items l_in r_in) in   (* l, r, l, r, ... *)
    let left  = spawn s (let () => work l_inr l_out) in
    let right = spawn s (let () => work r_inr r_out) in
    let merge = spawn s (let () => drain l_outr out; drain r_outr out) in  (* all of left first *)
    join split; join left; join right; join merge)
```

```console
$ piac --verify diamond.pia
diamond.pia:6:3: error: possible deadlock in this scope
  tasks split, left, right and merge can all block forever:
    split  sends to r_in      (full, capacity 1)    diamond.pia:7
    right  sends to r_out     (full, capacity 1)    diamond.pia:9
    left   receives from l_in (empty)               diamond.pia:8
    merge  receives from l_out (empty)              diamond.pia:10
  witness (model checker): a schedule of 11 steps, replay with --replay=diamond.trace
  help: merge with `select` over both inputs, or use `Pia.Chan.fan_in`
```

**Stage 2: protocols.** For each channel end a function uses, the compiler infers a **usage protocol**: a finite automaton over its sends, receives and closes, which is the function's control flow projected onto that end. `work` above follows `(recv; send)* ; close` on its two ends. Protocols are inferred inside a module and written as `@protocol` on exported parameters, so the check is modular. The protocol metaprogram from [ADR 0014](adr/0014-concurrency-model.md) checks that the protocols at the two ends of every channel are compatible, as it already does for collectives. This is not session typing, which ADR 0014 rejected: the type system is unchanged, and protocols are contracts the metaprogram checks.

The library also ships **patterns** with deadlock-freedom lemmas proved once, for any number of tasks:

- **pipeline** and **broadcast tree** (stage 1 already covers these);
- **worker pool**: a dispatcher, `n` identical workers and a collector, joined through one fan-in channel;
- **request and reply**: the request carries a one-shot `promise` for its reply, so the reply cannot block the server;
- **scatter and gather**, the channel form of the collectives.

When a scope's topology and protocols match a pattern, the goal is discharged by the pattern's lemma, with no state exploration. This is how a worker pool of `n` tasks is proved for every `n`.

**Stage 3: the model checker.** Anything else goes to the model checker (section 4). The protocol automata of every task in the scope, together with the channel capacities, form a finite system once data is abstracted away. The checker explores it with DPOR and tests the deadlock condition in every state. It finds request cycles (A waits for B's reply while B waits for A's), the diamond above, and mismatched rendezvous orders. Parametric claims need symmetry and a cutoff lemma, otherwise they are unproved. Channels sent over channels (mobile topologies, as in the pi-calculus) are explored while their number stays bounded. Topologies that grow with the data, such as a task spawned for each element of an input stream, are unproved unless they match a pattern.

**Timeouts.** A `select` with an `after d` arm is never blocked forever, so it is not a deadlock. It can still spin forever. Deadlock freedom is a safety property, and proving progress (liveness) is a later extension.

## 6. Unproved races

An unproved race goal is like any other unproved goal: `piac` refuses to compile ([codegen.md](codegen.md)). The error names both accesses, the tasks they come from, the stage that tried, and a witness: an FPL sample point, a Z3 model, or a model-checker schedule.

To compile anyway, `--allow-unproved` accepts race goals by kind:

| Flag | Accepts |
| --- | --- |
| `--allow-unproved=race:hist.pia:12` | the race goals on line 12 |
| `--allow-unproved=deadlock:pipeline` | the deadlock goals of scopes in function `pipeline` |
| `--allow-unproved=relaxed:Stats` | `relaxed` uses in module `Stats` that need RC11 |

An accepted race is a trust item in the module's certificate (below), and `piac` says that a `--config=tsan` build would check it at run time.

## 7. Interfaces and proof certificates

Modules are verified separately ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)), so every fact a caller's race proof needs must be in the interface. These join the interface, and so the interface hash and the witness symbols ([ADR 0024](adr/0024-published-proof-certificates.md)):

| Fact | Example | Why callers need it |
| --- | --- | --- |
| Suspension | `@suspends` | the caller must be `@suspends` or use `run` |
| Blocking | `@blocking` | the caller must `offload` it |
| Lock levels | `@acquires(3)` | the caller's held levels must be below 3 |
| Concurrency of calls | `@threadsafe`, `@serial` | whether two tasks may call it at once |
| Concepts of exported types | `sendable`, `shareable` | whether a value may cross a task boundary |
| Module-state footprint | which shared primitives a function touches | rules 4 and 6 across modules |
| Channel protocols | `@protocol((recv; send)* ; close)` on a channel-end parameter | deadlock goals across modules |

A change to any of these changes the interface hash, so a library whose function starts acquiring a higher-level lock, or stops being `@threadsafe`, no longer loads against a binary built for the old one. The ABI evolution rules apply as before. Interfaces refine safely when a function acquires lower levels (or none), suspends where it used to block, or becomes `@threadsafe` where it was `@serial`.

The certificate records each race and deadlock goal with its stage: `types`, `presburger`, `smt`, `topology`, `protocol` (with the pattern it matched) or `mc`. Model-checker results also record the state count and the reduction used, and are only recorded when the search was exhaustive. The trust section gains:

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
| CSP and FDR, occam | channel-only concurrency, and refinement checking of CSP processes for deadlock freedom |
| Go (runtime detector; static checkers such as Gong and Godel) | Go's runtime detects only global deadlock; the static checkers extract channel behaviour and model-check it, as Pia's stages 2 and 3 do |
| Kobayashi's deadlock-free pi-calculus types | the idea that a forest-shaped topology and usage protocols are enough for most programs |
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
10. **Deadlock freedom for channel communication**: channel topology and the forest lemma, then inferred protocols with compatibility checks and pattern lemmas, then the waits-for deadlock check in the model checker.

Each step is a GitHub issue under the tracking issue [#74](https://github.com/deanberris/pia-lang/issues/74): #75 to #83 for steps 1 to 9, and #111, #112 and #113 for step 10.
