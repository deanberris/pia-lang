# 27. Stackless coroutines, structured tasks, and race freedom proved from permissions

Date: 2026-11-21

Status: Proposed

## Context

Dean wants coroutines or green threads in Pia, locking and synchronisation and communication primitives, and a prover that says whether access to a resource could race. [ADR 0014](0014-concurrency-model.md) made Pia concurrent by default and ruled out races on tiles by moving them to workers, but did not cover tasks, locks, atomics, channels or shared resources in general. [ADR 0004](0004-strongest-guarantee-by-default.md) requires an unproved race to be a compile error. The detail is in [docs/concurrency.md](../concurrency.md).

## Decision

- **Stackless coroutines.** A function that suspends is compiled to a state machine whose frame has a size known at compile time, lowered through LLVM's `llvm.coro.*` intrinsics. Stackful green threads are rejected, because their stack size is a goal Pia cannot prove in general. "Green threads" are tasks on a scheduler written in Pia (`Pia.Task`: work-stealing workers over `Pia.Sys.Thread`, kqueue for I/O, a deterministic mode for tests and counterexample replay). `spread` and the collectives run on the same scheduler.
- **Keywords `wait` and `yield`**, and an `@suspends` effect that is inferred inside a module and written in exported interfaces. Blocking foreign calls are marked `@blocking` and must go through `Pia.Task.offload` from suspending code.
- **Structured tasks.** `spawn` returns a `@linear` `task<T>` that must be joined inside the `scope` that started it, so tasks may borrow from their parent. No detached tasks in the first version. Cancellation is an explicit token.
- **Primitives in the library** (`Pia.Sync`, `Pia.Chan`): `mutex<T>` and `rwlock<T>` own their data and are reached only through scoped `lock` closures that may not suspend, with the data type's refinement as the lock invariant. `atomic<T>`, channels whose `send` takes `moved`, `once`, `barrier`, `semaphore` and `event`. No bare condition variables.
- **Static lock levels.** Each lock has `@level(n)`. A task may only acquire a lock above every level it holds, and interfaces record `@acquires(n)`. Lock-order deadlock is then a type error.
- **Race freedom from permissions.** Every pair of possibly concurrent accesses must be justified by ownership, shared `fixed` reading, proved disjointness, a lock, atomicity, or a happens-before edge. The type checker settles most of these, using the `sendable` and `shareable` concepts (derived over fields) and task boundaries. Disjointness goes to FPL ([ADR 0020](0020-presburger-for-affine-goals.md)), then Z3. The model checker settles the rest: the primitives' own implementations, protocols and deadlock, and user code built from atomics. Non-memory resources (positioned file I/O, `stdout`) carry footprints that are checked the same way.
- **Memory orders.** Sequential consistency and release/acquire are checked from the start. `relaxed` is accepted where its value orders nothing, and otherwise is an unproved obligation until the model checker has an RC11 mode.
- **The model checker is exhaustive.** It uses DPOR and symmetry reduction. A search that hits a limit is unproved, never proved.
- **Unproved races, deadlocks and `relaxed` uses are compile errors**, with a witness (FPL sample, Z3 model or schedule). `--allow-unproved=race:...`, `deadlock:...` and `relaxed:...` accept them as trust items.
- **Certificates.** `@suspends`, `@blocking`, `@acquires`, `@threadsafe`/`@serial`, `sendable`/`shareable` of exported types, and module-state footprints are part of the interface and its hash ([ADR 0024](0024-published-proof-certificates.md)). The certificate records each race goal's stage and, for the model checker, the exhaustive search size. Accepted races, `@threadsafe` foreign claims and still-trusted primitives are trust items.

## Consequences

- The borrow checker becomes the race checker. Most programs never reach the model checker.
- Function colouring is visible, and generic code over both colours needs effect polymorphism in generics (M9).
- The model checker is substantial work. Until it lands, the primitives are trusted wrappers over `os_unfair_lock` and pthreads, and the trust report says so.
- Races between processes, for example on the file system, are out of scope.
