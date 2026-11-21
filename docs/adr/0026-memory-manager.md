# 26. A memory manager of explicit allocators, with no garbage collection

Date: 2026-11-21

Status: Proposed

## Context

Dean: the runtime needs a real memory manager. Naive `malloc` and `free` aren't enough; Pia needs arena allocators and explicit memory management, and no garbage collection. [ADR 0023](0023-minimal-core-self-hosted-stdlib.md) sketched `Pia.Mem` as an arena plus `alloc`/`free` over `mmap`. The detail is in [docs/stdlib.md](../stdlib.md#7-linear-resources-and-memory).

## Decision

- Pia has no garbage collector, now or later. All memory is managed by allocators written in Pia over `mmap`.
- Allocators are explicit, `@linear` values that meet an `Allocator` concept (`alloc`, `free`, `resize`), passed as parameters. Library code never allocates from a hidden global, and `main` receives the root allocator.
- `Pia.Mem` provides `pages`, `fixed_buffer`, `arena`, `scratch` (LIFO with marks), `pool<T>` (fixed-size slab), `general` (segregated size classes) and `shared<a>` (thread-safe wrapper with per-thread caches). Each proves its invariants as module state.
- Lifetimes are checked by two Sema rules, with no lifetime syntax in ordinary code: a `borrowed(m)` result cannot outlive `m`, and `m` cannot be moved while it is lent; and `with_arena` scopes a region so that nothing allocated in it escapes. Freeing into the wrong allocator is a proof goal, through a ghost `owns` fact.
- Out of memory is a `result`. A named `alloc_or_trap` traps through `Pia.Rt`.
- Concurrency: each task, worker or coroutine scope gets its own allocator by move. Stackless coroutine frames come from the task's allocator (ADR 0027). `shared<a>` is the only synchronised allocator, and its refill lock is a top-level leaf lock that never suspends.

## Consequences

- Proved code cannot leak, double free or use after free, with no run-time cost and no pauses.
- Every allocating API takes an allocator parameter, which is more to write than with a global heap, but shows where memory comes from.
- Sema needs a lexical borrow check for `borrowed(m)` results. It is smaller than Rust's, because borrows are lexical and regions are scoped.
