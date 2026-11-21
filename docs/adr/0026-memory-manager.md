# 26. A memory manager of explicit allocators, with no garbage collection

Date: 2026-11-21

Status: Proposed

## Context

Dean: the runtime needs a real memory manager. Naive `malloc` and `free` aren't enough; Pia needs arena allocators and explicit memory management, and no garbage collection. There is no `new` keyword: allocation is an explicit function of the memory module, which keeps TCMalloc-style size classes and arenas for tasks, fibers and coroutines. Its free lists must be proved to supply enough memory or fail, and every allocation must be handled at its call site. [ADR 0023](0023-minimal-core-self-hosted-stdlib.md) sketched `Pia.Mem` as an arena plus `alloc`/`free` over `mmap`. The detail is in [docs/stdlib.md](../stdlib.md#7-linear-resources-and-memory).

## Decision

- Pia has no garbage collector, now or later, and no `new` keyword. All memory is managed by allocators written in Pia over `mmap`, through ordinary function calls.
- Allocators are explicit values, reached through `borrowed` handles that many containers can share, that meet an `Allocator` concept (`alloc`, `free`, `resize`), passed as parameters. Library code never allocates from a hidden global, and `main` receives the root allocator.
- `Pia.Mem` provides `pages`, `fixed_buffer`, `arena`, `scratch` (LIFO with marks), `pool<T>` (fixed-size slab), `general` (TCMalloc-style: size classes, per-task caches, central free lists and a page heap of spans) and `shared<a>` (thread-safe wrapper with per-thread caches). Each proves its invariants as module state.
- Lifetimes are checked by two Sema rules, with no lifetime syntax in ordinary code: a `borrowed(m)` result cannot outlive `m`, and `m` cannot be moved while it is lent; and `with_arena` scopes a region so that nothing allocated in it escapes. Freeing into the wrong allocator is a proof goal, through a ghost `owns` fact.
- Every `alloc` returns a `result` that must be handled where it is called (with `match` or `?`, ADR 0028); there is no trapping variant. Its proved postcondition is enough memory, disjoint from every live block, or `Err OutOfMemory` with the allocator unchanged. All free lists live in `Pia.Mem`, and the proof covers them.
- Each task, worker and coroutine scope gets its own arena and `general` cache by default.
- Allocators and their buffers have `Drop` instances, so memory not freed explicitly is freed at scope end (ADR 0028).
- Concurrency: each task, worker or coroutine scope gets its own allocator by move. Stackless coroutine frames come from the task's allocator ([ADR 0027](0027-coroutines-and-race-freedom.md)). `shared<a>` is the only synchronised allocator, and its refill lock is a top-level leaf lock that never suspends.

## Acceptance

The design is accepted when `Pia.Mem.Vec`, a growable array over explicit heap allocation, is implemented and proved end to end: indices in bounds, no uninitialised reads, no overflow in capacity arithmetic, growth that gives enough memory or fails leaving the vec unchanged, no double free or use after free, no leak (RAII on every exit), frees into the right allocator, and no vec outliving its allocator. The sketch is in [docs/stdlib.md](../stdlib.md#the-litmus-test-a-proved-growable-array).

The second acceptance test is free-list reuse ([sketch](../stdlib.md#the-second-test-free-list-reuse)): a freed block handed out again provably aliases no live object, is reachable by no stale owner or borrow, and comes back `out`, so the old contents cannot be read. Free lists are side metadata (slot-index stacks per span), not pointers threaded through freed blocks, so `Pia.Mem` needs no `addr` and stays out of the trusted base.

## Consequences

- Proved code cannot leak, double free or use after free, with no run-time cost and no pauses.
- Every allocating API takes an allocator parameter, which is more to write than with a global heap, but shows where memory comes from.
- Sema needs a lexical borrow check for `borrowed(m)` results. It is smaller than Rust's, because borrows are lexical and regions are scoped.
