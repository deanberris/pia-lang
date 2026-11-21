# 28. Errors propagate with `?` to a scope's handler; cleanup runs at scope end

Date: 2026-11-21

Status: Proposed

## Context

Every allocation and every system call can fail, and Dean wants each failure handled where it happens ([ADR 0026](0026-memory-manager.md)). He likes `?`-style propagation where a scope defines one handler for the closed set of errors that can occur in it. He also wants RAII for anything not freed explicitly, so the language needs cleanup handlers that run at scope end. The detail is in [docs/stdlib.md](../stdlib.md#errors-and-scope-cleanup).

## Decision

- `result t e` carries a closed error set `e`, a variant type or a union of them, and error sets are part of function interfaces. A `result` must be used.
- `e?` yields the `Ok` payload or jumps with the error to the nearest enclosing `handle` block. With no handler, the error is returned, and the function's declared error set must include it.
- A `handle` block on a function body, `let ... in` scope or loop body must cover exactly the closed set of errors its scope's `?`s can produce. The compiler computes that set.
- `defer e` registers cleanup for scope end. Types with a `Drop` instance are dropped at the end of their owning scope unless moved or freed. Both run in reverse order on every exit, including `?`.
- Cleanup has no error set, cannot suspend, and takes no lock other than a top-level leaf lock. A resource whose cleanup can fail is `@linear` and must be consumed explicitly. A trap runs no cleanup.
- With ADR 0027: `?` does not cross a task or `lock` closure (a task's error returns from `join`; a lock body's error is its result, after release). A `scope` exiting early joins or cancels-then-joins its children before running its own cleanup. Cancellation is an explicit token that yields `Err Cancelled`.
- `handle` and `defer` become reserved words.

## Consequences

- Failure paths are visible and exhaustively handled, and cleanup is guaranteed on all of them, which is what lets every allocation be fallible without clutter.
- The verifier walks each exit's cleanup as code at that exit, so drops are proved like everything else.
- IRGen needs scope-exit lowering (a cleanup chain per scope), which is also what coroutine cancellation uses (ADR 0027).
