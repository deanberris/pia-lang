# 23. A minimal core, with the standard library written and proved in Pia

Date: 2026-11-21

Status: Proposed

## Context

Pia needs a standard library, and Dean wants it written in Pia so that it is verified like any other Pia code. Today Pia has no I/O, no allocation, no sum types and no bitwise operators, so the edge demo needs a C `main` for BMP files and buffers. The flagship demo needs PNG and GIF codecs in Pia. And any `*` in a module widens the whole SMT encoding to 132 bits, so loop goals time out. Dean's requirements: the core calls POSIX directly and wraps it in strongly typed, contract-constrained functions; FFI carries explicit contracts, with calls marked `unsafe` where it does not; and a runtime error handler prints stack traces and debug info when available. The detail is in [docs/stdlib.md](../stdlib.md).

## Decision

- A feature is in the core only if Pia cannot express it, the verifier must know its meaning, or it shapes the language. Everything else is library code in Pia, proved when the library builds.
- The core adds: integer bit builtins (with C-style prelude operators `& | ^ ~ << >>`, where `|` is bitwise or only inside parentheses), `widen`/`narrow`/`mul_wide`, sum types and `match`, spec functions and lemmas, slicing and constant arrays, `@linear` types, `extern`, `unsafe`, `addr`, `@trusted`, metaprogram type queries, and later float, vector and atomic builtins. Modules (M8) and generics (M9) are core as already decided.
- FFI is `= extern "symbol"` as a function body. A foreign function with a `requires` or `ensures` clause is called normally: its preconditions are goals and its postconditions are trusted. One without a contract can only be called as `unsafe f x`, which assumes nothing about the result.
- POSIX is reached through libSystem, declared with weak, cited contracts in one trusted module, `Pia.Sys.Posix`. The rest of `Pia.Sys` wraps it in strong types and is fully proved: errors are a `result` of a decoded `errno`, and handles such as `fd` are `@linear`, so they are closed exactly once.
- `addr` and `assume` are only allowed in modules marked `@trusted`. Each module's certificate lists its own trusted items (foreign contracts, `unsafe` call sites, `assume`s, accepted unproved goals), and `piac --trust-report` computes a program's transitive trusted base from the certificates. The format is [ADR 0024](0024-published-proof-certificates.md)'s.
- Allocation is Pia over `mmap`, through explicit allocators ([ADR 0026](0026-memory-manager.md)). Allocation failure is a `result` by default.
- Every run-time trap and fatal signal goes to one handler in `Pia.Rt`, written in Pia: it prints the Pia source location, a frame-pointer stack trace symbolised with `dladdr`, DWARF file and line when available, and exits with status 134. Programs may replace it.
- Multiplication is handled by a ladder in the verifier: per-goal bit widths, linear encoding of constant products, intervals, an opaque product with library lemmas, and exact nonlinear arithmetic only in a query of its own.

## Consequences

- The trusted base is the compiler, `Pia.Sys.Posix`, `Pia.Rt`, and whatever a program marks `@trusted` or `unsafe`, and it can always be listed.
- The edge demo can drop `main.c` once files, `main` and arenas exist, and use BT.601 once per-goal widths land.
- `unsafe` becomes a word the core gives meaning to, as `extern` does. Neither is a reserved keyword.
- Much of the work (the multiplication ladder, bit builtins, spec functions, variants, FFI) does not need modules, so it can proceed alongside M8.
- libm is never trusted: every maths function is written and proved in Pia, with its error bound in its contract.
