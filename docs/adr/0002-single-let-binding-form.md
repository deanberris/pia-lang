# 2. `let` is the only binding form

Date: 2026-11-20

Status: Accepted

## Context

Pia aims for a minimal core with OCaml-like syntax. Separate keywords for values, functions, lambdas and type declarations multiply the grammar and the cases the verifier must model.

## Decision

`let` binds every value, including functions and types. A nameless `let` is a function literal: `let (x) => x * x`. There is no `fun`, `lambda` or `type` declaration keyword. Function literals are curried (`let (a) (b) => a + b`), not tupled. `let rec` marks recursion so the prover can demand a termination measure. Bindings are immutable; mutation goes only through `mutable` parameters or locals.

## Consequences

- The grammar has one binding production plus the `type` constructor expression.
- Types being values means type-level functions are ordinary compile-time functions (see ADR 0009).
- Partial application is always available, so the optimiser must handle closure creation well.
