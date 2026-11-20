# 9. User-defined generics, checked concepts with laws, and adapters

Date: 2026-11-20

Status: Accepted

## Context

Users need their own generic types and constrained generic functions, and the optimiser wants algebraic laws (for example associativity) it can rely on.

## Decision

A generic type is a compile-time function returning a type. Constraints are concepts, written as metaprograms that accept a type or return a diagnostic. Concepts are checked both at the generic definition (the body may use only what its concepts promise) and at each use. Concepts may state laws; every instance must prove them, with no `@assume` escape. A type that does not meet a concept needs an adapter, a value supplying the required functions with its laws proved, which may live in any module. Type arguments are deduced from the call site by default; explicit arguments (`sum<i64> xs`) force an instance or resolve an overload.

## Consequences

- Laws give the optimiser proven rewrites.
- Adapters avoid orphan-rule restrictions while keeping every instance proved.
