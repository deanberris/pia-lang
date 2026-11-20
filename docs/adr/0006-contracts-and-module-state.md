# 6. Contracts, refinement types, and module state as exported symbols

Date: 2026-11-20

Status: Accepted

## Context

Pia must prove modules keep the contracts they advertise, including stateful protocols such as open/pull/close on a stream.

## Decision

There are four contract forms: refinement types (`int{0..255}`, `{ x : f32 | x >= 0.0 }`), pre and postconditions (`requires`, `ensures`), invariants (loop, struct, module), and state properties. Module state has no special syntax: an interface is a set of exported symbols, each with its type and pre/postconditions, and exported state is one more symbol constrained by those conditions. All forms lower to contract ops in Pia's MLIR dialects and become solver assertions.

## Consequences

- Importers prove each call against exported contracts; exporters prove their bodies keep every postcondition.
- No typestate machinery is needed in the type system.
