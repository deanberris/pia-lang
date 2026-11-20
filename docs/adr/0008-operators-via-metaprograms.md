# 8. Operators are defined only through metaprograms

Date: 2026-11-20

Status: Accepted

## Context

Built-in operators would hard-code arithmetic semantics and overflow modes into the core language.

## Decision

The core language has named functions only (`add`, `add_sat`, `vec_add`). Every operator, including `+ - * / < =`, is declared by an `operator` metaprogram that maps a symbol, precedence, associativity and operand types to an expansion. The standard operators live in a prelude imported by default.

## Consequences

- The parser must support user-declared infix operators with precedence.
- Overload resolution for operators uses the same rules as for generics (ADR 0009).
