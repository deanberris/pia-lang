# 4. The strongest guarantee is always the default

Date: 2026-11-20

Status: Accepted

## Context

Many features have a strict mode and weaker, cheaper modes (overflow handling, float semantics, unproved obligations). Defaults decide what most code actually gets.

## Decision

The strongest guarantee is the default everywhere, and weaker modes must be asked for explicitly. In particular: integer arithmetic defaults to `@overflow(proof)` (the compiler must prove no overflow; `wrap`, `saturate` and `trap` are opt-in), floats default to strict IEEE semantics, and an unproved obligation is a compile error unless the source writes `@assume` or `@check`.

## Consequences

- Some correct programs will initially fail to compile until annotated; this is intended.
- Every weakening is visible in the source and, where it affects callers, in the interface.
