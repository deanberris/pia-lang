# 12. Three ways to license float reassociation and FMA

Date: 2026-11-20

Status: Accepted

## Context

Strict IEEE semantics block reassociation, so tiled and vectorised float reductions cannot be proved equal to their naive specification.

## Decision

Strict IEEE is the default (ADR 0004). Pia supports three opt-in approaches: a per-function `@fp(reassoc, contract)` attribute (contracts proved over reals); a wrapper type such as `fast f32` with a `Numeric` adapter whose proof model uses real addition; and an error tolerance stated in `ensures` with strict IEEE semantics, proved by a rounding-error analysis pass.

## Consequences

- Authors choose where the licence lives: function, type, or contract.
- The tolerance approach needs a dedicated error-analysis pass; bit-precise Z3 floats won't scale.
