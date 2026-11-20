# 13. Auto-vectorise as much as possible; keep `vec<T, k>` for explicit control

Date: 2026-11-20

Status: Accepted

## Context

SIMD performance on Apple Silicon is the first milestone, and proved facts (trip counts, alignment, non-aliasing) are exactly what vectorisers need.

## Decision

The optimiser auto-vectorises every loop it can prove safe. `vec<T, k>` remains an ordinary prelude generic for authors who want to fix the vector shape themselves.

## Consequences

- Vectorisation quality depends on the verifier exporting facts to the optimiser.
