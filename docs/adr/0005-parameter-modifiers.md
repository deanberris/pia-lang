# 5. Parameters carry ownership, access and modifiability modifiers

Date: 2026-11-20

Status: Accepted

## Context

The prover needs aliasing, write and lifetime facts at every call boundary, and interfaces must carry them so modules can be verified separately.

## Decision

Each parameter has three independent modifiers: ownership (`borrowed` | `moved`), access (`in` | `out` | `inout`) and modifiability (`fixed` | `mutable`). The default is `borrowed in fixed`. `out` must be fully written before return. Closures capture by borrow unless written `move`.

## Consequences

- Interfaces state everything the prover needs about effects at the boundary.
- Combination rules (for example `out` implies `mutable`; mutable borrows may not alias, with slice disjointness proved) are proposed in `docs/design.md` and still need confirming.
