# 10. Modules export interfaces; imports name them; proofs carry certificates

Date: 2026-11-20

Status: Accepted

## Context

The language must support massively parallel build and link while proving properties across module boundaries and still allowing aggressive constant folding.

## Decision

A module exports named interfaces: sets of symbols with types and pre/postconditions. Imports must name the interfaces they use, so a module depends on interface artifacts only. Verification is assume-guarantee. Each compiled module carries a proof certificate with a hash of every interface it was proved against, and the linker refuses mismatches. Interfaces may export fixed values as symbols: importers prove against the symbol's type and refinement, and the value is resolved later during cross-module constant folding. A changed value invalidates dependent certificates and forces dependents to recompile.

## Consequences

- Modules type check, verify and compile in parallel.
- Cross-module folding happens late, behind certificate checks.
