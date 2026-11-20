# 3. Strong static typing; dynamic typing only through tagged values

Date: 2026-11-20

Status: Accepted

## Context

The prover needs every value's type to be known to reason completely, but some programs (decoders, heterogeneous data) want dynamic typing.

## Decision

Every expression has a static type and there are no implicit conversions. Dynamic typing exists only as `dyn`, a tagged value whose tags form a closed sum the prover can enumerate (optionally narrowed, as in `dyn[u8 | f32]`). Each tag maps to a Z3 datatype constructor, so matches over `dyn` are checked for exhaustiveness. Lowering erases tags the prover shows are unique; the proof model always keeps them. Generics are monomorphised before verification.

## Consequences

- Proofs are about concrete types only.
- `dyn` costs nothing at runtime when the prover can resolve it.
