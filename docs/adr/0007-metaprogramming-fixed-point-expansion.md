# 7. Metaprogramming from day one, expanded to a fixed point

Date: 2026-11-20

Status: Accepted

## Context

Serialisation, equality adapters, operators and code generators (such as tiled kernels) are core use cases, and generated code must be proved like hand-written code.

## Decision

A metaprogram is an ordinary Pia function (`let meta`) that runs at compile time over quoted syntax (`` `( ... ) `` and `$x` splices), with hygiene on by default. Expansion loops back to parsing until a fixed point: generated code may contain further metaprogram uses. Metaprograms see types only once fully resolved; one that needs a type still being generated is deferred to a later pass, and is an error only if the loop settles with it still waiting. A compiler flag (sketched as `--meta-cycles=N`) caps the number of passes. The first derives are `eq`, `ord`, `hash`, `serialise` and `deserialise`; `deserialise` emits refinement checks.

## Consequences

- Compile time is spent deliberately on expansion so that results are provable by construction.
- Type checking and expansion interleave, which shapes the compiler driver.
