# 14. Concurrent by default: collectives, task graphs, futures; collectives proved to match

Date: 2026-11-20

Status: Accepted

## Context

The flagship demo needs distributed, data-parallel execution, and deadlock freedom must be provable at compile time.

## Decision

The runtime is concurrent by default. Pia will have MPI-like collectives, task graphs and futures, built in the order the stream delineation demo needs them: collectives and `par_for` first, then task graphs (for flow accumulation), then futures. Matching of collectives is proved by a protocol metaprogram that checks every worker issues the same sequence, backed by a model checker pass for interleavings it cannot settle. Session types are rejected as too runtime-dependent. Tiles are `moved` to workers, so data races are ruled out by ownership.

## Consequences

- Needs a model checker pass in the verifier.
- Collectives are library metaprograms, not built-ins.
