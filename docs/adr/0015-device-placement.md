# 15. Device placement: compiler cost model, explicit, or overridable

Date: 2026-11-20

Status: Accepted

## Context

Work may run on CPU cores, the GPU, or eventually the Neural Engine, and authors sometimes know better than a cost model.

## Decision

Three forms are supported: `@place(auto)` uses the compiler's cost model; `@place(gpu)` or `@place(cpu)` fixes the device; `@place(auto, prefer = gpu)` keeps the cost model but overrides it. Placement must never change the proved result. CPU and GPU (Metal) are first targets; the Neural Engine is reachable only through Core ML, so it is a later, optional target for fixed operations.

## Consequences

- Placement interacts with float rules (ADR 0012).
