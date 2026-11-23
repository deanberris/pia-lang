# 55. Sediment transport is integer mass moved downhill in height order, with conservation proved exactly

Date: 2026-11-23

Status: Accepted

## Context

[ADR 0016](0016-stream-delineation-flagship-demo.md) makes sediment transport, with a proved conservation law, the second half of the flagship demo. [docs/design.md](../design.md#stress-test-stream-delineation) states the law "within the chosen float tolerance", which ties the stage to floats (M11, [#12](https://github.com/deanberris/pia-lang/issues/12)) and to [ADR 0038](0038-float-kernels-against-real-theories.md)'s rounding bounds. Neither is built.

Dean decided (2026-11-23, on the [survey of the path to the GPU demo](https://claude.ai/artifact/GNhoJ74ocgLnBPzE5kUcFA)) to build sediment transport now, in fixed point, without waiting for floats.

The delineation in [streams.pia.md](../streams.pia.md) already gives this stage what it needs: a filled surface `fill`, a direction `down` for every cell that points strictly downhill or at itself (an outlet), the slope `drop` of each route in the 10:7 weights, and the flow accumulation `acc`.

## Decision

### 1. Mass is an integer, so conservation is an equation

Sediment is counted in whole units of mass, `u32` per cell, in two buffers: `bed`, the erodible sediment resting in each cell, and `load`, the sediment carried in the water leaving it. One more `u64` counts `out`, the mass that has left the map through outlets.

The law is that the total never changes:

```ocaml
sum bed + sum load + out = old (sum bed + sum load + out)
```

This is exact. There is no tolerance and no rounding term, which is a stronger theorem than the float version in design.md. That version can come back after M11 as a refinement: a float model whose result is within a proved distance of this one.

Because the total is fixed, it also bounds every partial sum. A precondition that the initial total fits in `u32` proves that no cell's `bed` or `load` and no running sum can overflow, with no saturation.

### 2. The model: capacity, erosion and deposition per cell

Each cell has a transport **capacity**, how much the water leaving it can carry. It is a monotone function of the flow and the slope, computed in integers from `acc` and the route's `drop`:

```ocaml
capacity c = min cap_max (scale (acc.[c]) (drop c))
```

`scale` is chosen to keep the proof linear: shifts and additions, or a widening `u64` product whose bound intervals settle without Z3, never a product of two variables inside a quantified goal ([#45](https://github.com/deanberris/pia-lang/issues/45)). The conservation proof does not depend on the formula at all, only on its result being a `u32`, so the formula can be tuned later without touching the proof.

A cell receives `inflow`, the loads of the cells that drain into it. Then:

- if `inflow < capacity`, the water **erodes** `e = min (capacity - inflow) bed.[c]`: the bed loses `e` and the load is `inflow + e`.
- otherwise it **deposits** `d = inflow - capacity`: the bed gains `d` and the load is `capacity`.

Each branch moves mass between `bed` and `load` and creates none, which is the whole of the per-cell proof.

### 3. Cells are processed from high to low, so one pass is one time step

`down` points strictly downhill, so ordering the cells by decreasing `fill` is a topological order of the flow graph: every cell comes after all the cells that drain into it. A step walks the cells in that order and pushes each cell's load into `inflow.[down.[c]]`, or into `out` at an outlet. Sediment then travels the whole way to the outlet in one step, as water does in the accumulation.

The order is a buffer of cell indices, sorted once per map with `Pia.Core.Algo.Sort` and passed in with its contract (a permutation of `0..n`, decreasing in `fill`). The same order serves the topological flow accumulation that replaces `walk` for large maps (item 1 of the survey), so the two share it.

### 4. The proof is a sum and a point-update lemma

`sum` is a spec function over a slice, with one lemma proved by induction: writing `v` at index `i` changes the sum by `v - a.[i]`. Every transfer in a step is a pair of such writes, one down and one up by the same amount, so the loop invariant is the conservation equation itself, and each iteration preserves it by two uses of the lemma. Nothing is nonlinear and no quantifier holds a product, which keeps the goals out of [#96](https://github.com/deanberris/pia-lang/issues/96)'s slow cases.

The other theorems of the stage:

- **No overflow**, from the fixed total (section 1).
- **Every transfer goes downhill or out**: mass moves only from a cell to `down.[c]`, which is lower, or to `out`.
- **Erosion is bounded by the bed**: no cell's `bed` goes below zero, by construction of `e`.

### 5. The terrain stays fixed at first

In this first version, `fill`, `down` and `capacity` do not change between steps. Sediment moves over a fixed landscape, which is enough to colour the streams by load, as the demo's render step needs. Letting erosion and deposition change the heights (landscape evolution) means recomputing the fill and the directions every few steps. It is a later step, and the conservation law carries over unchanged, since it does not mention heights.

Dean decided (2026-11-23) that the fixed terrain is for building and proving the transport model only. The goal after it is **terrain evolution under rainfall models**, rendered as an **animated GIF**:

- **Rainfall models** replace the uniform one unit of water per cell in `acc` with a rainfall field per time step (uniform, a storm moving across the map, or seasonal), so each step's flow is accumulated rainfall, not area.
- **Evolution**: each step's erosion lowers `fill` and deposition raises it, in integer height units, and the fill and the directions are recomputed every few steps. The conservation law still holds across a recomputation, because it counts mass, not heights.
- **Animated GIF**: one frame per few steps, through the proved GIF encoder of [ADR 0054](0054-proved-gif-and-jpeg-codecs.md) (multiple frames with a delay, and a palette shared across frames so colours stay stable between frames).

### 6. The GPU form comes later and is proved against this one

Processing cells in height order is sequential. The GPU form ([survey](https://claude.ai/artifact/GNhoJ74ocgLnBPzE5kUcFA), items 3 to 7) is a "pull" step: every cell reads its eight neighbours and adds the loads of those that drain into it. Each cell writes only itself, so the step is race-free. Its conservation proof needs one more lemma, that summing every cell's inflow counts every pushed load once (a reindexing of the sum over `down`). Moving mass one cell per step, that form needs as many steps as the longest flow path to carry sediment to the outlet. So it is a second implementation proved to conserve the same total, not a replacement for the sequential one.

Dean decided (2026-11-23) the order: **sequential first, then concurrent on the CPU, then GPU offload last.** The CPU step needs no new lemma: cells in different basins never exchange mass, so each basin (the cells sharing an outlet label from the accumulation) is an independent sequential problem in height order, and basins run in parallel with `spread` (M12), each owning its disjoint set of cells. The total is the sum of the basins' totals, each conserved. The pull step above is the GPU form, after that.

### 7. Render

`render` colours stream cells by `load`, through an integer colour map: a ramp over `log2 load` from `Pia.Core.Bit`'s count of leading zeros. No `exp` or `log` is needed, so `Pia.Math` is not on this path either.

## Steps

1. `sum` and the point-update lemma, prototyped in the REPL, then in `tests/verify`.
2. The per-cell erode-or-deposit function and its conservation contract.
3. The height order: a proved sort of cell indices by `fill`, and the topological accumulation that uses it.
4. `transport`, one step over the whole map, with the conservation equation as its postcondition; `steps n` repeats it.
5. In `docs/streams.pia.md`: the new stage, `render` by load, and the theorems listed under "What is proved".
6. Rainfall fields in place of uniform water, then heights changed by erosion and deposition, with fill and directions recomputed every few steps.
7. The animated GIF, once ADR 0054's encoder writes multiple frames.

## Consequences

- The flagship demo's conservation law is proved now, exactly, and does not wait for M11.
- design.md's "within the chosen float tolerance" becomes "exactly, in integer mass units", and the float form becomes a later refinement.
- The topological order is shared by sediment transport and the scalable accumulation, so building one advances the other.
- The physics is simplified: one sediment class, fixed terrain, a capacity rule rather than a calibrated erosion law. It is a demonstration of a proved conservation law, not a geomorphology model.

## Questions for Dean (answered 2026-11-23)

1. ~~Fixed terrain first (section 5)?~~ Answered: fixed for building the model only, then terrain evolution under rainfall models, rendered as an animated GIF.
2. ~~Sequential first, pull step later?~~ Answered: sequential first, then concurrent on the CPU (basins in parallel), then GPU offload last.
