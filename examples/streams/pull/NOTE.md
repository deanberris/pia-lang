# The pull-form sediment step: parked

This is a prototype, not yet part of the demo. It is parked until
[ADR 0063](../../../docs/adr/0063-opaque-spec-functions.md) (opaque spec
functions, revealed per proof) is built. Nothing builds or tests these
files yet.

The pull form is the GPU-shaped version of one sediment step ([ADR 0055,
section 6](../../../docs/adr/0055-sediment-transport-in-fixed-point.md)).
The cells are taken in waves of equal height. Within a wave, every cell
pulls its inflow from those of its 8 neighbours that drain into it, and
writes only its own slot. The goal is to prove it equal, cell for cell, to
the sequential step of `docs/sediment.pia.md`.

## What is here

- **`kernel.pia`** (127 goals, all proved). One wave as a `spread` with
  identity ownership. Each iteration gathers the loads its upstream
  neighbours carry (`gather`, equal to the spec `inflow_of`). It then
  erodes or deposits, conserving mass, into scratch slots of its own.
- **`unique.pia`** (232 of 233 goals proved). The equality argument:
  - A step is `settled` when every cell's bed and load follow from its
    inflow `seen`, by `eb` and `el`.
  - It is `linked` when every `seen.[c]` is `inflow_of` the loads of `c`'s
    upstream neighbours.
  - `unique` says two settled, linked steps from the same start are the
    same step. Its proof is induction along the height order (`agree`):
    a cell's upstream neighbours are higher (`later`), so they come
    earlier, so they agree by then.

## What blocks it

The one unproved goal is `agree`'s postcondition, which times out. It is
not a hard goal: the same proof goes through when the `linked` hypothesis
is dropped. A loop that does the same induction fails even on its
trivially true entry invariant.

The cause is a matching loop in Z3. `linked`, instantiated at a cell,
reads `flux` at its neighbours. A per-cell quantifier, `settled` or
`determined`, then instantiates at those neighbours. That gives new `seen`
terms, which instantiate `linked` there in turn, and so on across the
whole grid.

Pia has no way yet to give a spec quantifier its triggers, or to keep a
spec function folded. ADR 0063's opaque spec functions are the fix:
`linked` and `settled` folded, revealed only at the cell a step needs.

## What is left once ADR 0063 lands

1. Make `linked` and `settled` opaque, and reveal them at `c` in `agree`.
2. Prove the sequential step (a copy of `transport`) settled and linked:
   - record each cell's inflow when it is processed;
   - keep the invariant that an unprocessed cell's inflow is the sum over
     its processed upstream neighbours.
3. Prove the pull step settled and linked. The kernel gives each wave's
   cells. An apply pass then commits each wave, zeroing the upstream loads
   it pulled, so that conservation is a chain of point updates.
4. `D8` directions must also promise that `down.[k]` is one of `k`'s
   eight neighbours (`adjacent`), which `directions` does not state yet.
5. Make it a page, `docs/pull.pia.md`, and time it on the SRTM tile against
   the sequential and the basin `spread`.
