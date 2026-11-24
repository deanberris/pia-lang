# 60. `spread` v0: iterations own the cells they write, proved one iteration at a time; MLIR's async runtime runs them

Date: 2026-11-24

Status: Proposed

## Context

M12 ([#13](https://github.com/deanberris/pia-lang/issues/13)) starts with `spread`, the parallel loop of [ADR 0014](0014-concurrency-model.md). Today `spread` parses, and the `pia_par` dialect has a `spread` op over a tiled grid, but IRGen rejects it, there is no runtime, and nothing proves that its iterations do not race. The first program that needs it is sediment transport over basins ([ADR 0055](0055-sediment-transport-in-fixed-point.md), section 6): cells in different basins never exchange mass, so each basin can run its steps on its own core.

[docs/concurrency.md](../concurrency.md) says how races are ruled out in general: every pair of possibly concurrent accesses is justified by ownership, shared reading, proved disjointness, a lock, atomicity or ordering, and disjointness goes to FPL ([ADR 0020](0020-presburger-for-affine-goals.md)) for affine indices and to Z3 otherwise. Two things are left open for a first version:

1. **How disjointness is proved when the indices are not affine.** A basin's cells are not a tile or a range: they are the cells `c` with `owner.[c] = b`, for an owner array computed at run time. FPL cannot express that, and FPL is not built yet. Asking Z3 whether two iterations `i <> j` can write the same cell means encoding the body twice, with everything it computes, which the verifier does not do and which would be slow.
2. **What runs the iterations.** [ADR 0027](0027-coroutines-and-race-freedom.md) puts the scheduler in Pia (`Pia.Task`, work-stealing over `Pia.Sys.Thread`), and `spread` moves onto it in step 4 of the plan. None of that exists yet, and #13 asks for a C++ runtime on CPU threads in the meantime.

## Decision

### 1. An iteration owns the cells it writes

Each buffer that a `spread` body writes has an **ownership predicate** that says which of its cells iteration `i` owns. A body may write a cell, and may read a cell of a buffer it writes, only if it owns that cell. Buffers that no iteration writes may be read anywhere (shared reading).

- **By default, iteration `i` owns cell `i`.** `spread i in 0 .. len out do out.[i] <- f xs.[i] done` needs nothing more. This is the identity owner, and covers the maps and stencils that write their own cell.
- **`@owns(buf, owner)`** on the `spread` names an owner array: iteration `b` owns `buf.[c]` exactly when `owner.[c] = b`. The owner array must be read-only in the loop. Sediment over basins is `spread b in 0 .. nb @owns(bed, label) @owns(load, label) ... do`, with `label` the basin of every cell.

Each access becomes one goal about one iteration: `e = i` for a write `buf.[e]` under the identity owner, `owner.[e] = i` under an owner array. These are ordinary goals of the body, proved like an index bound, with the loop variable an arbitrary value in the range. **They imply that no two iterations touch the same cell**, because an owner array is a function: if iterations `i` and `j` both owned cell `e`, then `owner.[e] = i` and `owner.[e] = j`, so `i = j`. No goal compares two iterations, and the body is encoded once. When FPL lands, an affine index that is not the identity (`out.[2*i]`, a tile) is proved disjoint there instead, and this rule stays for data-dependent owners.

The predicate is a property of the loop, so the race check is local and its cost is linear in the number of accesses. It also tells the reader of the code who writes what.

Other rules of the first version, all checked by the type checker:

- The body may not assign a variable declared outside it. A reduction is `all_reduce` or an atomic, later.
- A buffer the body writes may only be written by `buf.[e] <- v` in the body itself. Passing it to a call is an error until calls have footprints (`modifies` contracts), except as a view `buf.[a .. b]` whose every cell the iteration owns, which is one goal per call: `forall (c in a .. b). owner.[c] = i`.
- What is known after the loop is what a `spread`'s `ensures p` says, proved for an arbitrary iteration at the end of its body, and assumed as `forall (i in lo .. hi). p` after the loop. `p` may read a written buffer only at cells the iteration owns, which is one goal per read, as in the body, so another iteration cannot invalidate it.

### 2. The runtime is MLIR's async runtime, as a trusted v0

IRGen lowers `spread i in lo .. hi` to `scf.parallel`, and codegen runs MLIR's `async-parallel-for`, which outlines the body, splits the range into blocks and runs them on the **MLIR async runtime** (`mlirAsyncRuntime*`, over LLVM's thread pool, one thread per core), with a join at the end of the loop. The runtime is a static C++ library from the LLVM tree we already build, linked into programs that use `spread`. It is listed in the trust report, as the pthreads wrappers of ADR 0027 will be.

This is temporary in the way ADR 0027 already plans: when `Pia.Task` exists, `spread` lowers to it instead, and the trust item goes. The language-level rule of section 1 does not change.

### 3. Spec functions say what they read (amendment, 2026-11-24)

A `spread`'s `ensures` is proved after every cell that another iteration owns has been given an unknown value (section 1). A sum over the cells an iteration owns, which is what a conservation law per basin needs, is a spec function, and the solver cannot see that its value is unchanged when only cells it does not read changed: that is an induction. So such an `ensures` could not be proved.

A spec function over a buffer may say which cells it reads:

```ocaml
let spec rsum (xs : [u32]) (lo : usize) (hi : usize) : u64
  requires lo <= hi && hi <= len xs
  reads xs.[lo .. hi]
  decreases hi - lo
= if lo = hi then 0 else rsum xs lo (hi - 1) + xs.[hi - 1]
```

- **The footprint is `reads xs.[a .. b]`**, a range of a buffer parameter, or `reads xs where p`, the cells `c` of `xs` with `p` (for example `owner.[c] = b`). A spec function with no `reads` reads all of every buffer it takes, as today.
- **The frame lemma is a goal.** piac proves, once, for the spec function: for two arrays that agree on the footprint, it gives the same result. It is proved by induction on the function's own `decreases`, with the function unfolded once on each side, so it needs no lemma from the user; if it fails, the `reads` clause is wrong and the error says so.
- **The verifier uses the frame.** Wherever a buffer's contents change, by a write, a call, a loop or a `spread`'s forgetting of other iterations' cells, a call of a framed spec function on the new contents equals the same call on the old contents when every changed cell is outside its footprint. The verifier states this as a fact for the calls it meets, the way it unfolds a spec function's definition once, so a goal never needs a frame lemma by hand.

With frames, a basin's conservation law `rsum bed lo hi + rsum load lo hi + ... = old (...)`, over the range of the basin's cells in a basin-major layout, is stable under the other basins' writes, and a `spread` over basins proves it per basin. The sum over all basins is then a telescoping lemma over the ranges.

### Alternatives

- **Two iterations encoded at once**, asking Z3 for `i <> j` writing the same cell: general, but it encodes the body twice, with every value it computes, and a model mixes two iterations' states. Rejected for v0; FPL takes the affine cases, and owner arrays take the rest.
- **A runtime of our own over pthreads**: about 150 lines of C, a fixed pool and a chunked range, but codegen would have to outline the body and pack its captures itself, which `async-parallel-for` already does and tests.
- **OpenMP** (`scf-to-openmp`): needs `libomp`, which macOS does not ship.
- **Grand Central Dispatch** (`dispatch_apply`): simple on macOS, but not on the Linux targets Pia also builds for.
- **Writing `Pia.Task` first**: the right end state (ADR 0027), but it needs coroutines, `scope` and `spawn`, which are several steps away. Sediment over basins should not wait for them.

## Consequences

- `spread` over an index range compiles and runs on all cores in the first version, and its race freedom is proved, with a goal per access that names the cell and the iteration in its counterexample.
- Sediment transport can run basin by basin in parallel, with the basin labels of `drainage` as the owner array.
- Programs that use `spread` link the MLIR async runtime and say so in their trust report, until `Pia.Task` replaces it.
- Calls that write a shared buffer wait for footprints. `spread` over tiles (the `pia_par` grid op) and the collectives are still to come.
- With `reads` frames (section 3), a spec function's value is known to survive writes outside what it reads. This helps sequential code too: the frame lemmas written by hand today, such as the sediment sum's `frame`, become facts the verifier states itself.

## Questions for Dean

1. The ownership rule (section 1): one predicate per written buffer, the identity by default and `@owns(buf, owner)` for an owner array. Is `@owns` the spelling you want, or would you rather write it in the header, as in `spread b in 0 .. nb owning label do`?
2. ~~The runtime (section 2): MLIR's async runtime as a trusted v0, replaced by `Pia.Task` later, or a small pthreads runtime of our own now?~~ Answered 2026-11-24: MLIR's async runtime, trusted.
3. ~~Frames (section 3): `reads` clauses on spec functions, with a generated frame lemma, or (the weaker choice) per-iteration totals computed at run time, so that the global conservation law becomes a run-time check rather than a proof?~~ Answered 2026-11-24: `reads` frames on spec functions.
