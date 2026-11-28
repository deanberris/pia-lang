# 86. Collectives in a `spread`: `all_reduce` and `halo_exchange`, proved to match, run as phases

Date: 2026-11-28

Status: Proposed

## Context

M12 ([#13](https://github.com/deanberris/pia-lang/issues/13)) is done when `sediment_step` runs on CPU threads and a mismatched collective is rejected at compile time. `spread` v0 ([ADR 0060](0060-spread-v0-ownership-and-runtime.md)) has the loop, the ownership rule and the runtime, and 0.1.0 needs collectives on the CPU ([ADR 0080](0080-release-0-1-0-gates.md), section 3).

[ADR 0014](0014-concurrency-model.md) says what a collective is: every worker takes part, and the program is correct only if every worker reaches the same collectives in the same order, which is checked at compile time. [design.md](../design.md) sketches `sediment_step` with a `halo_exchange` before the stencil and an `all_reduce add` of the outflow after it.

Three things are open:

1. **What a worker is.** A `spread` iteration is one, so a collective is a call in a spread body that every iteration of the range joins.
2. **How "the same collectives in the same order" is proved.** Two iterations would have to be compared, which ADR 0060 avoided for ownership, and for the same reason: the body would be encoded twice.
3. **How it runs.** The MLIR async runtime splits a spread's range into blocks and runs a block's iterations one after the other on one thread, so an iteration that waits at a barrier for the next iteration of its own block waits forever.

## Decision

### 1. Two collectives, in a spread body

- **`all_reduce op e`** combines `e` from every iteration with `op`, and every iteration gets the result. `op` is `add`, `min` or `max` over integers, or `or` and `and` over `bool`. `add` gives a 64-bit result, `u64` for unsigned contributions and `i64` for signed ones, so the sum of up to 2^32 32-bit values cannot overflow; the goal is that `hi - lo` times the largest magnitude of `e`'s type fits the result. A 64-bit contribution is allowed when the range has one iteration, so in practice the contribution is 32 bits or less.
- **`halo_exchange b1 ... bk`** names buffers the spread writes. After it, until the next collective, the iteration may read every cell of each `bj`, not only its own, and no iteration may write them. It is the place where cells written by their owners before it become visible to everyone. In shared memory there is nothing to copy: the exchange is the barrier.

A collective is only allowed in a spread body itself, not in a function it calls, a lambda, a `match`, or a handler, which v0 rejects.

Both are names the compiler knows, not Pia functions with a body. A collective has no body that one iteration could run on its own, which is the exception the no-builtins rule allows; ADR 0014's "library metaprograms" waits for the protocol language of ADR 0053.

### 2. Collectives match because the control flow that reaches them is uniform

A value is **uniform** when it is the same in every iteration: a name bound before the spread, a constant, the result of an `all_reduce`, a cell of a buffer the spread does not write at a uniform index, and anything computed from uniform values alone. The loop variable is not uniform, and neither is a cell of a buffer the spread writes.

The **protocol check** walks the body once and rejects a collective unless every `if` condition and `for` range that encloses it is uniform. A uniform `for t in 0 .. steps` makes its loop variable uniform. A `while` that holds a collective is rejected in v0: its condition would have to be uniform and change, and nothing uniform can be assigned yet. `?` is not allowed in a body with collectives, since one iteration could leave while the others wait. If every enclosing condition is uniform, every iteration takes the same branches around collectives, so every iteration issues the same sequence: the check is a type-level fact, decided syntactically, with no goal and no second copy of the body. A body-local `let` is uniform when its value is and it is never assigned.

The error names the condition, for example: *every iteration must reach this all_reduce in the same order, but it is reached only when the condition 'b = 0' at 12:5 holds, and that depends on the iteration*.

This is ADR 0014's protocol check. Its model-checker pass, for protocols this check cannot settle, comes with ADR 0053's checker.

### 3. What each iteration knows

The verifier still sees one arbitrary iteration of the body, as in ADR 0060, and every collective is a barrier in it:

- At a collective, and on entering and leaving an `if` or `for` that contains one, every cell that another iteration owns of every buffer the spread writes is forgotten (ADR 0060's havoc), since the others may have written it.
- `all_reduce`'s result is an unknown value of its type with what one contribution says about it: `add` over unsigned values is at least `e`, `min` is at most `e`, `max` is at least `e`, `or` holds if `e` does, and `e` holds if `and` does.
- After `halo_exchange b`, reads of `b` need no ownership goal and writes of `b` are rejected, until the next collective; a compound statement that contains a collective ends the window.

ADR 0060's other rules stand: the body writes only cells it owns, and assigns no variable declared outside it.

### 4. A spread with collectives runs as phases

Codegen splits the body at its collectives. The code between two collectives becomes its own `scf.parallel` over the range, run on the MLIR async runtime exactly as a spread without collectives (ADR 0060, section 2), and the join at its end is the barrier. An `if` or `for` that contains a collective is lifted out of the parallel loops, which is legal because its condition and bounds are uniform: codegen computes them once, as the iteration at `lo` would. An `all_reduce` adds each iteration's contribution to one cell with an atomic read-modify-write, at the end of the phase before it, and the next phase reads the result.

So that phases can be separate loops, a value computed in one phase and used in a later one must be uniform, and then codegen computes it again where it is used; a per-iteration value that crosses a collective is rejected with a hint to keep it in a cell the iteration owns. The loop variable crosses freely.

Integer `all_reduce` is exact whatever the order of the atomics, so its result is deterministic. Float reductions, when they come, need a fixed order, which per-phase partial results in iteration order would give.

### Alternatives

- **Worker threads and barriers.** One thread per iteration and a barrier runtime over pthreads: what the design's word "worker" suggests, and the only way to run a collective inside a non-uniform loop. But it is a new trusted runtime, codegen would have to outline and pack the body, and the range would have to be no larger than the threads available. Phases need neither, and every program the protocol check accepts can be split.
- **Comparing two iterations in Z3** for matching collectives: general, but the body twice, as ADR 0060 rejected for ownership.
- **Collectives outside the spread**, `all_reduce add (map f grid)` in the global view: no matching to check, but nothing for iterations to agree on between steps, so a multi-step stencil is a spread per step, as today.
- **`scf.parallel` reductions** instead of atomics: MLIR's async lowering does not take them, so the loop would run on one core.

## Consequences

- A spread can loop over time steps with a `halo_exchange` and an `all_reduce` in each, and the compiler proves that every iteration reaches them in the same order.
- A mismatched collective, under a condition on the loop variable, is a compile error at the collective, naming the condition.
- No new runtime: phases run on the async runtime ADR 0060 already trusts.
- A phase is a fork and a join, so a spread with a collective in a loop of `k` steps costs `k` fork-joins, as `k` spreads would; collectives make such code shorter and proved, not faster, until `Pia.Task` (ADR 0027) gives persistent workers.
- `all_reduce` contends on one cell, so it suits a spread over workers, tiles or basins better than one over cells.
- Tiled grids with halo rows (`pia_par.tiled`) are still to come; `halo_exchange` works on the buffers a spread writes today.

## Steps

1. IRGen: `all_reduce` and `halo_exchange`, the protocol check, the window, and the goals and facts of section 3. Codegen: phases. Tests in `tests/verify/collectives.pia`, `tests/irgen/collective_errors.pia` and `tests/codegen/collectives.pia`.
2. `sediment_step` with a `halo_exchange` and an `all_reduce` on CPU threads, in the docs.
3. Partial results per phase for float reductions, with floats (M11).
