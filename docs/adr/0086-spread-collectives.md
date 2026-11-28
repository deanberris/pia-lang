# 86. Collectives in a `spread`: `@collective` library functions over every iteration's contribution, proved to match, run as phases

Date: 2026-11-28

Status: Proposed

## Context

M12 ([#13](https://github.com/deanberris/pia-lang/issues/13)) is done when `sediment_step` runs on CPU threads and a mismatched collective is rejected at compile time. `spread` v0 ([ADR 0060](0060-spread-v0-ownership-and-runtime.md)) has the loop, the ownership rule and the runtime, and 0.1.0 needs collectives on the CPU ([ADR 0080](0080-release-0-1-0-gates.md), section 3).

[ADR 0014](0014-concurrency-model.md) says what a collective is: every worker takes part, and the program is correct only if every worker reaches the same collectives in the same order, which is checked at compile time. [design.md](../design.md) sketches `sediment_step` with a `halo_exchange` before the stencil and an `all_reduce add` of the outflow after it.

The compiler knows no function names: an extension is a Pia function with a body that proves, and `@lower` where it needs another form ([#487](https://github.com/deanberris/pia-lang/issues/487), [ADR 0065](0065-lowerings-written-in-pia.md)). A first draft of this ADR made `all_reduce` and `halo_exchange` names the compiler knew, on the grounds that a collective has no body one iteration could run alone. Dean rejected that (2026-11-28): a reduction does have a body, once it can see what every iteration contributes. So the compiler gets the context, and the library gets the collectives.

Four things are open:

1. **What the compiler gives a library function**, so that it can be a collective.
2. **What a worker is.** A `spread` iteration is one, so a collective is a call in a spread body that every iteration of the range joins.
3. **How "the same collectives in the same order" is proved.** Two iterations would have to be compared, which ADR 0060 avoided for ownership, and for the same reason: the body would be encoded twice.
4. **How it runs.** The MLIR async runtime splits a spread's range into blocks and runs a block's iterations one after the other on one thread, so an iteration that waits at a barrier for the next iteration of its own block waits forever.

## Decision

### 1. `@collective`: a function every iteration calls once, over every iteration's contribution

**Index types** (Dean, 2026-11-28). `range` is the type of a spread's positions: a record of two `usize` bounds, `lo <= hi`, whose positions are `lo <= i < hi`. A spread's loop variable is a position of its range, of type `index r` for the range `r` it runs over. `[t; r]`, for a parameter `(r : range)`, is an array indexed by the positions of `r`: it has `r.hi - r.lo` elements, and `xs.[k]` is the element at position `k`, so a goal says `r.lo <= k` and the bounds goal that `k < r.hi`. In this ADR, ranges and the arrays over them are for collectives: a function that takes a `range` must be a `@collective`, and a gathered parameter must be an array over one. Written `index r` types, `for` loops over a range and tiles over a grid are a later ADR.

`@collective` after a function's return type makes it a collective. `@collective(xs)` names its **gathered** parameters, each an array `[t; r]` over a range parameter:

```ocaml
let sum (r : range) (xs : [u32; r]) : u64
  @collective(xs)
  requires len xs <= 4'294'967'297
  ensures forall (k in r.lo .. r.hi). result >= xs.[k]
= ... (* an ordinary proved loop that adds xs up *)
```

- **At a call** in a spread body, an iteration passes a `t` for each gathered parameter, as in `sum x`, and nothing for a range parameter: the call passes the spread's own range there. The function is called once for the whole spread: its gathered parameter holds every iteration's argument, iteration `i`'s at position `i`, and every iteration gets the one result. This is the introspection the compiler gives a library: the spread's range, as a value, and what each iteration contributed, as an array over it.
- **How the argument binds.** At the call, the verifier knows that the array has a cell for each position of the range and that the iteration's own argument is at its position. In the collective, the same two facts are what `[t; r]` says. They are how an argument binds to a gathered parameter, as a plain argument binds to its parameter, so neither is trusted.
- **Every other parameter** is passed as written, and must be the same in every iteration (uniform, section 3), since there is one call.
- **The body is the meaning.** It is proved against the contract like any function's, and codegen runs it (section 5), so a collective adds nothing to the trust report. A `@lower` on it is an ordinary lowering ([ADR 0065](0065-lowerings-written-in-pia.md)): an atomic form that skips the gathered buffer, trusted as every lowering is until ADR 0065 proves them.
- **`@collective` with no names** is a collective with nothing gathered: a barrier. A buffer the spread writes, passed to it as a `borrowed` (read-only) argument, is **published**: until the next collective, every iteration may read every cell of it, and none may write it. In shared memory there is nothing to copy.
- A collective takes no `out` or `inout` parameter, and is called only in a spread body itself, not in a function it calls, a lambda, a `match`, or a handler, which v0 rejects. Outside a spread it is an error.

### 2. `Pia.Par`: the collectives, in Pia

`lib/Pia/Par.pia` defines the standard collectives as `@collective` functions, with no `@lower` in v0:

| Function | Gathers | Result | What the contract says |
| --- | --- | --- | --- |
| `sum` | an unsigned integer of 32 bits or less | `u64` | at least each contribution; `len xs <= 2^32 + 1` |
| `sum` | a signed integer of 32 bits or less | `i64` | `len xs <= 2^32`, which keeps the sum in `i64` |
| `least`, `most` | an integer | the same type | at most, or at least, each contribution, and equal to one |
| `any`, `every` | `bool` | `bool` | some, or every, contribution holds |
| `exchange` | nothing; takes `b : borrowed [t]` | `unit` | `b` is published |

The signed and unsigned `sum` are generic over the integer type, told apart by `where` constraints ([ADR 0035](0035-substitution-failure-and-total-constraints.md)). Each is exported with its definition, as generics are, so an importer instantiates it in its own module.

The design's spelling is a metaprogram over them that importers run: `all_reduce add x` is `sum x`, `min` is `least`, `max` is `most`, `or` is `any` and `and` is `every`; `halo_exchange b` is `exchange b`. Any other operator is an error from the metaprogram.

### 3. Collectives match because the control flow that reaches them is uniform

A value is **uniform** when it is the same in every iteration: a name bound before the spread, a constant, the result of a collective, a cell of a buffer the spread does not write at a uniform index, and anything computed from uniform values alone. The loop variable is not uniform, and neither is a cell of a buffer the spread writes.

The **protocol check** walks the body once and rejects a call of a `@collective` function unless every `if` condition and `for` range that encloses it is uniform, as is every argument it does not gather. A uniform `for t in 0 .. steps` makes its loop variable uniform. A `while` that holds a collective is rejected in v0: its condition would have to be uniform and change, and nothing uniform can be assigned yet. `?` is not allowed in a body with collectives, since one iteration could leave while the others wait. If every enclosing condition is uniform, every iteration takes the same branches around collectives, so every iteration issues the same sequence: the check is a type-level fact, decided syntactically, with no goal and no second copy of the body. A body-local `let` is uniform when its value is and it is never assigned.

The error names the condition, for example: *every iteration must reach this call of the collective 'sum' in the same order, but it is reached only when the condition at 12:5 holds, and that depends on the iteration*.

The check is keyed on the attribute, so the compiler knows no collective by name. This is ADR 0014's protocol check. Its model-checker pass, for protocols this check cannot settle, comes with [ADR 0053](0053-protocols-checked-with-spacer.md)'s checker.

### 4. What each iteration knows

The verifier still sees one arbitrary iteration of the body, as in ADR 0060, and every collective is a barrier in it:

- At a collective, and on entering and leaving an `if` or `for` that contains one, every cell that another iteration owns of every buffer the spread writes is forgotten (ADR 0060's havoc), since the others may have written it.
- At a call, each gathered argument is a fresh array over the spread's range, a spec buffer ([ADR 0058](0058-spec-buffers.md)), of which the iteration knows one cell: its own argument, at its position `i`. The precondition is a goal over it, so `sum`'s `len xs <= 2^32 + 1` is a goal on the spread's range. The result is fresh, the postcondition is assumed of it, and so `sum x >= x` follows from `sum`'s contract.
- After a call that publishes `b`, reads of `b` need no ownership goal and writes of `b` are rejected, until the next collective; a compound statement that contains a collective ends the window.

ADR 0060's other rules stand: the body writes only cells it owns, and assigns no variable declared outside it.

### 5. A spread with collectives runs as phases

Codegen splits the body at its collectives. The code between two collectives becomes its own `scf.parallel` over the range, run on the MLIR async runtime exactly as a spread without collectives (ADR 0060, section 2), and the join at its end is the barrier. An `if` or `for` that contains a collective is lifted out of the parallel loops, which is legal because its condition and bounds are uniform: codegen computes them once, as the iteration at `lo` would.

A collective with gathered parameters gets a buffer of `hi - lo` cells for each, allocated on the heap where the spread starts and freed where it ends. In the phase before the call, each iteration stores its argument in its cell. Between the two phases the function is called once, on the buffers, and the next phase reads its result. Its body is ordinary Pia, so the order it combines in is the body's: a float sum, when floats come, is the same every run.

So that phases can be separate loops, a value computed in one phase and used in a later one must be uniform, and then codegen computes it again where it is used; a per-iteration value that crosses a collective is rejected with a hint to keep it in a cell the iteration owns. The loop variable crosses freely.

### Alternatives

- **Collective names in the compiler** (this ADR's first draft): `all_reduce` and `halo_exchange` known to IRGen, each reduction an atomic on one cell. No buffer, but a builtin per collective, and a new collective is a compiler change.
- **Gathered slices without index types**: `xs : [t]`, with the iteration's argument at `xs.[i - lo]` and `len xs` the count. It needs no new type, but the offset would be the compiler's rule rather than the type's, and nothing would carry over to tiles.
- **A trusted contract**: the library function's body is what one iteration would return alone, and its contract states the whole result, trusted. It has no buffer, but a reduction would be on the trust report for a fact its body can prove once it sees the contributions.
- **Worker threads and barriers.** One thread per iteration and a barrier runtime over pthreads: what the design's word "worker" suggests, and the only way to run a collective inside a non-uniform loop. But it is a new trusted runtime, codegen would have to outline and pack the body, and the range would have to be no larger than the threads available. Phases need neither, and every program the protocol check accepts can be split.
- **Comparing two iterations in Z3** for matching collectives: general, but the body twice, as ADR 0060 rejected for ownership.
- **Collectives outside the spread**, `sum (map f grid)` in the global view: no matching to check, but nothing for iterations to agree on between steps, so a multi-step stencil is a spread per step, as today.

## Consequences

- A collective is a Pia function, proved like any other. The compiler knows only `range`, arrays over a range and `@collective`: the gathered array, the protocol check, the barrier and the phases.
- A spread can loop over time steps with an `exchange` and a `sum` in each, and the compiler proves that every iteration reaches them in the same order.
- A mismatched collective, under a condition on the loop variable, is a compile error at the call, naming the condition.
- No new runtime: phases run on the async runtime ADR 0060 already trusts.
- A gathered parameter costs a buffer of the spread's count, and the call runs on one thread. That suits a spread over workers, tiles or basins; over millions of cells, an atomic `@lower` will be the fast path.
- A phase is a fork and a join, so a spread with a collective in a loop of `k` steps costs `k` fork-joins, as `k` spreads would; collectives make such code shorter and proved, not faster, until `Pia.Task` (ADR 0027) gives persistent workers.
- Tiled grids with halo rows (`pia_par.tiled`) are still to come; `exchange` works on the buffers a spread writes today.

## Steps

1. `range` and arrays over a range, `@collective`, gathered parameters, the protocol check, publishing, and the goals and facts of section 4 in IRGen and the verifier; phases and gathered buffers in codegen; `Pia.Par`. Tests in `tests/verify/collectives.pia`, `tests/irgen/collective_errors.pia`, `tests/codegen/collectives.pia` and `tests/std/par.pia`.
2. `sediment_step` with an `exchange` and a `sum` on CPU threads, in the docs.
3. An atomic `@lower` for `sum`, `least`, `most`, `any` and `every`, and float sums with floats (M11).
