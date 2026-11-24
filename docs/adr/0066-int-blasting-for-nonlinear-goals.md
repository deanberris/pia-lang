# 66. Nonlinear goals are tried first with Z3's int-blasting solver, and other solvers are kept out of the pipeline for now

Date: 2026-11-25

Status: Accepted (Dean, 2026-11-25, with the answers below)

## Context

The verifier encodes Pia's integers as signed bit-vectors, wide enough that no term wraps: 68 bits, or 132 bits when a product needs it (`encodingWidth` in `src/verify/Verifier.cpp`). Z3 bit-blasts those queries. Bit-blasting is exact, and fast for sums, comparisons and bitwise operations. A 68- or 132-bit multiplier or divider, though, becomes a large circuit, and Z3's SAT search on it is what times out on goals such as `a <= b ==> a * c <= b * c`. Several pieces of work have run into this:

- **#45, the raster index.** `(y * w + x) * c + k < w * h * c` times out. `Pia.Image.Raster` works around it with a lemma `mul_mono`, proved by induction under `@solver(tactic = "(using-params smt :bv.solver 2)")`, which is Z3's int-blasting solver chosen by hand. The GIF encoder uses the same annotation on `put_blocks`, `frames_bound` and `blocks_fit`.
- **#306, the to_chars round trip.** One step of `v = q * b^k + dval(...)` times out at 60 s.
- **Pia.Core.Rand** is parked on a u64 division goal, and `Pia.Core.Int`'s `gcd` has a weak contract because divisibility is nonlinear.
- **`divisionLemma`** in the verifier states the facts of division beside each `/` and `%`, because Z3 cannot bit-blast `(a / b) * b + a % b = a` at 32 bits within its timeout.

Dean asked (2026-11-24) whether Z3 extensions or other solvers already handle nonlinear goals better. [ADR 0061](0061-lean-proved-facts.md) covers general laws that need induction, in Lean. This ADR covers *concrete* goals: products and quotients of bounded integers, which are decidable and should be proved automatically.

### Measurements

Two sets of goals were benchmarked in the cloud (4 x86_64 cores, 30 s per query, one solver per query, 4 at a time).

**Hand-written goals.** These are 15 of the hard goals above, written in the verifier's encoding: signed bit-vectors at Pia's width, each type's range asserted, and the claim negated. 13 are true and 2 have counterexamples. Each was written four ways: at Pia's width (68 or 132), at the narrowest exact width, as integers (`QF_NIA`), and as reals (`QF_NRA`, for goals without division). Z3 is 4.15.1 (piac pins 4.15.2).

| Solver, on Pia's bit-vectors | True goals proved | Counterexamples found | Slowest |
| --- | --- | --- | --- |
| Z3 as piac calls it today (bit-blasting) | 2 of 13 | 2 of 2 | timeouts |
| Z3, `smt` tactic with `smt.bv.solver=2` (int-blasting) | **13 of 13** | 2 of 2 | 1.1 s |
| cvc5 1.4.2, `--solve-bv-as-int=sum` (int-blasting) | 13 of 13 | 2 of 2 | 1.2 s |
| cvc5 1.4.2, default (bit-blasting) | 2 of 13 | 2 of 2 | timeouts |
| Bitwuzla 0.11 | 3 of 13 | 2 of 2 | timeouts |
| Yices 2.6.5 | 2 of 13 | 2 of 2 | timeouts |

On the same goals written as integers, Z3's default nonlinear integer arithmetic proves all 13 (slowest 1.5 s), Yices's MCSat proves 11 and gives up on 2 (slowest 0.03 s), and cvc5 proves all 13. The narrowest exact width does not help the bit-blasters: a 66-bit multiplier is as hard as a 68-bit one. The real relaxation, which Z3 decides with `nlsat`, is fast, but it fails on every goal with a strict `<` between integers (`x < w` admits `x = w - 0.5`), so it adds nothing to integer int-blasting.

**Real queries.** `piac --dump-smt` on `lib/Pia/Core/Int.pia` gives 473 SMT queries (on the iMac, main at 436306d).

| Solver | Proved | Total time | Slowest |
| --- | --- | --- | --- |
| Z3, bit-blasting (the full query) | 473 | 144.8 s | 13.7 s |
| Z3, int-blasting on every query | 473 | 34.6 s | 20.0 s |
| Z3, int-blasting on the 267 nonlinear queries, bit-blasting the rest | 473 | 15.8 s | 1.0 s |
| cvc5, int-blasting on every query | 473 | 38.5 s | 0.4 s |

The slowest int-blasted query is linear, a chain of `bvashr` that is cheap to bit-blast and costly to state as integers, so int-blasting is for nonlinear goals only. On the nonlinear queries Z3 bit-blasting took 135.8 s and Z3 int-blasting 6.8 s. In piac's own resource count, routing the nonlinear goals to int-blasting would take the file from 22.6M to 15.1M. piac's count is lower than the plain bit-blasting run above, because piac first tries each division with multiplication and division uninterpreted (`abstractArithmetic`). The costliest goal, `Int.pia:369`, falls from 5.3M to 12k.

The Z3 version matters too. Z3 5.4.1 bit-blasts the same 473 queries in 46.9 s, three times faster than 4.15.1, but its int-blasting is slower on the linear ones (170.2 s on every query). Routed as above, 5.4.1 takes 18.0 s. Upgrading Z3 is a separate step, measured by the benchmark on its own.

No solver disagreed with another on any query: none proved a goal that another refuted.

### The options

1. **Encode bit-vectors as integers in the Encoder (`QF_NIA`).** This is exact while no term wraps, which `encodingWidth` already guarantees for arithmetic. But Pia's goals mix arithmetic with `bvand`, shifts, rotations and popcounts, which have no cheap integer form. It is a rewrite of the Encoder, and the counterexample printer, for what Z3's int-blasting already does inside the solver.
2. **Z3's int-blasting (`smt.bv.solver=2`).** Z3 translates the bit-vector query to integers inside the solver, with bitwise operations axiomatised lazily. It needs no new dependency, it is deterministic (the same rlimit count on every run), and it is selectable per solver from the C++ API: `z3::tactic(ctx, "smt").mk_solver()` with the parameter `smt.bv.solver = 2`. No global parameter is needed, so other goals' solvers are untouched. The `smt` tactic is needed, because the default solver for a bit-vector query runs the bit-blasting tactic before the SMT core sees it.
3. **nlsat over a real relaxation.** It is complete for real arithmetic, but it is weaker than integers wherever integrality matters, as above.
4. **A portfolio with cvc5 and Yices2.** cvc5's int-blasting matched Z3's on every goal and was steadier on the real queries (slowest 0.4 s). But cvc5 is a second solver to build with Bazel, with GMP (LGPL) under it, and a second SMT-LIB dialect to keep in step with the `smt` dialect's export. **Yices2 is GPLv3, so it cannot be linked into piac without making piac GPL.** It could only run as a separate process that the user installs. Bitwuzla (MIT) is a bit-blaster, and it fails on the same goals as Z3's.
5. **A user propagator for interval multiplication.** It is not needed while int-blasting decides the same goals, and a propagator is code inside the trusted base.

## Decision

1. **A nonlinear goal is tried first with Z3's int-blasting solver.** A goal is nonlinear when its query has a `bvmul` of two terms neither of which is a literal, or a `bvsdiv` or `bvsrem` by a term that is not a literal (`multipliesVariables`). After the abstract attempt (division and multiplication uninterpreted), `solve` gives such a goal to `z3::tactic(ctx, "smt").mk_solver()` with `smt.bv.solver = 2`, in a context of its own, with a budget of 50M rlimit (`kIntBlastRlimit`), or the goal's rlimit if that is smaller. The translation is exact both ways, so unsat is a proof. On sat or unknown, the bit-blaster decides the goal as before, and gives the counterexample.
2. **What stays as it is.** A goal with a `@solver` strategy of its own, with theory axioms, or with assumptions keeps today's path, since its strategy, or the unsat core of its solver, is the point. Linear goals keep the bit-blaster.
3. **Reported.** A goal proved this way is reported as `[smt]`, as before, and `--verify-stats` counts these goals as `intblast=`. `--no-int-blast` turns the attempt off, for comparison and as an escape hatch. The proof cache is keyed by the query, so its entries are unchanged.
4. **No second solver for now.** cvc5 is the fallback to revisit if Z3's int-blasting stops being enough: it is BSD-licensed and was as good on every goal measured, but it means building GMP. Yices2 is not bundled, because of its licence. Bitwuzla and the real relaxation are not used.

## Consequences

- The `@solver(tactic = "(using-params smt :bv.solver 2)")` annotations in `Pia.Image.Raster`, `Gif.LzwEncode` and `Gif.Encode` become unnecessary, and so may lemmas such as `mul_mono` that exist only to get around #45. Removing them is a follow-up, done one module at a time with the benchmark.
- Parked work can be retried: the to_chars round trip (#306), `Pia.Core.Rand`, `gcd`'s divisibility contract, and the exact sums of `Pia.Core.Algo.Numeric`.
- A nonlinear goal that int-blasting cannot prove pays for both attempts. The budget bounds the extra cost, and the benchmark (`tools/bench/proof_bench.py`) shows whether it ever matters. The baseline is regenerated in the PR that turns the attempt on.
- **Risk: #371.** Z3 hit an assertion violation (`ast.cpp:388`) with `bv.solver 2` on the whole of `Gif.Encode.encode_animation`. Int-blasting is now automatic, so every nonlinear goal of that function takes this path. The PR that turns it on must verify the GIF modules. If the crash recurs, nonlinear goals in a function with records go back to bit-blasting until it is fixed upstream, and #371's last item becomes more pressing: piac should turn a solver crash into a goal failure.
- The measurements and the scripts that produced them are in the PR. The hard nonlinear goals are a lit test, `tests/verify/int_blast.pia`.

## Dean's answers (2026-11-25)

1. **Int-blasting is on by default.** `--no-int-blast` stays, for comparison.
2. **cvc5 is deferred.** It is not built now, and is revisited only if Z3's int-blasting stops being enough.
3. **Nothing GPL, ever.** Pia does not bundle, link, call or script any GPL-licensed tool, so Yices2 is out entirely, in the pipeline and in the benchmark scripts.
