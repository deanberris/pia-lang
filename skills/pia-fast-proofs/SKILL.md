---
name: pia-fast-proofs
description: Prove only the part of a Pia program you changed, quickly, with `piac --verify-only`, `--proof-cache`, `--jobs` and `--verify-stats`, and decide whether slicing helps. Use when a full `piac --verify` is slow, when iterating on one function in a large file, or when checking proof build-time cost.
---

# Proving a subset fast

Proof time is a tracked benchmark in Pia (ADR 0032, [docs/verifier.md](../../docs/verifier.md#parallel-sliced-and-cached-proving)). Goals are encoded on one thread, then solved in parallel, one Z3 context per thread, and the result of every goal is the same on any number of threads. Use these levers in this order.

## 1. Select only the goals you are working on

`--verify-only=<spec>` proves only the selected goals. It repeats, and implies `--verify`:

```sh
piac --verify-only=settle streams.pia.md          # one function
piac --verify-only=edges.pia:41 edges.pia         # the goals on one line
piac --verify-only=streams.pia.md streams.pia.md  # one file (module)
```

A function's name selects all its overloads; `'sqrt(f64)'`, quoted for the shell, selects one. Earlier goals are still *assumed*, as in a full run, so a selected goal is proved exactly as it would be in the whole file. Unselected goals are left out of the report. A selective run never generates code: always finish with a full `--verify` (or a build) before you call the work done.

<!-- example: two.pia -->
```ocaml
let clamp (lo : i32) (hi : i32) (x : i32) : i32
  requires lo <= hi
  ensures lo <= result && result <= hi
= if x < lo then lo else if x > hi then hi else x

let halve (x : u32) : u32
  ensures result <= x
= x / 2
```

```console
$ piac --verify-only=halve two.pia
two.pia:8:5: proved: the divisor is not zero [intervals]
two.pia:8:5: proved: '/' does not overflow u32 [intervals]
two.pia:7:3: proved: the postcondition holds [smt]
3 proved, 0 failed, 0 skipped
```

## 2. Cache proved goals

`--proof-cache=<dir>` keeps one file per proved goal, keyed by the SHA-256 of the Z3 version, the rlimit and the query. An unchanged query is not solved again. Since calls are encoded from contracts, editing a callee's *body* leaves its callers' queries, and so their cache entries, unchanged; editing its *contract* invalidates them. Failures are never cached, so a cached run can never hide a failure. If an advisory revokes your Z3 ([docs/advisories.md](../../docs/advisories.md)), piac warns and skips the cache: upgrade piac.

A second run of an unchanged file answers from the cache (here on a two-function file):

```text
verify-stats: goals=4 unselected=0 intervals=2 skipped=0 solved=0 cached=2 sliced=0 unsliced=0 threads=2 cost=0 encode_ms=2 solve_ms=4
```

The report itself is the same as a full run, and a cached goal still prints its original method (`[smt]`). Check `cached=` in the statistics to see the cache working.

Use one cache directory per checkout (outside the source tree or in `.gitignore`), and keep it across runs:

```sh
piac --verify --proof-cache="$HOME/.cache/pia-proofs" f.pia
```

## 3. Measure

`--verify-stats` prints one line to stderr:

```text
verify-stats: goals=243 unselected=0 intervals=21 skipped=0 solved=222 cached=0 sliced=0 unsliced=0 threads=1 cost=269094119 encode_ms=947 solve_ms=30213
```

| Field | Meaning |
| --- | --- |
| `goals`, `unselected` | goals in the file, and those `--verify-only` left out |
| `intervals` | settled by range analysis, without Z3 |
| `solved`, `cached` | sent to Z3, and answered by the proof cache |
| `sliced`, `unsliced` | queries slicing made smaller, and slices solved again in full |
| `threads` | solver threads used |
| `intblast` | nonlinear goals proved by Z3's int-blasting solver (ADR 0066) |
| `cost` | Z3's deterministic resource count over every query: the number to compare between runs |
| `encode_ms`, `solve_ms` | wall time; depends on the machine |

Compare `cost`, not milliseconds, when you judge a change to a proof: it does not depend on load, and varies by only about 1% run to run. `python3 tools/bench/proof_bench.py --piac bazel-bin/tools/piac/piac --baseline tools/bench/baseline.json --out bench.json` runs the whole corpus, and CI fails when the cost of any corpus file grows by more than 10%. When a change makes a file legitimately costlier, such as new goals, record its new cost in the same pull request: `python3 tools/bench/proof_bench.py --piac bazel-bin/tools/piac/piac --passes=parallel --only=lib/Pia/Core/Charconv.pia --write-baseline` updates just that file's entry (cost does not depend on the machine, so the iMac or a cloud session's prebuilt `piac` will do), or `--write-baseline --merge=bench-1.json --merge=bench-2.json --merge=bench-3.json` takes every file from CI's `proof-bench-linux-*` artifacts.

## 4. Threads

Proving uses one thread per core by default. `--jobs=N` sets it. Lower it only when the machine is shared; results do not change with it, only wall time.

## 5. Slicing: usually leave it alone

Slicing cuts a query down to the goal's cone of influence. It is automatic, and only applied in functions with a buffer of records (one buffer per field), where it can cut cost by orders of magnitude. Elsewhere it usually costs *more*: forcing it on the streams demo raised cost by about 47%.

- `--slice` slices every goal whose slice is smaller. Try it, and keep it only if `cost` falls.
- `--no-slice` always solves the full query, which is the way to check that slicing is not the cause of a surprise.

Slicing never makes a goal fail that would otherwise prove, and a counterexample always comes from the full query.

## 6. Products: int-blasting is automatic

A goal that multiplies two values that are not constants, or divides by one, is first given to Z3's int-blasting solver, which decides it as integer arithmetic instead of building a 68- or 132-bit multiplier ([ADR 0066](../../docs/adr/0066-int-blasting-for-nonlinear-goals.md)). Goals like `a <= b ==> a * c <= b * c` prove in about a second with no lemma and no `@solver` annotation. `intblast=` in `--verify-stats` counts them. If int-blasting cannot prove a goal, the bit-blaster runs as before and gives any counterexample.

- `--no-int-blast` turns the attempt off: use it to compare `cost`, or to rule int-blasting out when a goal surprises you.

## In the REPL

Each cell re-verifies the whole environment, so keep sessions small: `:reset` between unrelated investigations, and `:load` only the files you need. `--timeout-ms=N` sets the solver's limit per obligation. When a session's subject is settled, move it to a file and use the flags above.

## Checklist

1. `--verify-only=<the function you changed>` while iterating.
2. `--proof-cache=<dir>` on every run.
3. `--verify-stats` when something feels slow, and compare `cost`.
4. A full `piac --verify` (no `--verify-only`) before you finish.
