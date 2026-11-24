# 62. Cost bounds are contracts: `costs e` bounds a function's steps, counted by a spec-only `spent` and proved by Z3

Date: 2026-11-24

Status: Proposed

## Context

Pia proves what a function computes, but not how much work it does. [ADR 0040](0040-cpp23-standard-library-in-pia.md) documents C++'s complexity clauses ("at most `log2(n) + 1` comparisons") and does not prove them. [ADR 0056](0056-tests-generated-from-contracts-and-theories.md) checks them by fitting benchmark counts, which tests a few sizes, not every size. [ADR 0061](0061-lean-proved-facts.md) puts asymptotic claims (`O(n log n)`) and closed forms of recurrences in Lean, but they need an exact bound to be about, and that bound has to be proved of the code.

Dean decided, when he accepted ADR 0061, that cost proofs by Z3 come first, in their own ADR, since they need no Lean.

Most complexity clauses are exact upper bounds on a count: comparisons, swaps, loop iterations, calls. A count is an integer that the code increases. If the verifier tracks it like any other value, then a bound on it is an ordinary postcondition, and Z3 proves it with the loop invariants and lemmas Pia already has. This is the approach of time credits (Charguéraud and Pottier, in Coq with CFML), of Liquid Haskell's resource analysis (Handley, Vazou and Hutton, "Liquidate your assets"), and of calf (Niu, Sterling, Grodin and Harper). RAML (Hoffmann) infers polynomial bounds automatically by linear programming. Pia starts with stated bounds, which are checked, and leaves inference for later.

## Decision

### 1. `costs e` bounds a function's cost

A function may state its cost after its other contracts:

```ocaml
let find (xs : [u32]) (v : u32) : usize
  ensures result <= len xs
  costs len xs
= ...
```

`costs e` means that every run of the function, from any state meeting its `requires`, costs at most `e`. `e` is a spec expression of type `int` (unbounded, so a bound never overflows) over the parameters and their `old` values. It is an upper bound only. Lower bounds and exact counts are out of scope.

Only upper bounds are in scope, because they are what callers need: a caller that knows each callee's bound can add them up. `costs` is a keyword only in contract position, like `requires` and `ensures`.

### 2. The cost model: steps by default, or calls to one function

**Steps (the default).** One unit for each loop iteration, and for each call that is not to a spec function or lemma. A call costs one unit plus the callee's bound: its `costs` clause, with the arguments substituted. A callee without `costs` has a bound only when the compiler can work one out: a function with no loops and no recursion costs the number of calls on its longest path, plus their bounds, which is a constant. Calling any other function without `costs` from a function with `costs` is an error that names the callee: "`sort` has no cost bound, so the cost of `top_k` cannot be proved; add `costs` to `sort`."

**Calls to one function, `@counts(f)`.** Only calls to `f` count, one unit each. `f` is a function, a function parameter, or a concept requirement such as `Ord`'s `less`. This is how C++ states its clauses, in comparisons or swaps. Under `@counts(f)`, a callee contributes its own bound if it is also `@counts(f)` for the same `f` (passed through as an argument), and nothing if `f` cannot be reached from it: the callee is not `f`, does not take `f` as an argument and has no concept that provides it. The type checker decides both from the callee's signature. Any other callee is an error, as for steps.

A cost model counts steps, not time. A step count says nothing about caches or vector width, so performance budgets stay benchmarks (ADR 0056). What a cost bound proves is the shape that a benchmark measures: how the work grows with the input.

### 3. `spent` counts the cost so far

Inside a function with `costs`, the spec-only value `spent` is the cost so far, under the function's model. It is `0` on entry. Each counted event adds to it: one for a loop iteration, and one plus the callee's bound for a call. At each return, `spent <= e` is a goal, with `e` evaluated at the parameters' entry values.

`spent` is a loop-carried value like any other, so loops bound it with an invariant, and the loop machinery that exists today ([verifier.md](../verifier.md#loops)) does the rest. Binary search, counting calls to `less`:

```ocaml
let lower_bound (xs : [t]) (v : t) : usize @counts(less)
  requires sorted xs
  costs Pia.Math.Log.bits (len xs)
= let lo : mutable usize = 0 in
  let hi : mutable usize = len xs in
  while lo < hi
    invariant lo <= hi && hi <= len xs
    invariant spent + Pia.Math.Log.bits (hi - lo) <= Pia.Math.Log.bits (len xs)
  do
    let mid = lo + (hi - lo) / 2 in
    if less xs.[mid] v then lo <- mid + 1 else hi <- mid
  done;
  lo
```

`bits m` is the number of binary digits of `m`, which is `floor (log2 m) + 1` for `m >= 1`: exactly C++'s "at most `log2(n) + 1` comparisons". Each iteration costs one `less` and leaves a range of at most `(hi - lo) / 2`, and `bits` drops by one when its argument is halved. That fact is a lemma of `Pia.Math.Log`, so the invariant's goal is linear.

`spent` can appear in loop invariants, `assert`s and lemma calls. It cannot appear in code, in `requires` or in `ensures`, and codegen erases it like any spec value. Encoded, it is a spec `int` local, which IRGen threads through loops, branches and error handlers like a mutable local ([ADR 0028](0028-error-propagation-and-cleanup.md)'s `?` returns are returns, so each has the goal).

### 4. Recursion

A recursive function with `costs` must have `decreases`. At a recursive call, the call's bound is the function's own `costs` at the call's arguments, as its `ensures` is assumed there. That is sound by induction on the measure, which is why the measure is required. Its cost is then a recurrence, which is often best written as a recursive spec function:

```ocaml
let spec merge_cost (n : int) : int
  requires n >= 0
  decreases n
= if n <= 1 then 0 else merge_cost (n / 2) + merge_cost (n - n / 2) + n

let merge_sort (xs : inout [t]) (scratch : out [t]) : unit @counts(less)
  requires len scratch = len xs
  ensures sorted xs && permutation xs (old xs)
  costs merge_cost (len xs)
  decreases len xs
= ...
```

Z3 proves that the code follows the recurrence, one call at a time. It cannot solve the recurrence. A closed form such as `merge_cost n <= n * bits n` needs induction beyond one step, and an asymptotic claim such as `merge_cost in O(fun n => n * log2 n)` is a limit. Both are lemmas for Lean, by [ADR 0061](0061-lean-proved-facts.md). Until then, a closed form that a recursive lemma can prove in Pia is proved there, and callers use it.

### 5. Amortised bounds

An operation that is cheap on average, such as `vec`'s `push` or a union–find `union`, states its bound with a potential: a spec function of the structure's model ([docs/stdlib.md](../stdlib.md), ghost models), such as `costs 1 + phi (old v) - phi v`. It is an ordinary `costs` expression, using `old`, so nothing new is needed to prove it. A sequence of `k` pushes then costs at most `k + phi (first) - phi (last)`, which is linear, because the potential is never negative (a lemma about `phi`). This is the banker's method of time credits, written as a contract.

### 6. `Pia.Math.Log`

A small spec-only module of the functions cost bounds use, with their laws as lemmas proved in Pia:

- `bits (m : int) : int`, the number of binary digits of `m >= 0`, with `bits 0 = 0`, `bits (m / 2) = bits m - 1` for `m >= 1`, and monotonicity;
- `log2 (m : int) : int`, `bits m - 1` for `m >= 1`, the floor of the binary logarithm;
- `clog2 (m : int) : int`, the ceiling, for bounds such as a heap's height.

They are recursive spec functions, so their laws are proved by induction lemmas, and goals use the lemmas rather than unfolding the definitions.

### 7. Interfaces and certificates

A `costs` clause is part of its function's contract, so it is in the interface and in the interface hash ([ADR 0024](0024-published-proof-certificates.md)). Importers rely on it as on `ensures`. A new version of a library refines the old one if its bound is no larger under the old `requires`, which is one more goal in the refinement check. Removing a `costs` clause breaks the interface. No item is trusted: a cost bound is proved like any other contract, so certificates record nothing new.

### 8. Build time

A function without `costs` has no `spent` and no cost goals, so existing code costs nothing more to prove. A function with `costs` gets one more loop-carried `int` and one more goal per return and per invariant. These goals are linear when the bound is linear or written with `bits` and its lemmas. Bounds such as `n * bits n` are nonlinear. They are proved through lemmas that do the multiplication once, or with `@solver(nlsat)`, and they join the benchmark corpus ([ADR 0032](0032-parallel-sliced-cached-proving.md)), so a costly bound shows up as a regression.

## Consequences

- The C++ library's complexity clauses become proved contracts: binary search, heap operations, sorts and partitioning first ([docs/cpp-std.md](../cpp-std.md)), and their doc comments stop restating them.
- Callers can bound their own cost from their callees' published bounds, so cost composes across modules like correctness does.
- Recurrences are proved to be followed, not solved. Solving them, and asymptotic claims, need ADR 0061's Lean lemmas, or induction lemmas in Pia where those are enough.
- A step is not time. Bounds say how work grows, and benchmarks still say how fast it is.
- Pia goes on being an upper-bound system. Lower bounds, worst-case inputs and parallel span (for `spread`, [ADR 0060](0060-spread-v0-ownership-and-runtime.md)) are left for later.
- New syntax: the `costs e` clause, the spec-only `spent`, and `@counts(f)`. `costs` is a keyword only in contract position.

### Implementation order

Each step is a PR with tests in `tests/verify/costs.pia`.

1. **`costs` and `spent` under the step model**: loops, calls, inferred bounds for functions with no loops or recursion, the error for a callee without a bound, and `spent` in invariants and `assert`s.
2. **Recursion and `@counts(f)`**, including function parameters and concept requirements, and `Pia.Math.Log` with its lemmas.
3. **Interfaces**: `costs` in `.piai`, the interface hash and the refinement goal; then the first proved clauses in `Pia.Core.Algo` (`lower_bound`, `upper_bound`, `push_heap`, `pop_heap`), with `docs/cpp-std.md` updated.
4. **Amortised bounds** with a potential, starting with `vec`'s `push`.
5. **Reporting**: `--verify-stats` and the REPL report cost goals separately, so their proof cost is visible.

## Open questions

1. **Is "steps" the right default?** The alternative is no default: every `costs` must name what it counts with `@counts`, so a bound always says what it is in units of. Steps are convenient for code written in Pia, and `@counts` fits C++'s clauses.
2. **Should a lint ask for `costs` on public library functions?** An idiom lint ([ADR 0037](0037-idiomatic-pia-and-lints.md)) could warn when an exported function of `Pia.Core` has loops and no `costs`, so the library's bounds are complete.
