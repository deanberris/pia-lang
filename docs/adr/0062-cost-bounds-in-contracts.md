# 62. Cost bounds are contracts: `costs c <= e` bounds what a function spends on a named counter, tracked by a spec-only `spent c` and proved by Z3

Date: 2026-11-24

Status: Accepted (2026-11-24, with Dean's answers below)

## Context

Pia proves what a function computes, but not how much work it does. [ADR 0040](0040-cpp23-standard-library-in-pia.md) documents C++'s complexity clauses ("at most `log2(n) + 1` comparisons") and does not prove them. [ADR 0056](0056-tests-generated-from-contracts-and-theories.md) checks them by fitting benchmark counts, which tests a few sizes, not every size. [ADR 0061](0061-lean-proved-facts.md) puts asymptotic claims (`O(n log n)`) and closed forms of recurrences in Lean, but they need an exact bound to be about, and that bound has to be proved of the code.

Dean decided, when he accepted ADR 0061, that cost proofs by Z3 come first, in their own ADR, since they need no Lean.

Most complexity clauses are exact upper bounds on a count: comparisons, swaps, loop iterations, calls. A count is an integer that the code increases. If the verifier tracks it like any other value, then a bound on it is an ordinary postcondition, and Z3 proves it with the loop invariants and lemmas Pia already has. This is the approach of time credits (Charguéraud and Pottier, in Coq with CFML), of Liquid Haskell's resource analysis (Handley, Vazou and Hutton, "Liquidate your assets"), and of calf (Niu, Sterling, Grodin and Harper). RAML (Hoffmann) infers polynomial bounds automatically by linear programming. Pia starts with stated bounds, which are checked, and leaves inference for later.

## Decision

### 1. `costs c <= e` bounds what a function spends on one counter

A function may state its cost after its other contracts, and every cost clause names what it counts:

```ocaml
let find (xs : [u32]) (v : u32) : usize
  ensures result <= len xs
  costs iterations <= len xs
= ...
```

`costs c <= e` means that every run of the function, from any state meeting its `requires`, spends at most `e` on the counter `c`. `e` is a spec expression of type `int` (unbounded, so a bound never overflows) over the parameters and their `old` values. A function may have several cost clauses, one per counter, such as `costs less <= n` and `costs swap <= n` for a sort. Each is proved on its own.

Only upper bounds are in scope, because they are what callers need: a caller that knows each callee's bound can add them up. Lower bounds and exact counts are out of scope. `costs` is a keyword only in contract position, like `requires` and `ensures`.

### 2. Counters

There is no default cost model. A bound always says what it is in units of, so two bounds are never compared in different units by accident (Dean, 2026-11-24). A counter is one of:

- **A function**, a function parameter, or a concept requirement such as `Ord`'s `less`: each call to it counts one. This is how C++ states its clauses, in comparisons, swaps or assignments.
- **`iterations`**: each iteration of a loop in the function counts one.
- **`calls`**: each call to a function that is not a spec function or lemma counts one.

`iterations` and `calls` are names only after `costs` and `spent`, not keywords, so they do not take names away from code.

**What a callee contributes.** A call adds the callee's own bound for the same counter, with its arguments substituted, so cost composes. The callee contributes nothing if the counter cannot be reached from it: for a function counter `f`, the callee is not `f`, does not take `f` as an argument and has no concept that provides it, which the type checker decides from its signature. For `iterations` and `calls`, every callee can reach the counter, so it must have a bound for it. A callee with no loops and no recursion has one without writing it: the compiler works out the constant from its body. Any other callee without a bound for the counter is an error that names it: "`sort` has no bound on `less`, so the cost of `top_k` on `less` cannot be proved; add `costs less <= ...` to `sort`."

A counter counts events, not time. A count says nothing about caches or vector width, so performance budgets stay benchmarks (ADR 0056). What a cost bound proves is the shape that a benchmark measures: how the work grows with the input.

### 3. `spent c` counts what has been spent so far

Inside a function with a cost clause on `c`, the spec-only value `spent c` is what the function has spent on `c` so far. It is `0` on entry. Each counted event adds one, and each call adds the callee's bound. At each return, `spent c <= e` is a goal, with `e` evaluated at the parameters' entry values.

`spent c` is a loop-carried value like any other, so loops bound it with an invariant, and the loop machinery that exists today ([verifier.md](../verifier.md#loops)) does the rest. Binary search, counting calls to `less`:

```ocaml
let lower_bound (xs : [t]) (v : t) : usize
  requires sorted xs
  costs less <= Pia.Math.Log.bits (len xs)
= let lo : mutable usize = 0 in
  let hi : mutable usize = len xs in
  while lo < hi
    invariant lo <= hi && hi <= len xs
    invariant spent less + Pia.Math.Log.bits (hi - lo) <= Pia.Math.Log.bits (len xs)
  do
    let mid = lo + (hi - lo) / 2 in
    if less xs.[mid] v then lo <- mid + 1 else hi <- mid
  done;
  lo
```

`bits m` is the number of binary digits of `m`, which is `floor (log2 m) + 1` for `m >= 1`: exactly C++'s "at most `log2(n) + 1` comparisons". Each iteration costs one `less` and leaves a range of at most `(hi - lo) / 2`, and `bits` drops by one when its argument is halved. That fact is a lemma of `Pia.Math.Log`, so the invariant's goal is linear.

(Step 1, 2026-11-24: the count is encoded as a `usize` that saturates at 2^64 - 1, not an `int`, because Z3 relates an `int` to machine integers through `bv2int` and timed out on the simplest loop invariants; see [verifier.md](../verifier.md#cost-bounds).)

`spent c` can appear in loop invariants, `assert`s and lemma calls. It cannot appear in code, in `requires` or in `ensures`, and codegen erases it like any spec value. Encoded, it is a spec `int` local per counter, which IRGen threads through loops, branches and error handlers like a mutable local ([ADR 0028](0028-error-propagation-and-cleanup.md)'s `?` returns are returns, so each has the goal).

### 4. Recursion

A recursive function with `costs` must have `decreases`. At a recursive call, the call's bound is the function's own `costs` at the call's arguments, as its `ensures` is assumed there. That is sound by induction on the measure, which is why the measure is required. Its cost is then a recurrence, which is often best written as a recursive spec function:

```ocaml
let spec merge_cost (n : int) : int
  requires n >= 0
  decreases n
= if n <= 1 then 0 else merge_cost (n / 2) + merge_cost (n - n / 2) + n

let merge_sort (xs : inout [t]) (scratch : out [t]) : unit
  requires len scratch = len xs
  ensures sorted xs && permutation xs (old xs)
  costs less <= merge_cost (len xs)
  decreases len xs
= ...
```

Z3 proves that the code follows the recurrence, one call at a time. It cannot solve the recurrence. A closed form such as `merge_cost n <= n * bits n` needs induction beyond one step, and an asymptotic claim such as `merge_cost in O(fun n => n * log2 n)` is a limit. Both are lemmas for Lean, by [ADR 0061](0061-lean-proved-facts.md). Until then, a closed form that a recursive lemma can prove in Pia is proved there, and callers use it.

### 5. Amortised bounds

An operation that is cheap on average, such as `vec`'s `push` or a union–find `union`, states its bound with a potential: a spec function of the structure's model ([docs/stdlib.md](../stdlib.md), ghost models), such as `costs calls <= 1 + phi (old v) - phi v`. It is an ordinary `costs` expression, using `old`, so nothing new is needed to prove it. A sequence of `k` pushes then costs at most `k + phi (first) - phi (last)`, which is linear, because the potential is never negative (a lemma about `phi`). This is the banker's method of time credits, written as a contract.

### 6. `Pia.Math.Log`

A small spec-only module of the functions cost bounds use, with their laws as lemmas proved in Pia:

- `bits (m : int) : int`, the number of binary digits of `m >= 0`, with `bits 0 = 0`, `bits (m / 2) = bits m - 1` for `m >= 1`, and monotonicity;
- `log2 (m : int) : int`, `bits m - 1` for `m >= 1`, the floor of the binary logarithm;
- `clog2 (m : int) : int`, the ceiling, for bounds such as a heap's height.

They are recursive spec functions, so their laws are proved by induction lemmas, and goals use the lemmas rather than unfolding the definitions.

### 7. Interfaces and certificates

A `costs` clause is part of its function's contract, so it is in the interface and in the interface hash ([ADR 0024](0024-published-proof-certificates.md)). Importers rely on it as on `ensures`. A new version of a library refines the old one if its bound is no larger under the old `requires`, which is one more goal in the refinement check. Removing a `costs` clause breaks the interface. No item is trusted: a cost bound is proved like any other contract, so certificates record nothing new.

### 8. Build time

A function without a cost clause has no `spent` and no cost goals, so existing code costs nothing more to prove. A function with a cost clause gets one more loop-carried `int` per counter and one more goal per return and per invariant. These goals are linear when the bound is linear or written with `bits` and its lemmas. Bounds such as `n * bits n` are nonlinear. They are proved through lemmas that do the multiplication once, or with `@solver(nlsat)`, and they join the benchmark corpus ([ADR 0032](0032-parallel-sliced-cached-proving.md)), so a costly bound shows up as a regression.

## Consequences

- The C++ library's complexity clauses become proved contracts: binary search, heap operations, sorts and partitioning first ([docs/cpp-std.md](../cpp-std.md)), and their doc comments stop restating them.
- Callers can bound their own cost from their callees' published bounds, so cost composes across modules like correctness does.
- Recurrences are proved to be followed, not solved. Solving them, and asymptotic claims, need ADR 0061's Lean lemmas, or induction lemmas in Pia where those are enough.
- A step is not time. Bounds say how work grows, and benchmarks still say how fast it is.
- Pia goes on being an upper-bound system. Lower bounds, worst-case inputs and parallel span (for `spread`, [ADR 0060](0060-spread-v0-ownership-and-runtime.md)) are left for later.
- New syntax: the `costs c <= e` clause and the spec-only `spent c`. `costs` is a keyword only in contract position, and `iterations` and `calls` are names only after `costs` and `spent`.
- Every exported `Pia.Core` function with a loop or recursion states a bound, which a lint checks (below).

### Implementation order

Each step is a PR with tests in `tests/verify/costs.pia`.

1. **`costs c <= e` and `spent c` for `iterations` and `calls`**: loops, calls, inferred bounds for functions with no loops or recursion, the error for a callee without a bound, and `spent c` in invariants and `assert`s.
2. **Recursion and function counters**, including function parameters and concept requirements, and `Pia.Math.Log` with its lemmas.
3. **Interfaces**: cost clauses in `.piai`, the interface hash and the refinement goal; then the first proved clauses in `Pia.Core.Algo` (`lower_bound`, `upper_bound`, `push_heap`, `pop_heap`), with `docs/cpp-std.md` updated.
4. **Amortised bounds** with a potential, starting with `vec`'s `push`.
5. **Reporting**: `--verify-stats` and the REPL report cost goals separately, so their proof cost is visible.
6. **The lint** `unbounded_cost` ([ADR 0037](0037-idiomatic-pia-and-lints.md)): an exported function of a `Pia.Core` module with a loop or recursion and no cost clause is a warning. It is on for `lib/Pia/Core` from the start, and the warnings it finds there are fixed module by module.

**Step 2a as built (2026-11-28).** A counter may name a function of the module, `costs less <= e`. Each call of it counts one, and a call of anything else adds the callee's bound on it. Section 2 decides reachability from the callee's signature, which is right for a function parameter or a concept requirement but not for a function of the module, which any body may call by name. So a callee without a clause adds 0 when no path through its body, its callees' bodies or a call through a function reference reaches the counted function, whatever loops or recursion it has, and otherwise is inferred as for `calls`. Function parameters and concept requirements as counters, and `Pia.Math.Log`, are step 2b (tests/verify/cost_functions.pia).

**Step 2b as built (2026-11-28), counters.** A counter may name a parameter of function type or a requirement of a concept on the function's type parameters. The proof over any function argument (ADR 0044) or over the type parameters (ADR 0043) counts each application of the parameter's stand-in, or call of the requirement, as one, and a call the parameter is passed to adds the callee's bound on its own parameter, or is an error when it has none. A specialisation renames the counter to what the parameter was given: the lambda, the named function (also when it goes through the wrapper with the arrow's contract, which calls it once), or `apply` for a closure or a function object. That last counts every `apply`, more than the parameter's, which a bound may only overcount. Only a specialisation at a lambda without captures is discharged by the generic proof: a named function or `apply` may be called elsewhere in the body or call itself, which the proof's count of applications does not see, so those specialisations are proved on their own. `Pia.Math.Log` follows in its own PR (tests/verify/cost_parameters.pia).

## Answers to the open questions

Dean answered when he accepted it (2026-11-24):

1. **Every bound names what it counts.** There is no default cost model, so `costs` always names its counter (`iterations`, `calls`, or a function such as `less`), and `spent` takes the counter too. This replaced the proposed default of steps and the `@counts(f)` attribute.
2. **A lint asks for bounds on the library.** `unbounded_cost` warns on an exported `Pia.Core` function with a loop or recursion and no cost clause (step 6).
