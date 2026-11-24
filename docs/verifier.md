# Verifier v0

Status: implemented in M5 ([#6](https://github.com/deanberris/pia-lang/issues/6)).

`piac --verify file.pia` lowers a program ([irgen.md](irgen.md)) and tries to prove every goal in it. It prints one line per goal and a summary, and exits with status 1 if any goal fails, or is skipped without `--allow-unproved` accepting it (the same flag as codegen, [codegen.md](codegen.md)):

```
overflow.pia:18:36: failed: '+' does not overflow u8
  counterexample: a = 248, b = 248, result = 496
overflow.pia:23:38: proved: '+' does not overflow u16 [intervals]
3 proved, 2 failed, 0 skipped
```

`piac --verify --emit=mlir` prints the IR as well, with the report on stderr. Every op whose goals all hold carries `pia.proved = "intervals"` or `pia.proved = "smt"`. `piac --dump-smt` prints each solver query.

This follows the pipeline in [architecture.md](architecture.md#verifier). The limits of v0 are listed at the end.

## Goals

The verifier walks each function in order and collects these goals:

| Goal | Raised by |
| --- | --- |
| `nooverflow` | `pia.add`, `sub`, `mul`, `div`, `band`, `bor`, `bxor`, `shl`, `shr` and narrowing `pia.convert` in `overflow(proof)` mode, which is the default. Also `pia.to_index` on a signed type (the index is not negative) and `pia.from_index` to a type narrower than `usize`. |
| `nonzero` | the divisor of `pia.div` and `pia.rem`, in every mode |
| `shift` | the amount of `pia.shl` and `pia.shr` lies in [0, w), w the storage width of the shifted value's type, in every mode |
| `inbounds` | `pia.load` and `pia.store`: `0 <= i < len`. `pia.slice`: `0 <= lo <= hi <= len` |
| `assert` | `assert p`, and `pia.abort`, whose claim is `false`: the path to it is impossible |
| `ensures` | each postcondition, at the return |
| `requires` | each of the callee's preconditions, at a call |
| `invariant` | each loop invariant, on entry and after each iteration ([Loops](#loops)) |
| `decreases` | each loop measure, and the function's measure at each recursive call ([Termination](#termination)) |
| `nonzero` | the step of a `for` loop, when it is not a constant |
| `emptyslot` | a `pia.store` marked `pia.fills`, which stores a box or other owning element: the element written over owns nothing ([ADR 0048](adr/0048-buffers-whose-elements-hold-slices.md), section 6) |

`wrap`, `saturate` and `trap` arithmetic raises no overflow goal. Wrapping and saturating results are modelled exactly. A trapping result is the exact value, since the program stops if it does not fit.

**Specifications are exact.** Ops that only feed contracts, such as the arithmetic in `ensures 2 * result <= a + b`, compute mathematical values and raise no goals. A contract can mention `a + b` without it overflowing, and `len xs > 0 ==> xs.[0] < 10` can read `xs.[0]` under its guard.

Goals are kept in the verifier's own list, in walk order. The architecture describes materialising them as `pia_contract.obligation` ops, and that waits for the modular and incremental work, where obligations must outlive one run. The verifier already accepts `obligation` ops, and `nonzero` was added to the obligation kinds.

## Intervals first

Before calling the solver, the verifier tries the operand ranges. A value's range is its type, narrowed through widening conversions, constants and other proof-mode arithmetic: `a * b + c` on `u8`, `u8` and `u16` lies within `[0, 130560]`, so it fits in `u32`. These goals are proved by intervals:

- arithmetic whose exact range fits the result type
- a divisor whose range excludes zero
- a quotient of non-negative operands, which lies in `[0, a]`
- an index into a fixed array whose range lies within the array, such as `lut.[i]` with `i : int{0..255}` and a 256-element `lut` ([design.md](design.md#primitive-types-and-overflow))

Everything else goes to Z3.

## Encoding

Each remaining goal becomes one query in the upstream `smt` dialect. The query is exported to SMT-LIB and decided by Z3 in-process ([ADR 0011](adr/0011-mlir-and-z3-implementation.md)). It holds:

- every parameter as a constant, with its type's range assumed
- the function's ops up to the goal, as terms
- every earlier goal as an assumption, which is sound because each is checked in its own query
- the goal's negation under the path condition

`unsat` means the goal holds. With `sat`, the model is the counterexample.

**Integers are bit-vectors.** Every Pia integer is a signed bit-vector of one width per function: 68 bits, wide enough for the exact sum or difference of any values in `[-2^63, 2^64 - 1]`. A multiplication widens a function to 132 bits only when its exact product can need more than 66 bits, which the operands' types decide: `u8 * u8` or `77 * r` stays at 68, `u64 * u64` or a product of `usize` values does not. The function's callees count too, since their contracts are encoded at each call. So one wide product slows only the functions that compute it, and the encoding never wraps by accident. Ranges are constraints on these bit-vectors. `wrap` reduces into the type with `bvsmod`, and `saturate` clamps with `ite`. `index` uses the same sort.

**Booleans** are SMT booleans. In contracts `&&`, `||` and `==>` are already plain logic. In code they arrive as `scf.if`, which becomes `ite`.

**Arrays and slices** are SMT arrays from index to element. A fixed array's length is its type's. A slice's length is a constant in `[0, 2^64 - 1]`. `pia.store` produces a new array term. After an `if`, the two branches' arrays merge with `ite`. A constant array (`pia.const_array`) is a broadcast array with each value stored into it, so every element is known. A `with_arena`'s region (`pia.region`) is a new broadcast array of zeros each time it is reached. A slice `pia.slice` has no array of its own: the verifier tracks its length and its offset in the root buffer, and reads and writes it there. A callee sees a slice argument as a fresh array, linked to the root by `forall i. 0 <= i < len ==> v[i] = root[off + i]`. A callee that writes it leaves a fresh root that equals the old one outside `[off, off + len)`. Every loaded element is assumed to lie in its element type's range.

**Control flow.** The two branches of `scf.if` are walked under the condition and its negation, and the results merge with `ite`.

**Atomics** ([ADR 0052](adr/0052-atomics.md), section 3). Another task may write a cell between any two accesses, so the verifier models nothing of the cell itself. Each `atomic_load`, and the old value each read-modify-write or `atomic_cas` returns, is a fresh value of the cell's type with its range assumed, so two loads of one cell may differ. `atomic_cas` succeeded exactly when its old value equals `expected`, which needs no extra fact, since that is the comparison the program makes. Stores and `desired` meet the cell's type through IRGen's conversion, which is a goal on a refined cell, so a refined cell's range holds across every task, one store at a time. An `@proof` add on a refined cell is the goal that the old value plus the operand stays in the range, for an old value about which only the range is known. A function with an atomic op never defines a value, so its callers use its contract, never its body.

**Records** are replaced with their fields before encoding ([irgen.md](irgen.md#records)). So a `pixel` parameter is four constants, and its counterexample values are named `p.r`, `p.g`, `p.b` and `p.a`.

**Buffers of slices** ([ADR 0048](adr/0048-buffers-whose-elements-hold-slices.md)) are an array of arrays with an array of their lengths. `xs.[i]` is element `i`'s array and length; a write through it goes back into `xs`, and every other slice read from `xs` is read again from it, so two reads of one element agree. Distinct elements are distinct arrays, which is sound because only elements that own their slices can be written through. A callee that may write such a buffer leaves its contents and lengths unknown. A callee's contract and a spec function see the elements' lengths too: a spec function over a buffer of slices takes them as one more argument, so calls with different lengths are different applications, and `old` reads them as they were on entry. An `if` that replaces an element in one branch merges the lengths as it merges the contents (tests/verify/vec_boxes.pia). An element moved out (`pia.moved_out`) gets length zero and keeps its contents, which the moved value reads, so the element left behind owns nothing and every access through it is out of bounds. A store marked `pia.fills` is a goal, "the element written over owns nothing": the old element's length is zero. An `out` buffer of slices, whether a parameter or what a function marked `pia.out_result` lends, starts with every length zero.

**Calls** use the callee's contract, not its body. Its preconditions become goals, with the arguments substituted. The result is a fresh value of the result type. The callee's postconditions are assumed about it, with `old` reading the arguments as they were before the call. A call under `old`, as in `ensures held m = old (held m)`, is the call the walk made with the parameters' entry values, so it means what the callee's contract says; this holds for a parameter holding a buffer too, when the callee's postconditions read no buffer's elements (tests/verify/old_calls.pia). A function with a spec-only result whose body only computes on its parameters, such as `held (m : bump) : Alloc.heap = m.h`, is unfolded at its callers like a pure function of scalars. A callee that returns one of its parameters unchanged gives a result equal to that argument. Buffers the callee may write (`out` or `inout`) are fresh arrays afterwards. Recursion needs nothing special.

**`old e`** reads the function's arrays as they were on entry.

**Quantifiers.** `forall (i in lo..hi). p` becomes an SMT `forall` over the bound variable, `(type range && lo <= i && i < hi) ==> p`. `exists` conjoins the guard instead.

**Division.** Z3 bit-blasts division, and cannot show `a mod b < b` on 68-bit values, or `(a / b) * b + a mod b = a` on 32-bit ones, within its timeout. So beside each division the encoding states, when `b` is not zero, the facts of truncating division: `(a / b) * b + a mod b = a`; the remainder has the dividend's sign and `-|b| < a mod b < |b|`; the quotient lies between zero and `a` (or `-a`), is `a` or `-a` when `b` is 1 or -1, and is strictly inside when `|b| >= 2`; and for non-negative operands `0 <= a / b <= a` and `0 <= a mod b < b`. Inside a quantifier, where the operands may be bound variables, it does not. A goal whose query divides by a value that is not a constant is first tried with `bvsdiv`, `bvsrem` and `bvmul` as uninterpreted functions, in a Z3 context of its own and with a small budget (500,000 rlimit units): any function models an uninterpreted one, so unsat there is a proof, and goals that follow from the facts alone, such as a quotient fitting its type, are proved without bit-blasting a divider. Otherwise the exact query decides, and gives the counterexample. Bit-blasted dividers are also what makes a goal's cost vary between runs on different numbers of threads, so this keeps proof cost reproducible ([ADR 0032](adr/0032-parallel-sliced-cached-proving.md)).

**Products.** Bit-blasting is exact, but a 68- or 132-bit multiplier is a large circuit, and goals such as `a <= b ==> a * c <= b * c`, or a pixel index `(y * w + x) * c + k < w * h * c`, time out on it. So a nonlinear goal, one whose query multiplies two terms that are not literals or divides by one, is next tried with Z3's int-blasting solver ([ADR 0066](adr/0066-int-blasting-for-nonlinear-goals.md)). That solver is Z3's `smt` tactic with `smt.bv.solver = 2`, which decides the bit-vector query as integer arithmetic. It runs in a context of its own, with a budget of 50,000,000 rlimit units. The translation is exact, so unsat is a proof, and on anything else the bit-blaster decides and gives the counterexample. Goals with a `@solver` strategy, theory axioms or `assume`s keep the bit-blaster. `--verify-stats` counts the goals proved this way as `intblast=`, and `--no-int-blast` turns the attempt off.

**Timeouts.** Each obligation is one Z3 query with two limits. The one that decides is `--solver-rlimit=<n>`, Z3's deterministic resource count, which does not depend on load or on the machine's speed; piac defaults to 1,200,000,000. `--solver-timeout=<ms>` is a wall-clock safety net, 600 seconds by default. A wall-clock limit alone would depend on load: a goal that proves in 5 seconds alone can time out while other goals and builds share the cores, and that is the normal case now that goals are solved in parallel. (`pia repl` and `pia-lsp` still use a wall-clock limit, `--timeout-ms`, since they answer interactively.) `--solver-cost` verifies like `--verify` and prints each proved SMT goal's resource count, as `(cost N)`, so a limit can be chosen from measurements. `--goal-times` prints how long each proved goal took to solve, as `(N ms)`. A slow proof can be cheap: its time may go into encoding the queries, not solving them, which the sum of these times shows. A goal the solver gives up on is reported as failed, with the reason, such as `[the solver gave up: timeout]` or `[the solver gave up: max. resource limit exceeded]`. The `pia_object` Bazel rule passes `--solver-rlimit=1200000000`, about 20 times the costliest goal in the repository (`settle` in docs/streams.pia.md, 56,923,063), and a 600-second timeout that serves only as a safety net, so whether a build proves its goals does not depend on load.

**Counterexamples** name the parameters, using the names IRGen records in the block arguments' locations, and slice lengths as `len xs`. They add the values that explain the goal: `result` for an overflow, `index` and `length` for bounds. Array contents are not shown yet.

## Parallel, sliced and cached proving

Build time is a benchmark ([ADR 0032](adr/0032-parallel-sliced-cached-proving.md)). Goals are listed and encoded in walk order on one thread, then the SMT queries are decided on a pool of threads, one per core unless `--jobs=N` says otherwise, each in its own Z3 context. The report keeps the walk order, and under an rlimit every goal has the same result on any number of threads.

**Slicing** cuts a query to the goal's cone of influence: the negated goal, and every assertion that shares a symbol with one already kept, transitively. A precondition about `b` stays out of a goal about `x`. An `unsat` slice proves the goal, since only hypotheses were dropped. Otherwise the whole query is solved again, so slicing never stops a goal from proving, and a counterexample always comes from the full query. By default it is automatic, and only in a function with a buffer of records, which ScalarizeRecords marks `{pia.record_buffers}`. There, a goal is sliced when the slice drops a whole declaration, a symbol the goal cannot reach: one buffer per field means a goal about `xs.[3].a` is asked alongside quantified facts about `xs.g` and `xs.b` that it never needs. Those facts make Z3's search grow quickly with the number of fields. Copying four-field records through a view costs 777 million resource units in full and 1.6 million sliced. `--slice` slices every goal whose slice is smaller, and `--no-slice` always solves the full query. Elsewhere slicing costs more than it saves: applied to every query that drops a declaration, it raises the streams demo from 269 million resource units to 395 million, and forcing it with `--slice` gives 392 million and 47 seconds on one thread, against 269 million and 33 seconds without. Smaller queries are not always easier for Z3, and a goal whose slice is satisfiable is solved twice. With the rule limited to buffers of records, every file in the benchmark (tools/bench) costs what it did before. The benchmark keeps measuring it.

**Selecting goals.** `--verify-only=<spec>` proves only the goals the spec selects, and can be repeated; a goal is proved if any spec selects it. piac takes one input file, and a second is an error, so a selection that a shell passed with a space before it, as zsh passes an unquoted variable, is reported rather than verifying the whole module (#376):

```sh
piac --verify-only=settle streams.pia.md          # one function
piac --verify-only=streams.pia.md streams.pia.md  # one module
piac --verify-only=edges.pia:41 edges.pia         # the goals on one line
```

Earlier goals are still assumed, as in a full run. Unselected goals are left out of the report, and a selective run never generates code.

**Proof cache.** `--proof-cache=<dir>` keeps a file per proved goal, named by the SHA-256 of the Z3 version, the rlimit and the query. A goal whose query is unchanged is not solved again, and calls are encoded from contracts, so editing a callee's body does not invalidate its callers. Failures are never cached.

**Statistics.** `--verify-stats` prints one line to stderr, here for `docs/streams.pia.md` on one thread:

```
verify-stats: goals=243 unselected=0 intervals=21 skipped=0 solved=222 cached=0 sliced=0 unsliced=0 threads=1 cost=269094119 encode_ms=947 solve_ms=30213 ...
```

`solved` counts the queries sent to Z3, `cached` the goals the cache answered, `sliced` the queries slicing made smaller, `unsliced` the slices solved again in full, and `cost` Z3's resource count over every query. The rest of the line splits the goals by where they came from ([ADR 0037](adr/0037-idiomatic-pia-and-lints.md)): `type`, `type_smt` and `type_cost` for goals the types of values raise (overflow and narrowing, bounds, divisors, shifts, exhaustiveness, out parameters), and `contract`, `contract_smt` and `contract_cost` for written ones (preconditions at calls, postconditions, invariants, measures, assertions, laws), with how many of each needed the solver and what they cost. After the report, a goal that cost a tenth of the rlimit or more gets a `costly_goal` warning ([Idiomatic Pia](idioms.md#decomposed-reasoning)). `tools/bench/proof_bench.py` runs these over the benchmark corpus on one thread and on every core, and CI fails when the cost grows by more than 10%. Z3's resource count varies by about 1% from run to run, since some of Z3's hash tables depend on memory addresses, so the benchmark compares reports exactly and costs within 5% over `tools/bench/baseline.json`.

## Loops

A loop is cut at its invariants, so the verifier never unrolls it.

```ocaml
let sum_to (n : u16) : u32 =
  let s : mutable u32 = 0 in
  for i in 0..n invariant s <= i * 65535 do s <- s + i done;
  s
```

1. **On entry**, each invariant is a goal, with the loop variable at its first value and the loop-carried values (`s` here) as they are before the loop.
2. **One arbitrary iteration** is then walked. The loop variable and the loop-carried values are fresh, and so is every buffer the loop writes. A `for` loop's variable satisfies `lo <= i < hi` and is a whole number of steps from `lo`. The invariant is assumed where it is written, so the goals in the body, such as `s + i` not overflowing, are proved for every iteration where it holds. At the end of the body, each invariant is a goal again, for the next value of the loop variable and the values the body leaves.
3. **After the loop**, what it computes and writes is fresh again, and only the invariant is assumed. A `for` loop's variable has then passed `hi` by less than one step, or equals `lo` if the loop never ran. A `while` loop's condition is also false.

The iteration's assumptions hold under a fresh guard in the path condition, so they say nothing about the code after the loop. A loop without an invariant still works, but nothing is known about its loop-carried values in the body or afterwards: without its invariant, `s + i` above could overflow.

A `while` loop's invariant is written before `do` and holds each time the condition is evaluated. The condition's own goals, such as the bounds of `xs.[i]` in `while i < len xs && xs.[i] <> x`, are proved in the iteration, under the invariant.

## Termination

A `for` loop always ends. A `while` loop ends when it has a measure, `decreases m`, that is never negative and goes down on each iteration. That is a `decreases` goal at the end of the body, `m >= 0 && m' < m`, where `m'` is the measure after the iteration. A function's `decreases` is checked the same way at each call of the function by itself: `gcd b (a mod b)` with `decreases b` needs `b >= 0` and `a mod b < b`, under the path condition `b <> 0`.

A recursive call on a value of a recursive type needs no measure when it is structural: its first argument of a recursive type is a component of the parameter, as a name a `match` binds below the top is, or an element of a box or vec such a name holds ([recursive types](#recursive-types)). Its goal, "the recursion terminates: 't' is smaller in each recursive call", is that the argument's `depth` is smaller than the parameter's.

Any other `while` loop or recursive call with no measure gets a `skipped` goal ("the loop terminates", "the recursion terminates"). So `piac --verify` fails, and piac generates no code, unless `--allow-unproved` accepts it ([codegen.md](codegen.md)).

## Recursive types

A value of a `let rec` variant ([ADR 0047](adr/0047-recursive-sum-types-and-shared-references.md)) is a value of an SMT-LIB datatype: mutually recursive types and the types they hold are declared as one `declare-datatypes`, a generic one once per instance, and each constructor holds its payload's fields. A constructor, a `match` and its payload names are the datatype's constructor, tester and selectors, so the proof sees what a value was built from, as it does for a variant.

- **A buffer in a payload,** such as a `box`'s slot or a `vec`'s items, holds what it held when the value was built: since `box` and `vec` own their contents uniquely, the proof sees a recursive value as a value, not as a heap. That holds while only the value owns the buffer, so a function that writes a buffer after building a value with it, or writes a buffer taken out of a value, is not verified: each of its goals is unproved, with that reason. Z3 does not decide datatypes whose constructors hold arrays well, so the field is a handle, an element of an uninterpreted sort, and the array is a function of the handle.
- **`depth t` and `size t`** are spec-only `int`s, for `decreases` and other contracts. The verifier knows only that a depth is at least 0 and a size at least 1, and that a component's, including each element of a box or vec in the payload, is smaller than its holder's. That is what a measure needs; their exact values are not known.
- **Structural recursion** is a `decreases depth t` on the function's first parameter of a recursive type ([termination](#termination)).

A counterexample shows a recursive value as its constructor and its payload's fields in order, `Node {_, 7, 4294967295, _, 0}`, where `_` is a buffer (tests/verify/rec_types.pia, tests/verify/rec_aliasing.pia). Equality of recursive values, `@derive(eq)` and structural lemmas come with metaprograms over recursive types (step 4).

## Spec functions and lemmas

`let spec f ...` defines a spec function: pure and total, used to say what code means. Contracts, other spec functions and lemmas can call it. Code cannot, and codegen erases it. It cannot loop, write a buffer, `abort`, or call anything but spec functions and pure functions of scalars. A recursive one needs `decreases`, and spec functions cannot be mutually recursive yet. Its body is checked like any function's: its own goals, its `ensures`, and its measure at each recursive call. A spec function imported from another module's interface comes with its definition, which importers unfold, but its goals are proved once, in its own module, not again in each importer (ADR 0039).

To the solver, `f` is an uninterpreted function `F` with one argument per scalar parameter and two, the array and its length, per buffer. A call `f a`, wherever it is, is `F a`, with these facts:

- `F a` is in the result type's range.
- `pre(a) ==> post(a, F a)`: f's postconditions, where its preconditions hold.
- `pre(a) ==> F a = body(a)`: the definition, unfolded once. A recursive call in the body is `F` again, with the two facts above but no definition. `@fuel(n)` on the return annotation unfolds n levels.

The definition is guarded by the precondition because termination is proved only where the precondition holds, so outside it the body could define `F` in terms of itself. Inside a quantifier, the facts for calls that mention the bound variables become hypotheses of the quantifier. A call that passes a view inside a quantifier is left uninterpreted, and so is a definition with a value the encoding cannot model.

A call in code to a spec function is a goal for its precondition, as for any call. In a contract, the call is checked the same way where it is walked, and is a plain term inside quantifiers and `old`.

`let lemma f ...` defines a lemma, which returns unit. It is proved once, like any function, and a call to it is a statement whose precondition is a goal and whose postcondition is assumed afterwards, by the usual rule for calls. Codegen erases lemmas and calls to them. An interface can list a lemma as `let lemma f : (a : int) -> unit requires ... ensures ...` (#305). The lemma is proved once, in its module. An importer calls it as `M.f a`, and that call works like a call to a local lemma: its precondition is a goal at the call, and its postcondition is assumed after it. The interface's contract must follow from the definition's, as for any function: the check calls the lemma, so it assumes what the lemma proved, by induction or otherwise. The interface and the definition must agree on which items are lemmas (tests/modules/lemma.pia). A recursive lemma with `decreases` is a proof by induction:

```ocaml
let spec count (xs : [u8]) (n : usize) (v : u8) : usize
  requires n <= len xs
  ensures result <= n
  decreases n
= if n = 0 then 0 else count xs (n - 1) v + (if xs.[n - 1] = v then 1 else 0)

let lemma split (xs : [u8]) (n : usize) (v : u8) (w : u8) : unit
  requires n <= len xs && v <> w
  ensures count xs n v + count xs n w <= n
  decreases n
= if n > 0 then split xs (n - 1) v w
```

One unfolding proves each step: the lemma's call for `n - 1`, plus `count`'s definition at `n`. Without the lemma, a goal about every `n` needs more unfoldings than any fixed fuel gives.

**Opaque spec functions** ([ADR 0063](adr/0063-opaque-spec-functions.md)). A spec function marked `@opaque` keeps its definition out of every goal: a call `f a` still gets its result type's range and `pre(a) ==> post(a, F a)` from f's `ensures`, but not `F a = body(a)`. f's own goals are unchanged. This is for a spec over a whole stream or table, whose unfolded body would otherwise sit in every goal of a loop that mentions it, including goals that never needed it. `with f, g` after a function's or lemma's contracts reveals f and g in its whole body, and the expression `with f in e` reveals f only in e. A revealed definition is a fact for every call met in the scope, and for the calls already met before it, such as one in the precondition; after the scope, a call with new arguments is opaque again. The intended pattern is to reveal in small step lemmas, never in the loop itself. An imported opaque function stays opaque, since the interface carries `@opaque` with its definition. A goal that fails while an opaque function was left unrevealed has the hint "'f' is opaque here; 'with f' may prove it". Codegen erases `with` (tests/verify/opaque.pia, tests/modules/opaque.pia).

```ocaml
let spec small (x : u8) : bool @opaque = x < 10

let shown (x : u8) : u8
  requires small x
  ensures result < 20
  with small
= x + x
```

Parameters of spec functions and lemmas cannot be `out`, `inout` or `mutable`. `spec` and `lemma` are keywords only between `let` (or `let rec`) and the name ([grammar.md](grammar.md#identifiers-and-keywords)).

**Pure functions of scalars.** An ordinary function with scalar parameters and one scalar result, whose body has no loop, buffer access, `abort` or recursion, and calls only other such functions, always returns exactly what its body computes. A call to one, in a contract, a spec function or code, is its body's value where its precondition holds: with no precondition the call is the body's term itself, and with one it is `if pre then body else F a`. Since that needs no definition as a fact, it keeps its meaning inside an assumed `forall`, as in a callee's `ensures forall (k in 0..result). p xs.[k] = false`. A call in a contract to one without a precondition, whose arguments are loads, constants or other such calls, is specification like the arithmetic around it, so it may be guarded: `result < len xs ==> p xs.[result]` reads `xs.[result]` only where it is in bounds. This is what makes a lambda's body known where it is passed (ADR 0044): the lambda is a private function `lambda@file.pia:line:col`, and the specialisation of the higher-order function calls it. A function object's `apply` is one too once its record is split into fields, and so is a capturing lambda's, which unfolds at the call with the captured values (unless it reads a captured buffer), and so is a call of a generic proof's abstract function, a concept requirement such as `same xs.[result] v` in an `ensures`. So a generic's contract that names a concept function, such as `ensures result = (if less b a then b else a)` in `min`, means `b < a` at the `u8` instance, where `less` is `a < b`, and a spec function over `Ord t` can call `less` (`lex_from` in `lib/Pia/Core/Order.pia`). A call to any other function in a contract is still an unknown value, constrained only by the callee's own `ensures` (tests/verify/pure_calls.pia). A call in a contract to a function with a precondition, such as a spec function, is needed only where its value can matter, so its precondition is a goal, and its postconditions are facts, under the short-circuit guard it sits behind: the right operand of `a ==> b` and of `a && b` where `a` holds, and of `a || b` where `a` does not. `r < len xs ==> ok xs r` checks `ok`'s `requires k < len xs` only where `r < len xs`, as `xs.[r]` would be read there; `ok xs r || r < len xs`, with the call on the left, checks it everywhere (#282, tests/verify/contract_guards.pia). The guard is followed along single uses up to the contract; a call whose value is used twice, or which code reads, is checked unguarded.

## Spec-only `int` and `real`

Two types exist only for specifications ([ADR 0036](adr/0036-library-theories.md), step 1):

- **`int`**, an unbounded mathematical integer. Bare `int` is unbounded, and `int{lo..hi}` is still a range type: a range is written with its braces right after `int`, so the two spellings cannot be confused ([grammar.md](grammar.md)). The verifier encodes `int` as the SMT `Int` sort. An element of a slice read in a spec function's body keeps its type's range, as it does where code loads one: an element of a `[u32]` is between 0 and 2^32 - 1 there, so a sum of them as an `int` does not decrease.
- **`real`**, a mathematical real number, encoded as the SMT `Real` sort. It is not a floating-point type.

They have `+`, `-`, `*`, unary `-` and the comparisons, and `real` also has `/`. All of it is exact, so nothing overflows and no `nooverflow` goal is raised. A real division raises a `nonzero` goal for its divisor where it is walked as code, such as in a spec function's body. An integer literal takes either type from the context, and an `int` literal may be larger than any machine type. A literal with a decimal point or an exponent, such as `0.5` or `1.0e3`, is a `real`, read as an exact rational (`1/2`, `1000`), and a suffix such as `0.5f32` is an error until Pia has floating-point types.

Conversions are exact, so none raises a goal. `int x` turns any integer into an `int`, and an integer also widens to `int` wherever an `int` is expected, as a range type widens to a larger one. `real x` turns an integer or an `int` into a `real`. There is no conversion back: a value of a machine type cannot come from a specification.

```ocaml
let spec half (x : real) : real = x / 2.0

let lemma product (x : real) (y : real) : unit
  requires 0.0 <= x && x <= 1.5 && 0.0 <= y && y <= 2.0
  ensures x * y <= 3.0
= ()

let lemma wide (a : u64) (b : u64) : unit
  ensures int a * int b <= 340282366920938463426481119284349108225
= ()

let halve (x : u8) : u8
  ensures real result <= half (real x) && half (real x) < real result + 1.0
= x / 2
```

`product` is nonlinear, and Z3 decides it with its nonlinear real arithmetic; with `x * y < 3.0` it fails with the counterexample `x = 3/2, y = 2`. A counterexample shows a real as a fraction, and an irrational value from a nonlinear model as a decimal approximation marked `~`.

**Spec-only.** `int` and `real` may appear in spec functions, lemmas, contracts and quantifiers (`forall (y : real). y * y >= 0.0`), and in the arguments of a lemma call. Code may not compute with them. It may only store one in a spec-only place: a parameter, local or record field of a spec-only type, as in `let steps : int = 10` or `t.heap <- Alloc.take t.heap b` ([ADR 0041](adr/0041-allocator-semantics-as-a-theory.md)). The expression stored is checked as spec code, so it may call spec functions. A field of a buffer's records may be spec-only, as `state` is in a buffer of `{ slot : [u16]; state : int }`: it is a buffer of its own, which the verifier sees and codegen erases, so C passes only the other fields (tests/verify/spec_buffers.pia, tests/codegen/spec_state.pia). A buffer whose elements are wholly spec-only, such as `[int]`, is an error, since its length is in code; a spec local of fixed length, `let spec sums : mutable [int; 9] = zeros`, is not ([Spec state](#spec-state)). Any other expression of such a type in code is an error. `let positive (x : u8) : bool = real x > 0.5` gives:

```
positive.pia:1:32: error: this expression has the spec-only type real; int and real can be used only in spec functions, lemmas, contracts and quantifiers, not in code (ADR 0036); code can only store it in a spec-only place, such as a field, local or parameter of that type (ADR 0041)
```

So nothing the program computes depends on a spec-only value. The verifier sees spec-only state like any other, and codegen erases it, along with spec functions, lemmas and contracts (see [codegen.md](codegen.md), "Spec-only state").

**Encoding.** `int` uses the upstream `smt` dialect's `Int` sort and its operations. The dialect has no `Real` sort at our LLVM pin, so the verifier extends it in the smallest way that keeps it the one encoding: `real` is written as a sort named `Real`, and the operations the dialect lacks (Real `+ - * /` and comparisons, `to_real`, and `bv2int` for converting a bit-vector) are declared as functions under their SMT-LIB names and applied with `smt.apply_func`. When the query is exported to SMT-LIB, those declarations and the sort's `declare-sort` are dropped, so Z3 reads each use as SMT-LIB's own interpreted symbol. A machine integer becomes an `Int` as `bv2int` of its bit-vector, less `2^w` when it is negative, since `bv2int` reads a bit-vector as unsigned. A real literal `n/d` is `(/ (to_real n) (to_real d))`.

## Spec state

`spec` marks a local or a parameter as spec-only whatever its type ([ADR 0058](adr/0058-spec-buffers.md)). It is how a proof keeps state that evolves with the code, such as a reference implementation run beside a fast one, or the trace of what a loop has written. For now a spec local is a fixed array `[t; n]`, whose length is a constant, and its elements may be machine integers, `bool`, `int` or `real`. `zeros` makes an array of zero elements of the type it is bound at, in code too.

```ocaml
let record (spec log : inout [u16; 64]) (i : int{0..63}) (v : u16) : unit
  ensures log.[i] = v
  ensures forall (k in 0 .. 64). k <> i ==> log.[k] = old (log.[k])
= log.[i] <- v

let twice (a : u16) (b : u16) : u16
  ensures result = a
= let spec log : mutable [u16; 64] = zeros in
  record log 0 a;
  record log 1 b;
  assert (log.[0] = a && log.[1] = b);
  a
```

The rule is the one for `int`: a spec value flows only into spec places and into contracts.

- **Code may write spec state.** `log.[i] <- v` is a spec write. Its index and value are specification, so they may read spec state too, as in `sums.[i + 1] <- sums.[i] + xs.[i]`, and its index is still a goal. A spec local's initial value may be any value of its type, so `let spec snap : [u8; 4] = a` keeps a snapshot of a code array.
- **Only specification may read it**: contracts, loop invariants, `assert`s, lemma calls, and the argument for a spec parameter. Anything else is an error, such as `s.[0]` as a function's result, `sum4 s`, or `if s.[0] = 0 then ...`.
- **A spec parameter the callee writes** (`out` or `inout`) takes a spec local or spec parameter by name, since codegen erases the write: a code buffer passed there would not change at run time, though the proof would say it does. An `in` spec parameter takes any value.

The verifier sees spec state as it sees any buffer: an SMT array, fresh at its `let` (an array of zeros for `zeros`), updated by each store, and fresh after a loop or a call that may write it. A spec write is no effect for a `spread`'s ownership goals: spec state is per-thread. An interface lists a spec parameter as `(spec log : inout [u16; 64]) -> ...`, and it must agree with the definition. Codegen erases a spec local's storage, every write to it, each spec parameter and the arguments calls pass for it, so `record` above is `void record(uint8_t i, uint16_t v)` to C ([codegen.md](codegen.md#spec-only-state); tests/verify/spec_locals.pia, tests/irgen/spec_local_errors.pia, tests/codegen/spec_state.pia).

**Spec fields.** A record field marked `spec`, as in `type { n : u8; spec seen : [u8; 256]; spec total : int }`, is spec state of any type, under the same rule: code may write it (`c.seen.[c.n] <- v`, `c.total <- c.total + v`, or a record literal's `seen = zeros`), and only specification may read it, so `c.owner` as a function's result is an error. This generalises ADR 0048's spec-only fields, whose types had to be spec-only: in a buffer of records such as `[{ spec owner : u8; v : u8 }]`, owner is a buffer of its own that the verifier sees and codegen erases, so C passes only the vs and their length, even with owner first. Codegen erases a spec field from records, buffers of records, parameters and results, and from the values loops and branches carry, so `count_from (z : int{0..15}) : counted`, with `counted = type { n : u8; spec seen : [u8; 16] }`, is `uint8_t count_from(uint8_t z)` to C. As for any record holding an array, the verifier cannot yet encode a loop that carries one (tests/verify/spec_fields.pia, tests/irgen/spec_field_errors.pia).

## Theories

A theory teaches the verifier a domain: new sorts, functions on them with no body, and axioms about them ([ADR 0036](adr/0036-library-theories.md), and the worked examples in [theories.md](theories.md)). Steps 2 and 3 of the ADR are implemented: theories, and models that prove them consistent.

```ocaml
@trusted

let theory Lip = sig
  let sort layer
  let spec in_w : (f : layer) -> usize
  let spec out_w : (f : layer) -> usize
  let spec lip : (f : layer) -> real
  let spec seq : (f : layer) -> (g : layer) -> layer
  let spec residual : (f : layer) -> layer

  let axiom lip_nonneg (f : layer) ensures lip f >= 0.0
  let axiom seq_shape (f : layer) (g : layer)
    requires out_w f = in_w g
    ensures in_w (seq f g) = in_w f && out_w (seq f g) = out_w g
  let axiom seq_lip (f : layer) (g : layer)
    requires out_w f = in_w g
    ensures lip (seq f g) <= lip f * lip g
  let axiom residual_shape (f : layer)
    requires in_w f = out_w f
    ensures in_w (residual f) = in_w f && out_w (residual f) = out_w f
  let axiom residual_lip (f : layer) @trigger(residual f)
    requires in_w f = out_w f
    ensures lip (residual f) <= 1.0 + lip f
end

let lemma block_bound (a : Lip.layer) (b : Lip.layer) : unit
  requires Lip.in_w a = 512 && Lip.out_w a = 512 && Lip.lip a <= 0.5
  requires Lip.in_w b = 512 && Lip.out_w b = 10 && Lip.lip b <= 2.0
  ensures Lip.lip (Lip.seq (Lip.residual a) b) <= 3.0
= ()
```

**What a theory holds.**

- `let sort s` declares a new uninterpreted sort, and `let sort s = t` is another name for the type `t`.
- `let spec f : (a : t) -> r` is an abstract function, with no body. Its parameters are named.
- A `let spec` with a body defines a spec function as usual.
- `let axiom name params requires ... ensures ...` states a fact for all values of its parameters. It has no body.
- A `let lemma` is proved from the axioms, as any lemma is.

`theory`, `sort` and `axiom` are keywords only between `let` and a name, like `spec` and `lemma`.

**Names.** Inside its theory, a member is used unqualified (`lip f`, `layer`). Everywhere else it is `T.x`: `Lip.lip`, `Lip.layer`. An interface lists functions and types, not theories, so a module cannot import another's theory yet ([ADR 0039](adr/0039-module-and-interface-syntax.md)): a theory is used in the file that declares it, and `import T` of such a theory does nothing. A module header's `@trusted` (`module M @trusted`) marks the file like a `@trusted` line. A name the theory does not declare is an error (`the theory 'Lip' has no 'nope'`). A member cannot shadow a name that is visible inside the theory, such as another item, a core builtin like `len`, or a builtin type. A parameter of a member cannot take a member's name either ([ADR 0022](adr/0022-metaprogram-hygiene.md)).

**Spec-only.** A theory's sorts and functions are spec-only, like `int` and `real`. Code cannot compute with them, but it can hold a sort's value in a spec-only parameter, local or field, which is how an allocator tracks `Alloc.heap` (ADR 0041). Codegen erases the theory along with every contract and spec-only value that uses it. A sort has only `=` and `<>`.

**Models.** A model gives each sort of a theory a type and each abstract function a definition:

```ocaml
let summary = type { in_w : usize; out_w : usize; lip : real where lip >= 0.0 }

let model shapes : Lip = struct
  let sort layer = summary
  let spec in_w (f : summary) : usize = f.in_w
  let spec out_w (f : summary) : usize = f.out_w
  let spec lip (f : summary) : real = f.lip
  let spec seq (f : summary) (g : summary) : summary =
    { in_w = f.in_w; out_w = g.out_w; lip = f.lip * g.lip }
  let spec residual (f : summary) : summary =
    { in_w = f.in_w; out_w = f.out_w; lip = 1.0 + f.lip }
end
```

A model must define every sort and every abstract function of its theory, and nothing else, and each function must have the theory's type with the theory's sorts replaced by the model's. `model` is a keyword only in `let model m : T`. Inside the model its members are used unqualified, and they are `m.x` elsewhere.

**The model check.** Each axiom of the theory, with the model's types and functions in place of the theory's, becomes a lemma `m.a`, which is proved like any lemma and reported as `the model 'shapes' meets the axiom 'Lip.seq_lip'`. If every one is proved, the theory is consistent: whatever its axioms prove is true in the model. A model that breaks an axiom fails verification, with a counterexample in the model's values.

**Field refinements.** A record field may carry a refinement, `lip : real where lip >= 0.0`, in which the field's name stands for the field. It is an implicit `requires` on every parameter of that record type, and of records that contain it, and an implicit `ensures` on every result. So a function that builds the record proves the refinement, and one that takes it may assume it. Models need this: `lip_nonneg` holds in `shapes` because every `summary` has `lip >= 0.0`.

**Sealing.** A client of the theory, such as the lemma `block_bound`, uses `Lip.lip` and the other abstract functions, never the model's. Its queries get the axioms and do not even declare the model's functions. So a fact true in the model but not stated as an axiom cannot be used, and changing a model's definitions does not change a client's proofs. A theory lemma is proved from the axioms in the same way.

**Counterexamples in the model.** A goal over a modelled theory is first tried in a copy of its function, called its witness, in which the model's types and functions stand for the theory's. There everything is concrete, so the solver decides it quickly. If it is false there, the model is a counterexample to the axioms as well, since the model meets them, and the report says so:

```
levels.pia:45:3: failed: the postcondition holds
  counterexample in the model 'bits': h = 0
```

A goal with no parameters reports `false in the model 'm'`. A model's counterexample is reported only when the witness query is complete: if it stopped unfolding a recursive spec function at its fuel, the function is uninterpreted past that point, so the model may give it a value its definition does not, and the goal is decided over the axioms instead (#188). Any failed goal whose query stopped at the fuel says so, with `hint: a recursive spec function was unfolded only as far as its @fuel allows ...`, since raising `@fuel` or proving the fact by induction may prove it. If the goal holds in the witness, it is decided over the axioms as above, with the fallback, so a goal that is true in the model but not proved by the axioms still fails. A witness is made for lemmas and spec functions that use a modelled theory, except those that use a theory member a model does not define, such as a theory lemma. This matters for speed: the queries over the axioms have quantifiers, and with them Z3 can search a long time for a counterexample that a concrete model gives at once.

**Trust.** Without a model, nothing proves that a theory's axioms are consistent. So a theory with axioms and no model in the program needs its file marked `@trusted`, on a line of its own, and every axiom is a trusted item. A theory with a model needs neither, and none of its axioms is trusted. `piac --verify --trust-report` lists the trusted axioms:

```
lip.pia:16:3: the theory 'Lip' is consistent: the solver found a witness, a model of its axioms
lip.pia:16:3: trusted: the axiom 'Lip.lip_nonneg', since the theory 'Lip' has no model
...
5 trusted items
```

**`assume` needs `@trusted` too.** Nothing checks an `assume p`, so it is allowed only in a file marked `@trusted` ([ADR 0023](adr/0023-minimal-core-self-hosted-stdlib.md)); anywhere else it is an error that suggests `assert`, a lemma or a `requires` instead. (`addr`, the other construct ADR 0023 restricts, does not exist yet.) Each `assume` is a trusted item. Its assertion is tracked in the unsat core like an axiom's, so `--why` lists the goals whose proofs used it, and the callers of a function whose proof did:

```
next.pia:11:3: trusted: the 'assume' in 'next'
  used by: next.pia:12:5, next.pia:21:3
...
2 of 5 proved goals rest on a trusted axiom or 'assume'; the other 3 are fully proved
```

A goal whose query asserts an `assume` is solved a second time, tracked, to find its core, as for axioms. Files without `assume` are solved exactly as before.

**Consistency of a trusted theory.** A trusted theory is checked once, when its file is verified: are its axioms, with the axioms of other theories they use (by the relevance closure), satisfiable, under the usual rlimit? The answer is in the trust report. `sat` means Z3 found a witness, a model of the axioms, so they cannot contradict each other. `unknown` leaves the theory unchecked, and the report says so with the solver's reason. `unsat` is an error that names the axioms that contradict each other, from the unsat core:

```
bad.pia:6:3: failed: the axioms of the theory 'Bad' are consistent [they contradict each other: Bad.one, Bad.zero]
```

A theory with a model needs no check: the model is the witness, and its check proves it.

**Which axioms a goal used.** With `--verify-stats`, `--trust-report`, `--check-vacuity` or `--proof-cache`, a goal proved with theory axioms (or an `assume`) is solved a second time with each axiom tracked, and the unsat core of that run names the axioms the proof used. The first run is untracked, because tracking slows the search for a counterexample. Only queries with axioms are solved twice, so every other query is solved exactly as before. Without those flags nothing reads the core, so the second solve is skipped: it can cost far more than the proof (about 30 seconds against 1.5 for `tests/verify/size_classes.pia`), and the goal records every axiom it was given instead. The proof cache keeps each core, so a run with `--proof-cache` still tracks. The core is kept in the goal's proof cache entry, as a line `axioms <name>,...` after `proved <cost>`. `--verify-stats` adds `used=...` to each such goal's line. `piac --verify --trust-report --why` lists, under each trusted axiom, the goals that used it. A call to a lemma assumes what the lemma proved, so a goal also rests on the axioms of every lemma its function calls, transitively. The report ends with how many proved goals rest on a trusted axiom. The others are fully proved, even in a file that trusts a theory:

```
trust_checks.pia:16:3: trusted: the axiom 'Good.f_small', since the theory 'Good' has no model
  used by: trust_checks.pia:32:38, trust_checks.pia:38:39
trust_checks.pia:17:3: trusted: the axiom 'Good.g_small', since the theory 'Good' has no model
  used by no proved goal
...
2 of 3 proved goals rest on a trusted axiom; the other 1 are fully proved
```

**Vacuity, opt-in.** A consistent theory can still contradict a goal's own hypotheses: with the axiom `f x < 10`, a lemma that `requires f x > 20` proves anything. So can an `assume` that cannot hold. `piac --verify --check-vacuity` ([ADR 0036](adr/0036-library-theories.md), step 7) finds such proofs. Each goal proved with a trusted axiom or an `assume` is solved again from its hypotheses alone, the same query without its negated goal. If they are unsatisfiable, the goal was proved from a contradiction, and that is an error naming the trusted items in the unsat core:

```
vacuity.pia:25:3: proved: the postcondition holds [smt]
vacuity.pia:25:3: failed: the proof is not vacuous [its hypotheses contradict each other, so 'the postcondition holds' was proved from a contradiction: Good.f_small]
vacuity.pia:30:3: failed: the proof is not vacuous [its hypotheses contradict each other, so 'the postcondition holds' was proved from a contradiction: the 'assume' at vacuity.pia:31:3]
```

A goal whose proof used nothing trusted is not checked: if its own preconditions contradict each other, that is the contract's business, and a goal in unreachable code is proved for the same reason. A vacuous goal is not proved, so its op is not marked proved and codegen refuses it like any failed goal. Finding a contradiction is usually quick, but showing that hypotheses with quantified axioms are satisfiable can mean a long search for a model. So each check has a budget of its own, ten times the resource count of the goal's proof and at least a million, within `--solver-rlimit`. A check the budget cannot decide leaves the goal proved, and piac prints a note with how many there were. The check costs one more query per goal it checks, which `--verify-stats` reports as `verify-stats-vacuity: checks=N vacuous=V unknown=U cost=C`. It is meant for CI and audits, not for every edit.

**`import M trusting`.** An importer accepts a trusted theory as a whole with `import M trusting`. There is no list of axioms to grant, and it is written only in the source, so it works the same in a file and in the REPL. `trusting` is a keyword only at the end of an import. Interfaces do not carry theories yet, so today the only theory a module can name in an import is its own, where `import T trusting` changes nothing: T is trusted there already. The grant is recorded, and the trust report lists it (`trusting the theory 'Ideal'`). The check that an import of another module's trusted theory needs `trusting` comes when interfaces can export theories.

**Encoding.** A sort is an uninterpreted SMT sort named after it (`(declare-sort Lip.layer 0)`), and an abstract function is a `declare-fun` under its qualified name (`Lip.lip`). The function's result is assumed to lie in its type's range. An axiom is an `smt.forall` over its parameters, `requires ==> ensures`, with each trigger as a pattern. The export cannot name an assertion, so the verifier adds the name afterwards as `(assert (! ... :named |Lip.seq_lip|))`. An axiom with several triggers is asserted once per trigger, under `|Lip.residual_lip#2|` and so on, since the export writes the terms of one quantifier as a single pattern.

**Triggers.** The solver instantiates an axiom where a term matches one of its triggers. `@trigger(seq f g)` sets one, and `@trigger(t1, t2)` sets a pattern of several terms that together mention every parameter. Otherwise `piac` infers them as Z3 would: every smallest call of a theory function that mentions all the parameters. It leaves out a term that would loop, one where the axiom holds a larger instance of it. An example is `in_w f` in `residual_shape`, which also holds `in_w (residual f)`: each instance would make the next, so the trigger chosen is `residual f`. An axiom with no such term is an error at its definition. `--verify-stats` prints each axiom's triggers:

```
verify-stats-axiom: Lip.seq_lip triggers=(Lip.seq f g)
verify-stats-axiom: Lip.residual_lip triggers=(Lip.residual f)
```

**Only the axioms a goal needs.** A query starts with the theory functions its goal's walk applies. An axiom is added when every function in one of its triggers is in the query. The functions it brings can add more, until nothing changes. A query that applies no theory function gets nothing, so it is the same, byte for byte, as without theories. Leaving out an axiom only removes a hypothesis, so a proof found this way is a proof. If the goal is not proved, it is solved again with every axiom of every theory whose functions it mentions, and the counterexample comes from that run, so it is never spurious because an axiom was missing. The proof cache keys that run by its own query. `--verify-stats` prints the axioms each goal was given, and marks the goals that needed the fallback:

```
verify-stats-goal: lip.pia:31:3 axioms=Lip.lip_nonneg,Lip.seq_shape,Lip.seq_lip,Lip.residual_shape,Lip.residual_lip
verify-stats-goal: closure.pia:33:45 axioms=Counter.value_small,Counter.label_one fallback=all
```

These lines have their own prefixes, so `tools/bench` still reads the single `verify-stats:` line.

**Not yet.** These come in the ADR's later steps:

- models in another module, found by the ADL rule, and the `trusting` check on imports between modules, once modules can import one another;
- trust recorded in proof certificates ([ADR 0024](adr/0024-published-proof-certificates.md)), which are not built yet;
- `--check-vacuity` (step 7).

A counterexample over the axioms shows a value of a sort as Z3 names it (`b = Lip.layer!val!0`). It does not yet show the theory functions' values at it.

## `spread`

A `spread i in lo .. hi do ... done` runs its iterations at the same time ([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md)). The verifier walks one arbitrary iteration, as for a `for` loop, and adds a goal at every access to a buffer the body writes: the iteration owns the cell. By default iteration `i` owns cell `i`; `@owns(buf, owner)` on the `spread` gives the cells of `buf` with `owner.[c] = i` instead. These goals imply that no two iterations touch the same cell, since an owner is a function, so no goal compares two iterations. The body may not assign a variable declared outside it, and may only index a buffer it writes.

A `spread`'s `ensures p` is proved at the end of one iteration, after every cell that another iteration owns has been given an unknown value, so it holds whatever the other iterations write; after the loop, `forall (i in lo .. hi). p` is a fact. A function with `@owns(buf, owner, b)` after its return type touches only the cells of `buf` with `owner.[c] = b`: every access to `buf` in it is that goal. A `spread` may pass a buffer it writes to such a function, if its own `@owns` names the same owner, and the call's goal is that its `b` is the iteration (tests/verify/spread.pia, tests/verify/spread_ensures.pia, tests/irgen/spread_errors.pia).

A spec function over a buffer may say which cells it reads, `reads xs.[lo .. hi]` ([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md), section 3). piac then writes its frame lemma `f'frame`, for two buffers that agree on the footprint `f` gives the same result, and proves it by induction on `f`'s own `decreases`, asserting that every element `f` reads is in the footprint. Where a buffer changes outside a framed call's footprint, by a store or by a `spread`'s forgetting of the cells other iterations own, the verifier states that the call on the new contents equals the call on the old, so a sum over a range survives writes elsewhere with no lemma by hand (tests/verify/frames.pia).

## Solver strategies and tactics

Two ways to help a proof the solver cannot find, or finds slowly ([ADR 0036](adr/0036-library-theories.md), step 6). Neither can make a wrong proof.

**`@solver(...)`** on a lemma, a function or a theory chooses the Z3 strategy for its goals. `@solver(nlsat)` uses Z3's strategy for nonlinear real arithmetic (`qfnra-nlsat`), and any other name is one of Z3's tactics, such as `@solver(smt)`. `@solver(tactic = "...")` takes a combination in SMT-LIB's syntax for `check-sat-using`: `(then t1 t2 ...)`, `(or-else ...)`, `(par-or ...)`, `(par-then ...)`, `(repeat t n)`, `(try-for t ms)` and `(using-params t :key value ...)`. An unknown tactic is a compile error. On a theory, `let theory T @solver(nlsat) = sig ... end`, it applies to each member without its own `@solver`, and to the checks of its model and of its consistency. `--dump-smt` shows the strategy as `(check-sat-using ...)`.

```ocaml
let lemma product (x : real) (y : real) : unit @solver(nlsat)
  requires x > 1.0 && y > 1.0
  ensures x * y > 1.0
= ()
```

A strategy changes only how a query is solved. Any tactic Z3 runs is sound, so `unsat` is still a proof, and a strategy that gives up leaves the goal failed, never proved. The strategy is part of the proof cache's key, so a goal proved one way is not taken as proved another way. The unsat core that says which axioms or `assume`s a goal used ([Trust](#theories)) is still found with Z3's default solver.

**Tactics.** `@by(t args)` on a lemma runs the metaprogram `t` on the lemma's goal and returns proof steps, which go before the lemma's body and are proved like steps written by hand ([meta.md](meta.md#tactics)):

- a lemma call, `l x`, whose precondition is a goal and whose postcondition is known afterwards;
- an `assert p`, a goal that is known afterwards;
- a case split, `if c then assert p else assert p`;
- an instance of a quantified fact, as a lemma call or an `assert` at particular arguments;
- `fuel n`, a hint rather than code: it puts `@fuel(n)` on the lemma, which unfolds every spec function at least `n` levels in the lemma's goals. `@fuel(n)` can also be written on a lemma by hand.

A tactic must terminate and be pure, by the rules for type-level metaprograms ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md)), so what a proof means never depends on a step budget or on the rest of the program. This is the LCF approach: the tactic is outside the trusted base, since everything it writes is checked. [theories.md](theories.md#clocks-a-proof-written-by-a-tactic) shows a tactic that writes a proof by induction.

**Proof by reflection** is not implemented yet. It needs a datatype of formulas, and recursive types are not supported yet ([status.md](status.md)). The plan is in ADR 0036: a total spec function `decide : formula -> bool` with a soundness lemma `decide f ==> eval f` proved once, and a tactic that reifies the goal into a `formula` and proves it from `decide f = true`.

## Generic functions

A generic function is proved once at its definition, over its type parameters, and its instances are then proved by that proof ([ADR 0043](adr/0043-generic-definitions-proved-once.md), steps 1 and 2).

- **Encoding.** The definition check ([ADR 0034](adr/0034-concepts-and-overload-resolution.md)) generates the body with each type parameter as a stand-in, a record with no fields. When the body is parametric, that function is kept as the generic's proof, marked `pia.generic_proof`, with the instances it makes at the stand-ins (`lex_from<t>`). ScalarizeRecords sets these functions aside, and the verifier encodes each stand-in as an uninterpreted sort, `generic.t`, and a buffer of one as an array of that sort. Codegen erases them.
- **Concepts.** Each requirement of the constraints is an uninterpreted function of a theory named after the concept at the stand-ins, `Ord<t>.less` (in full, `Pia.Core.Order.Ord<t>` for an imported concept), so a call in code and one in a contract are the same term. Each requirement's contract, `Ord<t>.less.contract`, and each of the concept's laws, `Ord<t>.less_transitive.law`, is an axiom of that theory (step 3), with the relevance closure of any theory ([Theories](#theories)); a law whose hypotheses chain calls, like transitivity's, is triggered by all of them together, and one the solver could not instantiate is left out. None is trusted: the use check proves each at every type that meets the concept. A proof gets only the axioms of the concepts its own constraints promise.
- **Imported generics.** An importer does not prove an imported generic again: its module proved it, and a build of the module requires that (ADR 0039). The importer keeps the proof only to match its own instances against it, so they are discharged too. A generic over another module's concept calls the concept's functions by their own names, `same`, and an importer's instance finds them in the concept's module, `Pia.Core.Order.same`.
- **`old` in a lemma's arguments.** A lemma's arguments are spec, so they may name the state on entry: `exchange` asserts `swapped_count (old xs) xs i j (len xs)`, a spec function whose contract relates how often each value occurs before and after, and so ensures it keeps every count.
- **`old xs` as a spec argument.** A whole slice in its state on entry, `old xs`, may be passed to a spec function, as in `ensures result = kept (old xs) v (len xs)`: it is the slice's memory on entry with its length, which a slice keeps, so `len (old xs)` is `len xs`.
- **Spec facts at computed arguments.** A spec function's definition and its `ensures` are claimed of a call only where its proof covers them: its precondition holds and each integer argument the spec body computed, such as `k - 1`, is in its parameter's type. Spec arithmetic is exact, so unfolding `cnt xs (k - 1)` at k = 0 makes a call at -1, where `requires k <= len xs` holds; without the range, `ensures result <= k` there contradicted the result's type, and every goal in its scope was proved (tests/verify/spec_arg_range.pia). Parameters, loads and constants are in their types already.
- **Facts under an assumed quantifier.** The definitions and contracts of the functions a quantifier's body calls, instantiated at its bound variables, are hypotheses of the quantifier, and are also asserted on their own as a `forall`: they hold for every value, so this is sound whatever the quantifier's polarity, and an assumed `forall k. if same old.[k] v then ...` from a callee's contract then tells the caller about each element. Without it, the solver would have to prove `same`'s contract at each element before it could use the quantifier, which it cannot.
- **Closures with no captures.** A lambda that captures nothing, passed as a function object, is a record with no fields, which has one value: the verifier gives such a record an uninterpreted sort and one constant, so a spec function such as Search's `count_where` can take the closure, and the closure's `apply` unfolds to the lambda's body in a contract.
- **Imported functions in specs.** An imported function of scalars is, to the verifier, an uninterpreted function that meets its interface contract, since its body here is only that contract. So an imported spec function that calls one unfolds at the importer: `Pia.Core.Order.lex_from<u8>` calls Order's `less` on u8, whose contract says it is `<`, and an importer proves that the empty slice is before every other.
- **Equality.** `=` and `<>` on values of a type parameter, which contracts may write, are equality in its sort (a call of `pia.eq<t>` that the verifier encodes as SMT equality). Any model reads that as equality of the instance's values, so a proof that uses it holds at every instance.
- **Instances.** Generic proofs are solved first. When every goal of a generic's proof holds, each instance whose body is the generic's is not proved again: the report gives it one line, `proved: 'lex_compare<u8>' is an instance of the generic proof of 'lex_compare' [generic]`. An instance is the generic's body when its calls are the proof's, one for one: each call of a concept's function goes to a function that returns (no `while` without a measure, no recursion without one, and the same of what it calls), each call of another generic at the type parameters goes to that generic's instance, and every other call to the same function. A call that resolves to a more specific overload at the instance's types makes the instance a body of its own, proved at its types. So is an instance of a generic whose proof failed, was not selected by `--verify-only`, or fell back. Calls into an instance still prove its precondition at the call, as for any function. The types meet the concepts' laws and requirement contracts because the use check proves those at each type, and a failure there still fails the program.
- **Reports.** The proof's goals are reported at the generic's lines with `[generic]`. A generic with a false contract fails at its definition even if nothing instantiates it, with a counterexample over its sort (`a = generic.t!val!0`). `--verify-stats` adds `generic=`, the proof goals, and `instances=`, the instances its proofs discharged.
- **Fallback.** A generic the verifier cannot prove over sorts is proved only at its instances, and the report says why, as `not proved generically: 'f' is proved at each instance, since ...`. In step 1 that is a generic whose signature applies a type-level metaprogram to a type parameter, one with a `where` predicate that is not a concept, one whose concepts have a requirement with a precondition or a record result, and one that takes, makes or returns a value of another type built from a type parameter, such as `option t` or `pair a b`. So is any body that applies an operation other than a call, a return, an `if`, a loop, a load, a store, a slice or a length to a value of a type parameter. The classifier errs towards falling back, which is today's behaviour.

## Higher-order functions proved once

A higher-order function is proved once, like a generic (ADR 0044, step 6): its function parameters are values of types that meet a concept whose `apply` is uninterpreted and has the arrow's `ensures` as an axiom. Each specialisation at a lambda, a named function or a function object is reported as an instance of that proof, `'find[lambda@f.pia:12:9]' is an instance of the generic proof of 'find#proof'`. A law of a function parameter in a contract, `requires Pia.Fn.strict_weak_order less`, is part of the copy: it is applied to the abstract `apply`, and the law's spec function at the proof's stand-in and at an instance's argument count as the same call when the instance is discharged, so an insertion sort over any strict weak order is proved once and its instances at `a > b` or at Pia.Core.Order's `less` are discharged. A copy whose check or proof fails is reported as `not proved generically`, with the goal or error that stopped it, and its specialisations are proved each; a module with no specialisation of its own does not pass silently. A function the copy calls that is itself proved once is not proved again inside it: the call is discharged by that function's own proof, so a chain of such calls (`sort`, `make_heap`, `sift_down`) is proved once along the chain, and an importer's specialisations along it are each an instance of its proof. An arrow's `requires` is part of the copy too: a concept requirement's precondition is a goal at each call in a generic body, and its axiom holds where the precondition does, so `apply_twice (f : (y : u8) -> u8 requires y < 200 ensures result > y)` is proved once. Arrows with `inout`, and functions whose copy is not parametric, are still proved per specialisation.

## Choosing overloads by precondition

Overloads with the same parameter types are told apart by their preconditions (ADR 0034). IRGen leaves a call between them open: a `func.call` of the least specific one, with every candidate, most specific first, in `pia.overload_candidates`. Before verification and code generation, `resolveOverloads` decides each open call. For each candidate but the last, it encodes the calling function with the call retargeted to that candidate and asks whether each of its preconditions holds at the call, from everything known there: the caller's `requires`, the branches the call is under, loop invariants and earlier calls' `ensures`. The first candidate whose preconditions are all proved is called. If none is, the call keeps the least specific candidate, whose precondition is then an ordinary goal. This runs in every build, with or without `--verify`, and `--verify-only` does not limit it. Each query uses the proof cache like any goal.

## Limits of v0

- **Loops whose bounds or loop-carried values cannot be encoded** have every goal inside reported as `skipped`, and what they compute or write is unknown afterwards.
- **Termination is checked for direct recursion only.** Mutual recursion is not checked, since each call is taken on its callee's contract.
- **Affine goals in loops**, such as subscripts like `xs.[2*i + 1]`, aliasing and loop-carried dependence, still go to Z3. A Presburger stage will decide them first ([ADR 0020](adr/0020-presburger-for-affine-goals.md)).
- **A call to an ordinary function inside a contract** stands for a value that meets the callee's postconditions, and inside a quantifier for an unknown value. To say what a function means in a contract, use a [spec function](#spec-functions-and-lemmas).
- **Ops the verifier does not model** produce unknown values of their types, which is sound but may cause failures.
- **Interval analysis** is local to each goal. Extending MLIR's integer range analysis, so that ranges flow through control flow, comes later.
