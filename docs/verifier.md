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

**Records** are replaced with their fields before encoding ([irgen.md](irgen.md#records)). So a `pixel` parameter is four constants, and its counterexample values are named `p.r`, `p.g`, `p.b` and `p.a`.

**Calls** use the callee's contract, not its body. Its preconditions become goals, with the arguments substituted. The result is a fresh value of the result type. The callee's postconditions are assumed about it, with `old` reading the arguments as they were before the call. A callee that returns one of its parameters unchanged gives a result equal to that argument. Buffers the callee may write (`out` or `inout`) are fresh arrays afterwards. Recursion needs nothing special.

**`old e`** reads the function's arrays as they were on entry.

**Quantifiers.** `forall (i in lo..hi). p` becomes an SMT `forall` over the bound variable, `(type range && lo <= i && i < hi) ==> p`. `exists` conjoins the guard instead.

**Division.** Z3 bit-blasts division, and cannot show `a mod b < b` on 68-bit values within its timeout. So for non-negative operands the encoding states `0 <= a / b <= a` and `0 <= a mod b < b` (when `b` is not zero) beside the term. Inside a quantifier, where the operands may be bound variables, it does not.

**Timeouts.** Each obligation is one Z3 query with two limits. The one that decides is `--solver-rlimit=<n>`, Z3's deterministic resource count, which does not depend on load or on the machine's speed; piac defaults to 1,200,000,000. `--solver-timeout=<ms>` is a wall-clock safety net, 600 seconds by default. A wall-clock limit alone would depend on load: a goal that proves in 5 seconds alone can time out while other goals and builds share the cores, and that is the normal case now that goals are solved in parallel. (`pia repl` and `pia-lsp` still use a wall-clock limit, `--timeout-ms`, since they answer interactively.) `--solver-cost` verifies like `--verify` and prints each proved SMT goal's resource count, as `(cost N)`, so a limit can be chosen from measurements. A goal the solver gives up on is reported as failed, with the reason, such as `[the solver gave up: timeout]` or `[the solver gave up: max. resource limit exceeded]`. The `pia_object` Bazel rule passes `--solver-rlimit=1200000000`, about 20 times the costliest goal in the repository (`settle` in docs/streams.pia.md, 56,923,063), and a 600-second timeout that serves only as a safety net, so whether a build proves its goals does not depend on load.

**Counterexamples** name the parameters, using the names IRGen records in the block arguments' locations, and slice lengths as `len xs`. They add the values that explain the goal: `result` for an overflow, `index` and `length` for bounds. Array contents are not shown yet.

## Parallel, sliced and cached proving

Build time is a benchmark ([ADR 0032](adr/0032-parallel-sliced-cached-proving.md)). Goals are listed and encoded in walk order on one thread, then the SMT queries are decided on a pool of threads, one per core unless `--jobs=N` says otherwise, each in its own Z3 context. The report keeps the walk order, and under an rlimit every goal has the same result on any number of threads.

**Slicing** cuts a query to the goal's cone of influence: the negated goal, and every assertion that shares a symbol with one already kept, transitively. A precondition about `b` stays out of a goal about `x`. An `unsat` slice proves the goal, since only hypotheses were dropped. Otherwise the whole query is solved again, so slicing never stops a goal from proving, and a counterexample always comes from the full query. By default it is automatic, and only in a function with a buffer of records, which ScalarizeRecords marks `{pia.record_buffers}`. There, a goal is sliced when the slice drops a whole declaration, a symbol the goal cannot reach: one buffer per field means a goal about `xs.[3].a` is asked alongside quantified facts about `xs.g` and `xs.b` that it never needs. Those facts make Z3's search grow quickly with the number of fields. Copying four-field records through a view costs 777 million resource units in full and 1.6 million sliced. `--slice` slices every goal whose slice is smaller, and `--no-slice` always solves the full query. Elsewhere slicing costs more than it saves: applied to every query that drops a declaration, it raises the streams demo from 269 million resource units to 395 million, and forcing it with `--slice` gives 392 million and 47 seconds on one thread, against 269 million and 33 seconds without. Smaller queries are not always easier for Z3, and a goal whose slice is satisfiable is solved twice. With the rule limited to buffers of records, every file in the benchmark (tools/bench) costs what it did before. The benchmark keeps measuring it.

**Selecting goals.** `--verify-only=<spec>` proves only the goals the spec selects, and can be repeated:

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

A `while` loop or a recursive call with no measure gets a `skipped` goal ("the loop terminates", "the recursion terminates"). So `piac --verify` fails, and piac generates no code, unless `--allow-unproved` accepts it ([codegen.md](codegen.md)).

## Spec functions and lemmas

`let spec f ...` defines a spec function: pure and total, used to say what code means. Contracts, other spec functions and lemmas can call it. Code cannot, and codegen erases it. It cannot loop, write a buffer, `abort`, or call anything but spec functions. A recursive one needs `decreases`, and spec functions cannot be mutually recursive yet. Its body is checked like any function's: its own goals, its `ensures`, and its measure at each recursive call.

To the solver, `f` is an uninterpreted function `F` with one argument per scalar parameter and two, the array and its length, per buffer. A call `f a`, wherever it is, is `F a`, with these facts:

- `F a` is in the result type's range.
- `pre(a) ==> post(a, F a)`: f's postconditions, where its preconditions hold.
- `pre(a) ==> F a = body(a)`: the definition, unfolded once. A recursive call in the body is `F` again, with the two facts above but no definition. `@fuel(n)` on the return annotation unfolds n levels.

The definition is guarded by the precondition because termination is proved only where the precondition holds, so outside it the body could define `F` in terms of itself. Inside a quantifier, the facts for calls that mention the bound variables become hypotheses of the quantifier. A call that passes a view inside a quantifier is left uninterpreted, and so is a definition with a value the encoding cannot model.

A call in code to a spec function is a goal for its precondition, as for any call. In a contract, the call is checked the same way where it is walked, and is a plain term inside quantifiers and `old`.

`let lemma f ...` defines a lemma, which returns unit. It is proved once, like any function, and a call to it is a statement whose precondition is a goal and whose postcondition is assumed afterwards, by the usual rule for calls. Codegen erases lemmas and calls to them. A recursive lemma with `decreases` is a proof by induction:

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

Parameters of spec functions and lemmas cannot be `out`, `inout` or `mutable`. `spec` and `lemma` are keywords only between `let` (or `let rec`) and the name ([grammar.md](grammar.md#identifiers-and-keywords)).

## Spec-only `int` and `real`

Two types exist only for specifications ([ADR 0036](adr/0036-library-theories.md), step 1):

- **`int`**, an unbounded mathematical integer. Bare `int` is unbounded, and `int{lo..hi}` is still a range type: a range is written with its braces right after `int`, so the two spellings cannot be confused ([grammar.md](grammar.md)). The verifier encodes `int` as the SMT `Int` sort.
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

**Spec-only.** `int` and `real` may appear in spec functions, lemmas, contracts, quantifiers (`forall (y : real). y * y >= 0.0`), the arguments of a lemma call, and record fields that only spec code reads. Code may not compute with them. A parameter or result of an ordinary function whose type is or holds one, such as a record with a `real` field, is an error, and so is any expression of such a type in code. `let positive (x : u8) : bool = real x > 0.5` gives:

```
positive.pia:1:32: error: this expression has the spec-only type real; int and real can be used only in spec functions, lemmas, contracts and quantifiers, not in code (ADR 0036)
```

So codegen never sees them: it erases spec functions, lemmas and contracts, and with them every value of these types.

**Encoding.** `int` uses the upstream `smt` dialect's `Int` sort and its operations. The dialect has no `Real` sort at our LLVM pin, so the verifier extends it in the smallest way that keeps it the one encoding: `real` is written as a sort named `Real`, and the operations the dialect lacks (Real `+ - * /` and comparisons, `to_real`, and `bv2int` for converting a bit-vector) are declared as functions under their SMT-LIB names and applied with `smt.apply_func`. When the query is exported to SMT-LIB, those declarations and the sort's `declare-sort` are dropped, so Z3 reads each use as SMT-LIB's own interpreted symbol. A machine integer becomes an `Int` as `bv2int` of its bit-vector, less `2^w` when it is negative, since `bv2int` reads a bit-vector as unsigned. A real literal `n/d` is `(/ (to_real n) (to_real d))`.

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

**Spec-only.** A theory's sorts and functions are spec-only, like `int` and `real`. Code cannot take, return or compute them, and codegen erases the theory along with every contract that uses it. A sort has only `=` and `<>`.

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

A goal with no parameters reports `false in the model 'm'`. If the goal holds in the witness, it is decided over the axioms as above, with the fallback, so a goal that is true in the model but not proved by the axioms still fails. A witness is made for lemmas and spec functions that use a modelled theory, except those that use a theory member a model does not define, such as a theory lemma. This matters for speed: the queries over the axioms have quantifiers, and with them Z3 can search a long time for a counterexample that a concrete model gives at once.

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

**Which axioms a goal used.** A goal proved with theory axioms is solved a second time with each axiom tracked, and the unsat core of that run names the axioms the proof used. The first run is untracked, because tracking slows the search for a counterexample. Only queries with axioms are solved twice, so every other query is solved exactly as before. The core is kept in the goal's proof cache entry, as a line `axioms <name>,...` after `proved <cost>`. `--verify-stats` adds `used=...` to each such goal's line. `piac --verify --trust-report --why` lists, under each trusted axiom, the goals that used it. A call to a lemma assumes what the lemma proved, so a goal also rests on the axioms of every lemma its function calls, transitively. The report ends with how many proved goals rest on a trusted axiom. The others are fully proved, even in a file that trusts a theory:

```
trust_checks.pia:16:3: trusted: the axiom 'Good.f_small', since the theory 'Good' has no model
  used by: trust_checks.pia:32:38, trust_checks.pia:38:39
trust_checks.pia:17:3: trusted: the axiom 'Good.g_small', since the theory 'Good' has no model
  used by no proved goal
...
2 of 3 proved goals rest on a trusted axiom; the other 1 are fully proved
```

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

## Choosing overloads by precondition

Overloads with the same parameter types are told apart by their preconditions (ADR 0034). IRGen leaves a call between them open: a `func.call` of the least specific one, with every candidate, most specific first, in `pia.overload_candidates`. Before verification and code generation, `resolveOverloads` decides each open call. For each candidate but the last, it encodes the calling function with the call retargeted to that candidate and asks whether each of its preconditions holds at the call, from everything known there: the caller's `requires`, the branches the call is under, loop invariants and earlier calls' `ensures`. The first candidate whose preconditions are all proved is called. If none is, the call keeps the least specific candidate, whose precondition is then an ordinary goal. This runs in every build, with or without `--verify`, and `--verify-only` does not limit it. Each query uses the proof cache like any goal.

## Limits of v0

- **Loops whose bounds or loop-carried values cannot be encoded** have every goal inside reported as `skipped`, and what they compute or write is unknown afterwards.
- **Termination is checked for direct recursion only.** Mutual recursion is not checked, since each call is taken on its callee's contract.
- **Affine goals in loops**, such as subscripts like `xs.[2*i + 1]`, aliasing and loop-carried dependence, still go to Z3. A Presburger stage will decide them first ([ADR 0020](adr/0020-presburger-for-affine-goals.md)).
- **A call to an ordinary function inside a contract** stands for a value that meets the callee's postconditions, and inside a quantifier for an unknown value. To say what a function means in a contract, use a [spec function](#spec-functions-and-lemmas).
- **Ops the verifier does not model** produce unknown values of their types, which is sound but may cause failures.
- **Interval analysis** is local to each goal. Extending MLIR's integer range analysis, so that ranges flow through control flow, comes later.
