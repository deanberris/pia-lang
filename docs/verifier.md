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
| `nooverflow` | `pia.add`, `sub`, `mul`, `div` and narrowing `pia.convert` in `overflow(proof)` mode, which is the default. Also `pia.to_index` on a signed type (the index is not negative) and `pia.from_index` to a type narrower than `usize`. |
| `nonzero` | the divisor of `pia.div` and `pia.rem`, in every mode |
| `inbounds` | `pia.load` and `pia.store`: `0 <= i < len` |
| `assert` | `assert p` |
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

**Integers are bit-vectors.** Every Pia integer is a signed bit-vector of one width per module: 68 bits, or 132 if the module multiplies. That is wide enough for the exact result of any operation on values in `[-2^63, 2^64 - 1]`, so the encoding never wraps by accident. Ranges are constraints on these bit-vectors. `wrap` reduces into the type with `bvsmod`, and `saturate` clamps with `ite`. `index` uses the same sort.

**Booleans** are SMT booleans. In contracts `&&`, `||` and `==>` are already plain logic. In code they arrive as `scf.if`, which becomes `ite`.

**Arrays and slices** are SMT arrays from index to element. A fixed array's length is its type's. A slice's length is a constant in `[0, 2^64 - 1]`. `pia.store` produces a new array term. After an `if`, the two branches' arrays merge with `ite`. Every loaded element is assumed to lie in its element type's range.

**Control flow.** The two branches of `scf.if` are walked under the condition and its negation, and the results merge with `ite`.

**Records** are replaced with their fields before encoding ([irgen.md](irgen.md#records)). So a `pixel` parameter is four constants, and its counterexample values are named `p.r`, `p.g`, `p.b` and `p.a`.

**Calls** use the callee's contract, not its body. Its preconditions become goals, with the arguments substituted. The result is a fresh value of the result type. The callee's postconditions are assumed about it, with `old` reading the arguments as they were before the call. A callee that returns one of its parameters unchanged gives a result equal to that argument. Buffers the callee may write (`out` or `inout`) are fresh arrays afterwards. Recursion needs nothing special.

**`old e`** reads the function's arrays as they were on entry.

**Quantifiers.** `forall (i in lo..hi). p` becomes an SMT `forall` over the bound variable, `(type range && lo <= i && i < hi) ==> p`. `exists` conjoins the guard instead.

**Division.** Z3 bit-blasts division, and cannot show `a mod b < b` on 68-bit values within its timeout. So for non-negative operands the encoding states `0 <= a / b <= a` and `0 <= a mod b < b` (when `b` is not zero) beside the term. Inside a quantifier, where the operands may be bound variables, it does not.

**Counterexamples** name the parameters, using the names IRGen records in the block arguments' locations, and slice lengths as `len xs`. They add the values that explain the goal: `result` for an overflow, `index` and `length` for bounds. Array contents are not shown yet.

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

## Limits of v0

- **Loops whose bounds or loop-carried values cannot be encoded** have every goal inside reported as `skipped`, and what they compute or write is unknown afterwards.
- **Termination is checked for direct recursion only.** Mutual recursion is not checked, since each call is taken on its callee's contract.
- **Affine goals in loops**, such as subscripts like `xs.[2*i + 1]`, aliasing and loop-carried dependence, still go to Z3. A Presburger stage will decide them first ([ADR 0020](adr/0020-presburger-for-affine-goals.md)).
- **A call inside a contract** stands for an unknown value of its result type, so a contract that relies on another function's meaning cannot be proved yet.
- **Ops the verifier does not model** produce unknown values of their types, which is sound but may cause failures.
- **Interval analysis** is local to each goal. Extending MLIR's integer range analysis, so that ranges flow through control flow, comes later.
