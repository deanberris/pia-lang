# 38. Float kernels are proved against real-valued specifications by rounding-error bounds

Date: 2026-11-22

Status: Accepted (2026-11-22, with Dean's answers to its questions below)

## Context

[ADR 0036](0036-library-theories.md) lets libraries reason in real arithmetic: a layer's Lipschitz bound is a `real`, a probability is a `real`, and the [catalogue](../theories.md) keeps its examples in integers, booleans and reals. Code computes in `f32`, `f16` and `bf16`. When Dean accepted ADR 0036, he asked for a separate ADR on how a float kernel is proved against a real-valued theory.

What exists today:

- Floats are strict IEEE 754 by default ([ADR 0004](0004-strongest-guarantee-by-default.md)), and the verifier can encode them in Z3's bit-precise floating-point theory ([ADR 0011](0011-mlir-and-z3-implementation.md)). That is exact, and it does not scale past a few operations.
- [ADR 0012](0012-floating-point-reassociation.md) offers three licences for reassociation and FMA. One of them is an error tolerance written in `ensures`, under strict IEEE semantics, "proved by a rounding-error analysis pass". That pass was never designed.
- Device placement ([ADR 0015](0015-device-placement.md)) can move a kernel to the GPU or the Neural Engine, whose float behaviour differs from the CPU's: subnormals may be flushed, and some operations are not correctly rounded.

Prior art: Higham's standard model of floating-point arithmetic and its γₙ bounds; Gappa and Frama-C/Why3, which prove such bounds with interval reasoning; FPTaylor, Daisy and Rosa, which compute bounds automatically; and Fluctuat's abstract interpretation of errors.

## Decision

### Floats are related to reals by a rounding theory

Two spec builtins connect the types:

- `to_real (x : f32) : real` is the value of a finite float (SMT `fp.to_real`), and `finite x` says `x` is neither infinite nor NaN. The same exist for `f16`, `bf16` and `f64`.
- `eps t` is the unit roundoff of float type `t` (2⁻²⁴ for `f32`, 2⁻¹¹ for `f16`, 2⁻⁸ for `bf16`), and `tiny t` is the absolute error of its subnormal range (half the smallest subnormal).

The library `Pia.Float.Error` is a theory in the sense of ADR 0036. It gives the standard model as an abstract `round`:

```ocaml
let theory Rounding = sig
  let spec round : (t : type) -> (x : real) -> real
  let axiom standard (t : type) (x : real)
    ensures abs (round t x - x) <= eps t * abs x + tiny t
end
```

Its model is the identity, so it is consistent and nothing is trusted. Its *meaning* comes from the compiler: in an error goal, the verifier encodes `fadd a b` at type `t`, with round-to-nearest, as `round t (to_real a + to_real b)`, and likewise for `-`, `*`, `/` and `sqrt`. IEEE 754 guarantees that this holds for finite results. That encoding is part of the compiler's trusted base, as the meaning of `+` on `u8` already is. An FMA is one `round` of `a * b + c`. Operations that are exact, such as `max`, `abs`, negation, comparison and multiplication by a power of two without overflow, are encoded without `round`. That is why ReLU costs no error.

### A tolerance contract

A kernel states its result against a real-valued spec function, with a bound:

```ocaml
let spec dot_r (xs : [f32]) (ys : [f32]) (n : usize) : real
  requires n <= len xs && n <= len ys
  decreases n
= if n = 0 then 0.0 else dot_r xs ys (n - 1) + to_real xs.[n - 1] * to_real ys.[n - 1]

let dot (xs : [f32]) (ys : [f32]) : f32
  requires len xs = len ys && len xs <= 4096
  requires forall i, i < len xs ==> abs xs.[i] <= 1.0e3 && abs ys.[i] <= 1.0e3
  ensures finite result
  ensures abs (to_real result - dot_r xs ys (len xs))
          <= gamma f32 (len xs) * dot_abs xs ys (len xs) + error_floor f32 (len xs)
= ...
```

`gamma t n = n * eps t / (1 - n * eps t)` is Higham's γₙ, and `dot_abs` is the same sum over absolute values. Both are spec functions in `Pia.Float.Error`. `error_floor` covers subnormals.

A goal of this kind is proved in three layers, cheapest first:

1. **Ranges and finiteness by interval analysis** (ADR 0011's first stage, extended to floats): every intermediate is bounded, so `finite result` and the absence of overflow are proved without Z3 in the common case. An overflow is a failed goal, and its counterexample gives input magnitudes.
2. **Per-operation error** for straight-line code: each operation gets a fresh `δ` with `|δ| <= eps t` (from `standard`), and the goal is a nonlinear real query that Z3's `nlsat` decides for small kernels. Interval bounds from the first layer are added as hypotheses, so the query has only a few products.
3. **Library lemmas for loops.** A reduction is never unrolled. `Pia.Float.Error` proves, once and by induction (spec functions and lemmas with `decreases`, [PR #133](https://github.com/deanberris/pia-lang/pull/133)), the classical bounds for summation, dot products, matrix-vector products and Horner evaluation. A loop states the accumulated bound in its invariant and calls the step lemma. The query per goal stays the size of one iteration.

The bit-precise FP theory stays available for a goal that asks for it with `@solver(fp_exact)`, for single operations and tests of the encoding itself.

### Reassociation keeps tolerance contracts valid

The γₙ bounds for summation hold for every association order. So a kernel under `@fp(reassoc)` (ADR 0012), whose tiled or vectorised code sums in another order, keeps the same tolerance contract, and the proof uses the order-free lemma. This is how ADR 0012's licences and tolerance contracts compose: the licence lets codegen reorder, and the tolerance says by how much the result may then differ from the real value. FMA contraction only removes roundings, so it never invalidates a bound.

### Theories over reals, kernels over floats

A real-valued theory meets float code at the abstraction function (ADR 0036, "Connecting a theory to code"). For Lipschitz bounds, the float kernel is not exactly Lipschitz, because rounding errors do not shrink with the distance between inputs. What holds is a bound up to an error: if `|f̂ x - f x| <= e` for all `x` and `f` is `L`-Lipschitz, then `|f̂ x - f̂ y| <= L |x - y| + 2e`. The network theory therefore tracks a pair, `lip` and `err`, and composes both:

```ocaml
let axiom seq_err (f : layer) (g : layer)
  requires out_w f = in_w g
  ensures err (seq f g) <= lip g * err f + err g
let axiom residual_err (f : layer)
  requires in_w f = out_w f
  ensures err (residual f) <= err f + add_err (in_w f)
```

`add_err` is the error of the residual's own addition, from the per-operation rule. The summary model of ADR 0036 extends with an `err` field, and these axioms are proved in it as before. A dense kernel's tolerance contract supplies `err` for its layer, and ReLU's is 0.

### Mixed precision and devices

The rounding theory is indexed by type, so a kernel with `bf16` weights and `f32` accumulation is encoded exactly: a `bf16` value converts to `f32` without rounding, and then each product and each accumulation step is one `round f32`. Rounding a result down to `bf16` adds one `round bf16`, and the γ bounds use the `eps` of the type each step rounds to.

Each placement target has a float model, part of the placement contract of ADR 0015. The CPU's (NEON on Apple Silicon) is strict IEEE with subnormals, since Pia never sets flush-to-zero. A GPU or Neural Engine model states its own `eps`, its absolute error for flushed subnormals, and the operations it does not round correctly, with their error in ulps. A kernel with a tolerance contract may only be placed on a device whose float model proves that contract, and the placement report says which devices were excluded and why. A device's float model is a trusted theory where its vendor does not document correct rounding, so it is listed like any other.

### Build time

Error goals are new goals, so they go through ADR 0032's pool and proof cache like any other. The interval layer settles finiteness without solver queries in most kernels. Loops cost one iteration's query, because their bounds come from proved library lemmas. The standard library's float kernels join the proof benchmark, so a bound that becomes expensive shows up as a resource-count regression.

## Consequences

- A float kernel can be proved to approximate a real-valued specification with an explicit bound, and real-valued theories (network bounds, probabilities, control envelopes) can be used to reason about float code through those bounds.
- Tolerance contracts survive vectorisation and reassociation, so the fast code and the proved contract are the same code.
- The compiler's encoding of float operations as `round` of the real operation becomes part of the trusted base. It is the IEEE 754 standard's own promise, and it is tested against the bit-precise encoding with `@solver(fp_exact)` on single operations.
- Bounds are worst-case and can be pessimistic for long reductions. Tighter, probabilistic bounds would be a later theory, not a change to this one.
- Devices that flush subnormals or do not round correctly need float models before kernels with tolerance contracts can run on them.
- Implementation order, each step a PR with tests: (1) `to_real`, `finite`, `eps`, `tiny`, the `Float` concept with adapters for the builtin types, and float intervals in the interval stage; (2) the `round` encoding of operations in error goals, with per-operation `δ` and `nlsat`; (3) `Pia.Float.Error` with γₙ and the summation, dot product and matrix-vector lemmas; (4) order-free bounds under `@fp(reassoc)`; (5) device float models in placement; (6) the `~=` ... `within` form and derived bounds published in interfaces; (7) the `approximate` theory builder for `Composable` theories, with the network theory as a catalogue entry; (8) a block format (such as an MX format) as a `Float` type, as a worked example. Steps (1) to (3) need ADR 0036's steps 1 to 3 first.

## Answers to the review questions

Dean accepted this ADR on 2026-11-22 and answered its three questions. These answers are part of the decision.

### 1. A dedicated tolerance form, for any float format that meets a concept

A tolerance is written with its own form, not with helpers:

```ocaml
ensures result ~= dot_r xs ys (len xs) within gamma f32 (len xs) * dot_abs xs ys (len xs)
```

- **Meaning.** `a ~= e within b` means `finite a && abs (to_real a - e) <= b`, where `a` is a float-format value, `e` is a `real` and `b` is a `real`. `≈` is accepted as another spelling of `~=`. `~` is otherwise only prefix bitwise not, and no expression starts with `=`, so lexing `~=` as one token is unambiguous ([grammar.md](../grammar.md)).
- **The bound is optional.** Without `within`, `result ~= e` asks for the bound the verifier derives. The report shows the derived bound, and the contract that is published states it. That is the automatic error term of question 2.

The form is not tied to the builtin float types. It works for any type that meets the `Float` concept of `Pia.Float.Error` ([ADR 0034](0034-concepts-and-overload-resolution.md)):

```ocaml
let meta Float (t : type) : concept = sig
  let spec to_real : (x : t) -> real
  let spec finite : (x : t) -> bool
  let spec rel : real                       \ relative error of one rounding
  let spec abs_err : (scale : real) -> real \ absolute error at a given scale
  let spec round : (x : real) -> (scale : real) -> real
  let lemma standard (x : real) (scale : real)
    requires abs x <= scale
    ensures abs (round x scale - x) <= rel * abs x + abs_err scale
end
```

- **`f32`, `f16`, `bf16` and `f64`** meet `Float` through adapters in the library. `scale` doesn't affect their error (`abs_err` is the subnormal term `tiny t`).
- **Block formats** fit the same concept. Examples are device-specific formats with a shared exponent per block, such as microscaling (MX) formats, block floating point on a Neural Engine, or a vendor's packed GPU type. Each one is a Pia type: a record of the shared exponent and the element mantissas, with an adapter for `Float` on its element view. For a block format the error is absolute, relative to the block's largest magnitude, so `abs_err scale` carries it and `scale` is the block's maximum. The `≈ within` form, the per-operation encoding and the γ lemmas are all written over the concept, so a kernel over a block type is proved the same way as one over `f32`.
- **Proving `standard`.** An adapter proves it like any law, from a model of the format's encoding. When the format belongs to hardware whose rounding isn't documented, the adapter's `standard` comes from a trusted theory ([ADR 0036](0036-library-theories.md)). It is then imported with `trusting` and listed in `--trust-report`, as the device float models below are.

### 2. An automatic error term

- **Kernels.** A kernel whose contract says `result ~= e` without `within` gets its error bound derived by the verifier. The derivation uses the per-operation model, the interval bounds and the γ lemmas, and the derived bound is published in the kernel's interface. A caller's goals use that published bound, so error propagates through calls without being written at each one.
- **Theories.** A theory used by float code through an abstraction function gets an error term without the author writing one. When a theory meets the prelude concept `Composable` (a sort, `seq`, and a Lipschitz bound `lip` with the usual composition axioms), the prelude theory builder `approximate` (ADR 0036, step 5) generates:
  - an `err` function;
  - the axioms `err (seq f g) <= lip g * err f + err g` and `err (residual f) <= err f + err_add`, plus one for each other combinator the theory declares in `Composable` form;
  - the extended model, in which every model gets an `err` field, so the new axioms are proved and nothing is trusted.

  It is applied automatically wherever an abstraction function maps a `Float` type into the theory's sort. A theory that is not `Composable` gets no automatic term. Its author writes the error axioms, as the `lip`/`err` example above does by hand.

### 3. A placement that cannot prove a tolerance is a hard error

- **Explicit placement.** If a kernel with a tolerance contract is placed explicitly, with `@place(gpu)`, `@place(ane)` or `@place(auto, prefer = ...)` naming a device, on a device whose float model cannot prove the contract, compilation fails. The error names the device, the contract and the goal that failed under that device's model.
- **`@place(auto)`.** The cost model never considers a device that cannot prove the contract. Since nothing was asked of that device, this is not an error, but the placement report lists the device as excluded and gives the reason.
- **No warning-only mode.** A tolerance contract that holds on one device and not on another is never downgraded to a warning.
