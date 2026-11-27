# 78. Library functions lower to `pia_lib.call`, a Pia-owned op whose meaning is its Pia body, and a late pass either expands it into the body or substitutes an upstream op through a rule proved against the body

Date: 2026-11-27

Status: Proposed

## Context

Pia's codegen benchmarks (ADR 0075) need `sqrt` for n-body (#487). Dean's rules, from the thread and #487 (2026-11-27):

- **No builtins.** A compiler extension is a Pia function with a special lowering, unless that's impossible. Builtins are kept to what `@lower` cannot express, and never added to cheat for performance. Pia still needs provable low-level maths.
- **A Pia-owned dialect as the lowering target:** "a Pia dialect in MLIR that we can lower to, that we control the implementation of. So that way we can choose to lower to the Pia and still be able to detect that the implementation is correct, whether or not we do the substitution at lowering time."

ADR 0065's `@lower` puts the upstream op (`linalg.matmul`, or `math.sqrt` for `sqrt`) in place of the call when the function is compiled. That decides the substitution early, at IRGen, and the only record of the Pia function left in the IR is its symbol. ADR 0074 section 4 plans value-returning lowerings (`$result`) for tensors on the same mechanism.

`sqrt` shows what that leaves out. A pure Pia `sqrt` that is proved correctly rounded is an integer algorithm over `to_bits` and `from_bits` (#452): about 53 steps of a digit-by-digit square root, a few hundred cycles. The hardware's `fsqrt` takes 10 to 15. The pure body is the definition and the proof, and the hardware op is the speed. Both should be in the build, with a check that they agree.

## Decision

### 1. One generic op, `pia_lib.call`, names the Pia function

A new dialect, `pia_lib`, has one op:

```mlir
%r = pia_lib.call @Pia.Math.sqrt(%x) : (f64) -> f64
```

It names the Pia function whose body is its meaning. There is no op per function, so a library adds no C++ and no ODS, which is the point of ADR 0074. The function's body stays in the module as a private `func.func`, so the op can always be expanded.

IRGen emits `pia_lib.call`, not `func.call`, for a call to a function with a substitution rule (section 2). The op is `Pure` when the function is pure (ADR 0069), so CSE and hoisting treat it like any pure op, and `Elementwise` when the function is marked so, so the vectoriser can widen it (M10, #11) before the late pass.

Operand and result types are whatever the function's types lower to. That includes a library type's MLIR type (ADR 0074 section 3, such as `tensor<?x?xf32>`), not only scalars and memrefs. A tensor op carries its `moved` destination as an operand, the way `linalg`'s `outs` does.

### 2. A substitution rule is `@lower`, read as a rule rather than an immediate rewrite

The surface does not change: `@lower(...)` on the function, with ADR 0065's MLIR text and `$` splices. What changes is when it applies. The lowering is now a rewrite rule from `pia_lib.call @f` to the upstream form, applied late.

A rule may return a value with `$result`. It is pulled forward here from ADR 0074 step 3, for scalars, and extended to tensors there. The operand-effect check gains one rule: `$result` is the op's only output.

```ocaml
(** IEEE 754 square root: the real square root, rounded once to nearest even. *)
let sqrt (x : f64) : f64
  @lower("$result = math.sqrt $x : f64")
= (* to_bits, a digit-by-digit integer square root of the scaled
     significand, round to nearest even, from_bits; NaN, -0, +0, +inf
     and negatives first *)
```

### 3. A late pass expands or substitutes

`pia-lib-lower` runs after the vectoriser, before one-shot bufferisation, and before the lowering to LLVM. For each `pia_lib.call` it does one of two things:

- **Substitute:** apply the function's rule when `--lower=on` (the default) and the target supports the rule's dialects.
- **Expand:** otherwise call or inline the body. A tensor operand goes back through `bufferization.to_memref` into the body's buffer field.

Substitution runs before bufferisation, so bufferisation only sees upstream ops. "After the vectoriser" is for scalar rules. A tensor rule substitutes `linalg.matmul`, `linalg.generic` and the like, which still need linalg's own tiling and vectorisation. So the linalg pipeline, with ADR 0065's `@schedule`, runs after `pia-lib-lower` and before one-shot bufferisation, and a substituted op is never left unvectorised. ADR 0074's no-allocation check runs on both paths. On the expand path, the operands go through `to_memref` into a body that writes to the destination's buffer, so an expansion cannot quietly copy either. `--lower=off` means "always expand", which keeps ADR 0065's differential tests.

### 4. Each rule's correctness is proved once, whether or not it is applied

A rule's obligation is ADR 0065's refinement goal (step 3), the same one ADR 0074 section 5 extends to tensors. Under the function's `requires`, the meaning of the rule's MLIR form satisfies the function's `ensures`, and writes nothing else. There is no second kind of goal.

For a scalar op, "meaning" is the op's SMT semantics:
- `math.sqrt` on `f64` is `fp.sqrt RNE` in Z3's floating-point theory;
- `arith` ops are what piac already gives them.

When the `ensures` is "equals the body", which is what `sqrt`'s contract will say once ADR 0038's encoding lands, the goal is exactly "the upstream op computes the Pia implementation".

A rule has one of ADR 0065's states:
- **Proved** by Z3;
- **Proved in Lean** (ADR 0061);
- **Trusted:** listed in the trust report and the certificate as a `lowering` item, as today, until it is proved.

The goal is checked when the function is verified, not at each call, so the result holds wherever the rule is applied and wherever it is not.

### 5. Scope: every maths function, and anything that would otherwise be a builtin

Dean, 2026-11-27: "this idea scales to pretty much every math function that we want to optimize for the Pia standard library. Likewise, for anything that needs to look like some sort of built-in, we can do the MLIR side expansion on our terms instead of reaching into specifics in other dialects."

- **All of Pia.Math (#62)** takes this shape: `exp`, `log`, `pow`, `sin`, `cos`, `atan2`, `fma`, `rsqrt`, `hypot`. Each one is a Pia function whose body is the proved implementation, called through `pia_lib.call`. Most need no rule at all. A body built from range reduction and a polynomial is already the fast path, and the vectoriser widens it through `Elementwise`. A rule is added only where the target has a better form.
- **Anything that would otherwise be a builtin** takes this shape too: bit counts, byte swaps, saturating and widening multiplies, checksums such as CRC32, atomics' fences, memory copies. The expansion is ours: by default the body, which is pure Pia. The decision of what a `pia_lib.call` becomes stays in Pia's code, not in another dialect's conventions.
- **A rule may also target the `llvm` dialect, for assembly-style implementations.** This covers LLVM intrinsics (`llvm.intr.*`, such as `llvm.intr.sqrt`, `llvm.intr.fma`, `llvm.intr.ctpop`) and `llvm.inline_asm` with a fixed instruction sequence per target, such as `fsqrt d0, d0` on arm64, a NEON or AVX2 sequence for a kernel, or `crc32cx`. The rule names its target (`@lower(target = arm64, ...)`, one rule per target), and the pass picks the rule for the target being built, else the body. Its obligation is the same refinement goal. An intrinsic piac gives a meaning to is proved like any other op. Inline assembly has no meaning piac can read, so its rule is **trusted**. It is listed in the trust report with the target and the instruction text's hash, and the differential test against the body (`--lower=off`) runs on that target in CI.

### 6. `sqrt` first

1. `pia_lib` and `pia_lib.call`, emitted for functions with a rule, and the expand path of `pia-lib-lower`. Nothing is substituted yet, so behaviour is ADR 0065's `--lower=off`.
2. Scalar `$result`, and the substitute path.
3. `Pia.Math.sqrt` on `f32` and `f64`: the body proved correctly rounded with integer facts, `@lower` to `math.sqrt`, and the rule trusted at first. A test runs both forms against C's `sqrt` on special values and a sweep of bit patterns.
4. The rule's refinement goal with `fp.sqrt`, for `f32` first.
5. n-body in `bench/codegen` (ADR 0075).

ADR 0065's existing function lowerings (`linalg.matmul` in `tests/codegen/lower_linalg.pia`) move onto `pia_lib.call` in step 1. They keep their states and their tests.

## Consequences

- Pia.Math and every would-be builtin become Pia functions with optional rules, so the compiler's C++ grows by one dialect and one pass, not by one op per function.
- The IR keeps the Pia function as an op until late. Passes see `sqrt` as one pure, elementwise value rather than a call or an upstream op, and the substitution choice can depend on the target or on `--lower`.
- Correctness of an implementation no longer depends on whether it was substituted. Each rule is proved, Lean-proved or listed as trusted, once.
- `pia_lib` is a fourth dialect beside `pia`, `pia_contract` and `pia_par` (ADR 0018). It has one op.
- ADR 0074 section 4 becomes "a tensor op lowers to `pia_lib.call`, and its substitution rule targets `linalg`". The tensors thread will amend ADR 0074 to point here.
- Bit-blasting `fp.sqrt` on 64 bits against an integer algorithm may be too slow for Z3. `f32` is small enough to try first; `f64` may need a lemma split or Lean, and stays trusted until then.

## Open questions

1. ~~Is one generic op naming the function right, or should libraries be able to declare named ops (`pia_lib.sqrt`)?~~ Decided (Dean, 2026-11-27): one generic op. Named ops would bring back ODS per library.
2. ~~For `f32`, is running both forms on all 2³² inputs at build time an accepted proof of a rule?~~ Decided (Dean, 2026-11-27): no. A rule is proved by Z3 or Lean, or it is trusted. There is no `exhaustive` state, though a run over every input may still serve as a differential test.
3. ~~Should a rule that has not been proved be applied by default?~~ Answered by a principle instead (Dean, 2026-11-27): the compiler changes on principle to make every Pia program faster, not only the benchmarks (ADR 0075). So a rule belongs to the library function, not to a program. It applies to every call of that function on its target, in every program, or to none. It is never chosen per program, per benchmark or by flag. A rule is added only when it makes the function faster for every caller on that target. It is proved by Z3 or Lean, or listed as trusted in the trust report until it is.
