# 87. SIMD vectors are a library type, `simd t k` in `Pia.Simd`, lowered to MLIR `vector` values

Date: 2026-11-28

Status: Proposed

## Context

[ADR 0013](0013-auto-vectorisation.md) auto-vectorises every loop it can prove safe and keeps `vec<T, k>` "for authors who want to fix the vector shape themselves". Milestone M10 ([#11](https://github.com/deanberris/pia-lang/issues/11)) asks for both. The first half is built: proved loops reach LLVM's loop vectoriser with no checks left in them, so elementwise kernels vectorise as written (PR #579), and float reductions vectorise under `@fp(reassoc, contract)` (ADR 0012, PR #564). On 2026-11-28 Dean chose to build the second half, the explicit vector type, for 0.1.0.

The design so far is a few lines. [design.md](../design.md) says `vec<T, k>` is "an ordinary generic from the prelude" with `k * size_of t` of 64 or 128 bits, and [stdlib.md](../stdlib.md) lists its ops: `splat`, `lane`, `with_lane`, `vload`, `vstore`, lane-wise arithmetic with the usual overflow modes, comparisons and `vselect`, constant `shuffle`, widening and narrowing, and horizontal reductions, lowered to MLIR's `vector` dialect, with the verifier modelling a vector as `k` values. Since then, two rules have changed how such a type should be built:

- **No new builtins** (Dean, 2026-11-27, #487). Compiler extensions are Pia functions with a provable body and an `@lower` (ADR 0065), and a builtin is argued for only where `@lower` cannot express it.
- **Library types** (ADR 0074). A type written in Pia gets its MLIR type, ops and proofs from its library. ADR 0074's last step is "the second library type, with no compiler change, as the test of the mechanism", and names `vec<T, k>` over MLIR's `vector` as a candidate.

So this ADR builds the vector type as that second library type. A prototype with the piac of PR #564 (2026-11-28) showed how far today's mechanism reaches:

- `let simd = let (t : type) (k : usize) => type { lanes : [t; k] } @lower("memref<$k x $t>", lanes)` is accepted for integer lanes: value parameters on types (ADR 0074 step 2) and `@lower` on types (step 3a) both work.
- A float element is refused: "a lowered type's elements are an array or a slice of integers or bools". The check predates floats (ADR 0067 F1).
- A lowering cannot give a vector back. `@lower` on a type views the value's buffer as a `memref`, so an op would have to write an `out` operand, and an `out` value whose elements are an array is refused: the array is part of the value and is copied back, so a write through the view would be lost. `$result` (ADR 0078) is a scalar result only.
- The `vector` dialect is not loaded for lowerings, and codegen has no `vector`-to-LLVM conversion.
- `add`, `mul` and the other operator names are core builtins, which no definition may shadow (ADR 0022).
- `vec` is already a type: `Pia.Mem.Vec`'s growable vector (`vec t a r`), and `Pia.Text.Json.Dom`'s.

None of these is about SIMD in particular. Each is a gap in the library-type mechanism, and closing it helps every value-like library type: complex numbers, fixed-point and small matrices.

### Prior art

- **MLIR's `vector` dialect.** `vector<4xf32>` is an SSA value. `vector.load` and `vector.store` move it to and from a `memref`, `vector.broadcast` splats a scalar, `vector.extract` and `vector.insert` read and write a lane, `vector.reduction` folds it, and `arith` and `math` ops work lane by lane on vectors. `convert-vector-to-llvm` lowers all of it to LLVM's fixed-width vectors, which instruction selection maps to NEON and AVX2 and splits when a vector is wider than the target's registers.
- **Rust's `std::simd`** (`Simd<f32, 4>`), and **Mojo's `SIMD[DType.float32, 4]`**: a vector is a library type, generic over element and lane count, with lane-wise operators and explicit reductions. Mojo builds it on `__mlir_type`, with no proofs.
- **Zig's `@Vector(4, f32)`** and **GCC's and Clang's vector extensions**: built in, with the same lane-wise meaning.
- **Highway** (Google) and **xsimd**: portable C++ SIMD libraries whose widths are chosen per target, which is the case for a "natural width" constant.

## Decision

### 1. `simd t k` is a record of `k` lanes in `Pia.Simd`, and its machine form is `vector<k x t>`

```
let simd = let (t : type where Lane t) (k : usize) => type {
  lanes : [t; k]
} where supports t k
  @lower("vector<$k x $t>", lanes)
```

- **The meaning is the array.** A `simd f32 4` is four `f32`s, and every contract about it is about `v.lanes.[i]`. The verifier needs nothing new: a record of a fixed array is already `k` values to it, as stdlib.md planned.
- **The name is `simd`**, as in Rust's `Simd` and Mojo's `SIMD`, so that it does not collide with `Pia.Mem`'s growable `vec` (open question 1). design.md's `vec<T, k>` becomes `simd<T, k>`: the angle brackets are the same sugar for applying a generic type (grammar.md), and `simd f32 4` is the other spelling.
- **`Lane t`** is a concept that every integer type, `bool`, `f32` and `f64` meet. `bool` lanes are what comparisons give and what `select` takes, and lower to `i1`.
- **Widths depend on the target** (Dean, 2026-11-28). `k` is a power of two, and `k * bits t` is at most the widest vector the CPU runs natively, `Target.vector_bits` in the model of the target being compiled for ([ADR 0049](0049-targets-are-theories.md)): 128 bits on arm64 (NEON) and 256 on x86-64-v3 (AVX2). There is no fixed table, so a new target or CPU level with wider vectors (AVX-512, SVE at a known length) allows wider `simd` types by changing its model alone.
- **Named shapes are aliases in their own module** (Dean, 2026-11-28). No vector type is built into the compiler, and `Pia.Simd` defines only `simd t k`. `Pia.Simd.Types` holds the familiar names as aliases ([ADR 0064](0064-distinct-types.md)), so they are the same types as their `simd` spelling and an importer that wants none of them never sees them: `let f32x4 = simd f32 4`, `f64x2`, `i8x16`, `u8x16`, `i16x8`, `u16x8`, `i32x4`, `u32x4`, `i64x2` and `u64x2` for 128 bits, and `f32x8`, `f64x4`, `u8x32` and the rest for 256 bits, each of which is a type error on a target where `supports` says no.
- **Target-generic code asks the library, with metaprograms** (Dean, 2026-11-28). `Pia.Simd` exports type-level metaprograms ([ADR 0035](0035-substitution-failure-and-total-constraints.md)) that answer for the target being compiled for, so code that names no target can still use each target's width:

  | Metaprogram | Meaning | arm64 | x86-64-v3 |
  | --- | --- | --- | --- |
  | `vector_bits t` | the widest native vector, in bits (`t` is only there because a type-level metaprogram takes types) | 128 | 256 |
  | `bits t` | the bits of one lane of `t` | 32 for `f32` | 32 for `f32` |
  | `natural t` | the lanes of one native vector, `vector_bits t / bits t` | 4 for `f32` | 8 for `f32` |
  | `supports t k` | `k` is a power of two and `k * bits t <= vector_bits t` | `supports f32 8` is false | true |

  They read the target through one new metaprogram builtin, `target_value "vector_bits"`, the value the target's model gives a `Target` spec. The width check is `simd`'s `where supports t k`, a constraint that piac evaluates where the type is formed, as it does a generic's `where` over a type-level metaprogram, so it costs no solver query and a use outside the target's widths is a type error naming the target, not a failed goal. A type argument may be a type-level metaprogram's integer, `simd f32 (natural f32)`, and overloads may be chosen by `where supports t 8` (substitution failure, ADR 0035), so one kernel takes the wide path where the target has it. The proofs of a target-generic function are then the proofs of its instance for the target it is compiled for, the instance's width being a constant, as with any value parameter. A function that must hold on every target still says so with the axiom `vector_bits >= 128`, which lets it use `simd f32 4`, `simd u8 16` and other 128-bit types without a query.

### 2. A type lowered to `vector` is a value: `$a` is the vector, and `$result` may be one

This is the one compiler change in this ADR, and it is general: it applies to any library type whose `@lower` names a `vector` type, not to `simd` alone.

- **An argument** of such a type is spliced as a vector value. Codegen loads it from the value's storage with `vector.load` before the lowering, where ADR 0074's memref types get a view. `$a.type` is `vector<4xf32>`.
- **`$result`** may have such a type (ADR 0078, section 2, which allowed scalars only). Codegen stores the lowering's result vector into the result's storage with `vector.store`. Records are returned by out-pointer (`ArrayResults.cpp`), so this is the same buffer the Pia body writes.
- **`out` and `inout` operands** of a vector type are refused, with a hint to return the value. A vector is a value; it is never written in place.
- **Float lanes** are allowed in every lowered type, `memref` and `tensor` as well as `vector`, which closes the check that predates floats.
- **No memory is left behind.** Each lowered op is its own function in core MLIR, so values travel through memory between ops. Every call is inlined at `-O1` and above (the functions are small and internal), after which SROA and instruction combining remove each store-load pair and the vector stays in a register. `tests/codegen/simd.pia` checks that a chain of ops compiles to vector instructions with no stack traffic.

### 3. The ops are Pia functions with a body and a trusted `@lower`

Each op in `Pia.Simd` has a contract, a Pia body over the lanes, which is its specification and its fallback under `--lower=off`, and an `@lower` to `vector` and `arith`. In version 1 every lowering is trusted and appears in the trust report, as `Pia.Math.sqrt`'s does (ADR 0078). They become proved when ADR 0065's refinement goal gets the meaning of `vector` ops (section 5).

| Op | Meaning | Lowering |
| --- | --- | --- |
| `splat x` | every lane is `x` | `vector.broadcast` |
| `lane v i` | `v.lanes.[i]`, with `i < k` a goal | `vector.extract` |
| `with_lane v i x` | `v` with lane `i` set to `x` | `vector.insert` |
| `load xs i` | `xs.[i .. i + k]`, with `i + k <= len xs` a goal | `vector.load` |
| `store xs i v` | writes `v` to `xs.[i .. i + k]`, same goal; `xs` is `out` or `inout` | `vector.store` |
| `plus`, `minus`, `times` | lane-wise `+ - *` | `arith.addi`, `subi`, `muli`; `addf`, `subf`, `mulf` |
| `over` | lane-wise `/` on floats | `arith.divf` |
| `fma a b c` | lane-wise `a * b + c`, rounded once | `math.fma` |
| `min`, `max` | lane-wise; on floats, IEEE 754-2019 `minimum` and `maximum`, so a NaN lane gives NaN (unlike C's `fmin`) | `arith.minsi`, `minui`, `minimumf` and their `max` forms |
| `less`, `at_most`, `equal` | lane-wise comparisons, giving `simd bool k` | `arith.cmpi`, `arith.cmpf` |
| `select m a b` | lane `i` is `a`'s where `m`'s is true, else `b`'s | `arith.select` |
| `sum v` | lanes added in order, lane 0 first | `vector.reduction <add>` |
| `largest v`, `smallest v` | the largest or smallest lane | `vector.reduction <maxsi>` and friends |

The names avoid the core builtins `add`, `mul` and the rest, which no definition may shadow (ADR 0022). Operators for a type (`let meta operator ( + ) for simd t k`, ADR 0022 section 5) are not built yet. When they are, `a + b` on two vectors is `plus a b`, and these names stay.

- **Integer lanes keep Pia's overflow rule.** `plus` on `i32` lanes raises one `nooverflow` goal per lane, as four scalar additions would, in the default `@overflow(proof)` mode. `plus_wrap` and `plus_sat` are the modular and saturating forms, lowered to `arith.addi` and to LLVM's `sadd.sat` or `uadd.sat` intrinsic, which NEON's `sqadd` and `uqadd` implement. No vector op wraps silently.
- **Float lanes are strict IEEE.** Each lane is rounded once, as the scalar op is, so a vector kernel gives the same bits as its scalar loop. `fma` is the one op with one rounding, and is a distinct op, not a contraction. `sum v` adds in lane order, which LLVM lowers to an ordered reduction (`fadda` on SVE, a chain of `fadd` on NEON). Under `@fp(reassoc)` in the caller, ADR 0012's licence lets codegen reorder it into a tree.
- **Lanes are proved like scalars.** A goal about `lane (plus a b) 2` is a goal about `a.lanes.[2] + b.lanes.[2]`, so the interval stage and Z3 see what they see for scalar code.

### 4. Codegen loads `vector` and lowers it to LLVM

`loadLoweringDialects` adds `vector`, and the LLVM conversion adds `convert-vector-to-llvm` with the vector lowering patterns it needs: transfers, broadcasts, reductions and `math.fma`. The C ABI never passes a vector: an exported function that takes or returns `simd t k` passes it as its array, as it does any record of an array (ADR 0030). So no calling convention changes, and C callers see `float lanes[4]`.

### 5. Later: proved lowerings

The meaning of a `vector` op for ADR 0065's refinement goal is the meaning of the same op on an array of `k` values. It is lane-wise for `arith`, an index for `extract` and `insert`, and a fold for `reduction`. With it, each lowering in `Pia.Simd` becomes a refinement goal against its Pia body, and the trusted list shrinks to nothing. This is ADR 0074's step 5 applied to vectors, and is not needed for 0.1.0.

## Consequences

- An author who wants a fixed vector shape writes `simd f32 4` and calls `load`, `fma` and `sum`, gets NEON and AVX2 instructions, and keeps every proof obligation the scalar code would have.
- The compiler gains one mechanism, value lowerings to `vector` types (section 2), and learns nothing about SIMD. ADR 0074's test, a second library type with no SIMD-specific compiler code, is met. Complex numbers and other value-like library types can use the same mechanism.
- Until section 5, `Pia.Simd`'s lowerings are trusted, and every program that uses them lists them in its trust report.
- A JSON scanner in the style of simdjson (ADR 0045) and the best-known lane of the codegen benchmarks (ADR 0075) can now be written.

### Implementation order

Each step is one PR with its tests, docs and skill changes.

1. **Value lowerings to `vector`** (section 2) and **float elements** in lowered types, with the `vector` dialect and its LLVM conversion (section 4). Tested by a lowered type in `tests/codegen`, by checking the vector instructions on both targets, and by refusing `out` vector operands.
2. **`Pia.Simd`** and **`Pia.Simd.Types`**: the type, its aliases, the target queries of section 1 (`target_value`, type-level metaprograms that return an integer, and their use as a value argument), and the ops of section 3, with trusted lowerings. `tests/std/simd.pia` proves the bodies, `tests/codegen/simd.pia` checks NEON and AVX2 output, and a C harness checks every op against the scalar loop bit for bit, under `--lower=off` too.
3. **Kernels**: a dot product and clamp-and-scale written with `simd`, against the auto-vectorised loops of PRs #564 and #579, which closes #11.
4. **Proved lowerings** (section 5), after 0.1.0.

## Open questions

1. **The name.** `simd t k` in `Pia.Simd` is proposed above, because `vec` is `Pia.Mem`'s growable vector. The alternatives are to keep `vec<T, k>` and rename `Pia.Mem`'s type (a breaking change with a migration rule), or to keep both and write the SIMD one `Simd.vec` wherever both are in scope.
2. **Widths.** Resolved (Dean, 2026-11-28): what is supported depends on the target, not a fixed limit, and target-generic code asks the library's metaprograms (`natural`, `supports`) rather than naming a target (section 1). design.md's fixed 64 or 128 bits and the earlier proposal of a fixed 512 bits are both dropped.
