# 74. Library types: a type written in Pia gets an MLIR type, ops and proofs from its library, and `Pia.Tensor` over MLIR `tensor` is the proof point

Date: 2026-11-27

Status: Accepted (2026-11-27, with Dean's answers below)

## Context

Dean asked for a tensor library that uses MLIR tensors under the hood while keeping contracts in Pia that are proved at compile time, and for it to be "the proof point for a way to extend Pia without having to add more primitive types in the language".

Today every type the compiler understands is a primitive in C++: integers, floats (ADR 0067 F1, PR #440), `bool`, fixed arrays, slices, records and variants. Each one has a row in `Codegen.cpp`'s type table, an encoding in the verifier, and its own printing, layout and FFI rules. A tensor done the same way would be another row in each of those tables, and so would every type after it: complex numbers, fixed-point, SIMD vectors, big integers, quantised weights. That is the path this ADR avoids.

[ADR 0065](0065-lowerings-written-in-pia.md) already gives most of the mechanism, for functions. `@lower` gives a function an MLIR form, the Pia body stays the specification and the fallback, and the lowering is proved to refine it or is listed as trusted. Steps 1 and 2 are merged (PRs #423 and #459): a trusted `@lower` on a function, metaprograms that compute the MLIR text, a parse check before proving, and the operand-effect check. ADR 0065 also sketched `@lower` on a type (section 1, step 6), and left it at one paragraph. This ADR turns that paragraph into a design, and puts `Pia.Tensor` on top of it.

What exists, and what a prototype with today's `piac` showed (2026-11-27, the `latest` prerelease):

- **Types can take types and regions, not values.** `let mat = let (t : type) (r : region) => type {...}` works; `let mat = let (t : type) (m : usize) (n : usize) => type {...}` is rejected ("only a generic type can take type arguments"). So a shape cannot be part of a type yet.
- **A field can carry a `where` about itself, not about its siblings.** `rows : usize where rows <= 65536` proves, and callers keep the fact. `data : [t] where len data = rows * cols` is "unknown name 'rows'", and a record-level `} where ...` is "refinements ('where') are not supported yet". ADR 0006 designed refinement types; they are not built.
- **With the shape as fields, every function must restate the invariant.** A `mat` of `rows`, `cols` and `data` with a spec `ok a = len a.data = a.rows * a.cols` proves `get` and `fill` (17 goals, 0.34 s) once each `requires ok a`. A matmul cell against a `dot` spec with symbolic `rows` and `cols` needs one bounds lemma per indexing map (as ADR 0065's prototype found), and its nonlinear index goals are where the time goes (see Prototype below).
- **With constant shapes the same proof is cheap.** ADR 0065's 4 x 4 `i8` matmul over `[i8; 16]` proved 51 of 51 goals in 17.5 s, because every extent is a literal and the index products fold.

### Prior art

- **MLIR's `tensor` dialect and destination-passing style.** A `tensor` is an immutable value. `linalg` ops on tensors take an `outs` operand, the *destination*, and return a new tensor of its shape; one-shot bufferisation then turns each op into an in-place write when the destination has no other reader, and inserts a copy when it does. `tensor.empty` makes a destination with no contents. This is the semantics the library takes, because it is already the one MLIR optimises.
- **Futhark, Dex and Idris** put sizes in types: `[n][m]f32` in Futhark, `n=>m=>Float` in Dex, `Vect n a` in Idris. A shape mismatch is a type error, and the compiler knows every extent that is a constant. Futhark also has the uniqueness types that make in-place updates of arrays safe, as Pia's `moved` does.
- **Mojo** builds its `Tensor` and `SIMD` types in the standard library on `__mlir_type`, with no proofs.
- **Rust's const generics** (`[T; N]`, `struct Matrix<const R: usize, const C: usize>`) are the mainstream form of a value as a type parameter, restricted to integers and other simple constants.
- **mlir-tv** (CAV 2022) gives `tensor` and `linalg` on tensors an SMT encoding as arrays from indices to elements, which is simpler than the memref encoding because there is no aliasing.

## Decision

### 1. A library type is a Pia type, its MLIR type, its ops, and its proofs, all in the library

A **library type** is a type whose meaning and whose machine form are both written in Pia, in a library, with no row for it in the compiler's tables. It has four parts:

1. **A Pia definition**: a record (or variant) of existing types, with its invariant. This is the type's meaning, what the verifier reasons about and what the REPL's JIT and `--lower=off` run.
2. **An MLIR type**, given by `@lower` on the type (ADR 0065, section 1): which MLIR type a value has, and how the Pia fields map onto it.
3. **Ops**: Pia functions with contracts, each with a Pia body (the specification and the fallback, ADR 0065's rule that a body is always kept) and a `@lower` that gives its MLIR form.
4. **Proofs**: each op's `@lower` is proved to refine its Pia body (ADR 0065's refinement goal, step 3), or is listed as trusted. Clients prove from the contracts only, and never see MLIR.

The compiler learns nothing about tensors. What it gains, once, are four general mechanisms that any library type uses:

| Mechanism | What it is | Status |
| --- | --- | --- |
| **`@lower` on types** | The MLIR type of a value, and how fields map onto it | ADR 0065 step 6, designed here (section 3) |
| **Value-returning lowerings** | A lowering whose result is a value (`$result`), not only writes to `out` buffers | New here (section 4) |
| **Type invariants** | A `where` on a whole record, over its fields, kept by every value of the type | ADR 0006, not built; needed here (section 2) |
| **Value parameters on types** | A type that takes a `usize` or a `[usize; r]`, so a shape is part of the type | New here, an open question (section 2) |

Each of those is a language or compiler feature, but none is a type: complex numbers, fixed-point, quantised blocks and SIMD vectors all use the same four and need nothing else. The test of this ADR is that after `Pia.Tensor` lands, a second library type (`Pia.Complex`, or `vec<T, k>` from ADR 0013 rebuilt as a library type over MLIR's `vector`) needs no compiler change at all.

### 2. `tensor t s`: shape in the type, extents as values

<!-- untested: proposed syntax -->
```ocaml
let tensor = let (t : type) (s : shape) (r : region) => type {
  data : borrowed(r) mutable [t]
} where len data = size s
  @lower("tensor<$s x $t>", data)
```

- **`s : shape` is a value parameter**: an array of extents, `[4; 4]`, where each extent is a literal, a constant, or `?` for one fixed at run time. A type with all-literal extents lowers to a static MLIR type (`tensor<4x4xi8>`), and every index product in its proofs folds, which is what made ADR 0065's static matmul cheap. A `?` extent is carried as a field the library adds, and lowers to `tensor<?x4xi8>`.
- **The invariant `len data = size s`** is a type invariant (ADR 0006): it holds of every value, is assumed on every parameter and proved at every construction, so no op restates it. Without type invariants, every op `requires ok a`, which the prototype shows works but which every client then has to prove again.
- **Rank is the length of the shape**, so `tensor i8 [64]` is a vector, `tensor i8 [4; 4]` a matrix, and there is one type, not a family. A shape mismatch is a type error at the call site, not a goal.
- **Elements are any type the core has**: integers now, `f32` and `f64` once floats have their meanings (ADR 0067 F2 and F3). A tensor of a library type (complex, quantised) needs the element type's own `@lower` to name a scalar MLIR type.

### 3. `@lower` on types

`@lower(mlir_type, buffer_field, extents...)` on a type names the MLIR type its values have, the field that holds the elements, and the fields that give the `?` extents. Version 1 allows ranked `tensor` and `memref` with the identity (row-major) layout over one buffer field, as ADR 0065 said; strided views come with FPL (ADR 0020). Codegen builds a value of the type from the buffer's pointer and the extents with `bufferization.to_tensor` (or a memref descriptor), and a value of the type passed to Pia code that is not lowered goes back through `bufferization.to_memref`. A function whose parameters and result are all tensors never makes that round trip.

### 4. Ops are values in destination-passing style, and nothing allocates behind the program's back

Pia's memory rule is that nothing allocates implicitly and every allocation is fallible (ADR 0026). MLIR tensors look like values that are made fresh by every op. Destination-passing style reconciles the two:

<!-- untested: proposed syntax -->
```ocaml
let matmul (a : tensor i8 [m; k] r) (b : tensor i8 [k; n] r)
           (c : moved tensor i32 [m; n] r) : tensor i32 [m; n] r
  ensures forall (i in 0 .. m) (j in 0 .. n). at result [i; j] = dot a b i j k
  @lower("%r = linalg.matmul ins($a, $b : $a.type, $b.type) outs($c : $c.type) -> $c.type")
= ...
```

- **Every op takes its destination**, `moved`, and returns it. The destination is the only storage the result uses. `Pia.Tensor.empty alloc s` is the only function that allocates, and it returns an error on failure like every other allocation (ADR 0026); `drop` frees.
- **`moved` is what makes bufferisation in place**, the way ADR 0065 section 1 said ownership facts would. A `moved` destination has no other reader, so one-shot bufferisation writes it in place. After bufferisation piac checks that it inserted no `memref.alloc` and no copy, and it is an error if it did: a hidden allocation is a bug in the library or in piac, never something a program silently pays for.
- **`$result` is a lowering's result value**, new in this ADR: ADR 0065's lowerings so far only write `out` operands. A lowering on tensors returns the op's result, and the operand-effect check (step 2) becomes: the result's buffer is the destination's.
- **Inputs are read, never written**, which on tensors is true by construction, since a tensor value cannot be written.

### 5. Contracts are about elements, through one spec accessor

Each op's contract is stated with the library's spec accessor `at t [i; j]`, never with `data` and index arithmetic, so clients never see the layout and never prove an index product. The accessor's bounds lemma (one per indexing map, ADR 0065's prototype finding) is proved once in the library. Reductions use the same spec folds as `Pia.Linalg` (ADR 0065, section 5): `matmul` is specified by `dot`, and the library's ops are generated from MLIR's own op definitions where `Pia.Linalg` already is, so `Pia.Tensor.matmul` and `Pia.Linalg.matmul` share one meaning and one proof.

The meaning of the MLIR form on tensors (for the refinement goal of ADR 0065 step 3) is the memref meaning without memory: a tensor is an SMT array from an index tuple to an element, `tensor.extract` and `tensor.insert` are select and store, `extract_slice` and `insert_slice` are index maps, and `linalg.generic` on tensors is the same fold as on memrefs, writing a new array instead of a buffer. One-shot bufferisation is an upstream pass, trusted the way `-O2` is, and listed in the trust report.

### 6. What `Pia.Tensor` has in version 1

`empty`, `fill`, `at` (spec) and `get`, `set` (an `insert` that returns the tensor), `map` and `zip_with` over a lambda (`linalg.generic` with a scalar body from the lambda), `reduce`, `transpose`, `reshape` (`tensor.reshape`, `expand_shape`, `collapse_shape`), `slice` and `insert_slice`, `matvec`, `matmul` and `batch_matmul`, and `dot`. These are exactly what the llama2.c port needs (ADR 0067: the projections are `matvec`, attention is `dot`, `slice` and `matvec`, the KV cache is `insert_slice`), so the LLM's kernels become the library's first client.

### Prototype

Run with the `latest` prerelease `piac` in the cloud (2026-11-27). Shapes as fields, since types cannot take values yet:

- `mat t r = {rows; cols; data}` with `rows`, `cols` bounded by field `where`s, and the invariant as a spec `ok`: `get` and `fill` prove, 17 goals in 0.34 s.
- A matmul cell (`i8` elements, `i32` sum) against a recursive `dot` spec over symbolic `rows` and `cols`: 46 of 50 goals proved in 10 min 7 s of wall-clock time (20 min 46 s of CPU at 4 jobs). The 4 that timed out are the two index-bounds goals inside `dot` and the two loop invariants after an iteration, all nonlinear in the symbolic `cols`. That compares with 51 of 51 goals in 17.5 s for the same cell at a literal 4 x 4 shape (ADR 0065's prototype). Shapes that are literals in types are the difference between a library whose proofs are cheap and one whose every client fights nonlinear goals.

### Implementation order

Each step is one PR and useful on its own.

1. **Type invariants**: a `where` on a record over its fields (ADR 0006), assumed on parameters, proved at construction and after each field write. Useful to every record, not only tensors.
2. **Value parameters on types**: a type that takes `usize` and `[usize; r]` arguments, with literal and `?` extents, and generic functions over them (`(m : usize)` deduced from an argument's type, as type arguments are). Also gives `[t; n]` generic functions.
3. **`@lower` on types** (ADR 0065 step 6): ranked `tensor` and `memref`, identity layout, one buffer field; value-returning lowerings with `$result`; one-shot bufferisation with the no-allocation check.
4. **`Pia.Tensor` with trusted lowerings** on CPU: the version 1 ops, each with its Pia body and contract, tested against `--lower=off`.
5. **Proved lowerings on tensors**: the tensor meaning of section 5 added to ADR 0065 step 3, so `Pia.Tensor`'s lowerings stop being trusted.
6. **Floats**: `f32` tensors once ADR 0038's meanings are in (ADR 0067 F2, F3), and the LLM's `matvec` on `Pia.Tensor`.
7. **The second library type**, with no compiler change, as the test of the mechanism.

## Consequences

- New numeric types become library code: a type, its MLIR form, its ops and their proofs, reviewed like any library, with no new primitive and no new row in Codegen or the verifier.
- Two general language features (type invariants and value parameters on types) come first, and they are worth having on their own; the tensor library waits for them.
- piac's trusted base grows by its reading of `tensor` semantics and by one-shot bufferisation, both listed in the trust report; the no-allocation check keeps bufferisation from adding hidden costs.
- `Pia.Tensor` and `Pia.Linalg` share meanings, so there is one proof of `matmul`, not two.

## Open questions

1. **Shapes in types, or shapes as values?** This ADR puts the shape in the type (section 2). The alternative is shapes as fields with contracts, which works today but makes every client prove shape agreement and index bounds, and costs more to prove (Prototype).
2. **Destination-passing, or ops that allocate?** This ADR has every op take a `moved` destination (section 4). The alternative is ops that take an allocator and return a result or an error, which reads more like NumPy and puts an allocation and an error path on every op.

## Answers to the open questions

- **Shapes in the type (question 1), Dean, 2026-11-27:** `tensor t s` takes its shape as a value parameter, as section 2 says, so value parameters on types (step 2) come before `Pia.Tensor`.

- **Destination-passing (question 2), Dean, 2026-11-27:** every op takes a `moved` destination and returns it, as section 4 says. Only `Pia.Tensor.empty` allocates.

- **How a function names a value parameter, Dean, 2026-11-27:** implicitly. A name in a value parameter's place that no parameter declares, `n` in `(b : block t n)`, is deduced from the argument like a type parameter, and in the body and contracts it is the argument's value. This replaces step 2's `(m : usize)` and needs no new syntax. The `matmul` signature in section 4 is already written this way.

## Amendment, 2026-11-27: ops lower through `pia_lib.call` (ADR 0078)

[ADR 0078](0078-pia-lib-ops-with-proved-substitutions.md) changes how section 4's ops reach MLIR. A `Pia.Tensor` op no longer puts `linalg.matmul` in place of the call at IRGen. It lowers to `pia_lib.call @Pia.Tensor.matmul`, whose meaning is the Pia body, and the `@lower` form becomes a substitution rule. A late pass, `pia-lib-lower`, either substitutes the rule's `linalg` op or expands the body. Section 4 reads with these changes:

- **The destination is an operand** of `pia_lib.call`, the way it is of `linalg`'s `outs`. Substitution runs before one-shot bufferisation, so bufferisation still sees only upstream ops, and the no-allocation check is unchanged. ADR 0065's `linalg` pipeline, and `@schedule`, run after the substitution, so a substituted op is still tiled and vectorised.
- **Expansion** sends a tensor operand back through `bufferization.to_memref` into the body's buffer field, writing the destination's buffer. The no-allocation check covers that path too, so expanding an op cannot copy behind the program's back.
- **`$result`** is ADR 0078's value-returning rule. ADR 0078 builds the scalar case first, for `Pia.Math.sqrt` (#487), and step 3 here extends it to tensors.
- **Each rule's obligation** is ADR 0065's refinement goal, which section 5 extends to tensors. It is proved once, when the op is verified, whether or not a build applies the rule. A rule nobody has proved yet is trusted and listed in the trust report, the same as step 4's lowerings.

Steps 3 to 5 build on this: step 3 adds `@lower` on types and the tensor case of `$result`, step 4's trusted lowerings are ADR 0078 rules, and step 5 proves them.

Steps 1 and 2 are built: record invariants (PR #472), and value parameters on types and on functions (PRs #499 and #515). Shapes, `(s : shape)` with `[4; 4]` or `[m; k]`, complete step 2 with literal extents; a `?` extent needs a field to carry it, so it comes with step 3.

Step 3 is built in two parts. Step 3a is `@lower` on types with `memref` only. A record names its MLIR type and the field that holds its elements, `@lower("memref<$s x $t>", data)`, where `$s` and `$n` splice value parameters and `$t` the elements' type parameter. A function lowering that splices a value of the type gets a view of its buffer. An array is viewed with `expand_shape`. A slice is cast to the length its type's invariant proves, and the body proves that length, so its view keeps a dynamic offset (`strided<[4, 1], offset: ?>`). An `inout` value whose elements are a slice is written through its loan and returned as it came in. Every extent is static, and there are no extent fields yet. Step 3b adds `tensor`, `$result` on tensors and one-shot bufferisation with the no-allocation check.
