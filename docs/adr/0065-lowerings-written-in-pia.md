# 65. Pia code extends the compiler's lowering: `@lower` gives a function an MLIR form and a type an MLIR type, the Pia definition stays the specification, and each lowering is proved to refine it or is listed as trusted

Date: 2026-11-24

Status: Accepted (2026-11-24, with Dean's answers below)

## Context

Dean asked for a way to extend the compiler from Pia itself: to say that certain Pia types lower to MLIR types and certain functions lower to MLIR ops, with tensors, memrefs and `linalg` as the key cases. The motivation is matmul and SIMD kernels that are represented and optimised as `linalg` on `memref`, and run on GPUs by going down through MLIR to SPIR-V. That is the path Dean chose for the GPU demo on 2026-11-23: SPIR-V, then SPIRV-Cross to MSL for Metal now, other vendors later.

Today the lowering is closed. `Codegen.cpp` maps each `pia` type and op to `arith`, `scf`, `memref` and `func` by a fixed table ([docs/codegen.md](../codegen.md#types)): `[T; n]` is `memref<n x T>`, a slice is a strided `memref<?xT>`, and nothing produces `linalg`, `tensor`, `vector` or `gpu`, although [ADR 0018](0018-dialect-layering.md) always meant code to lower through them. Every new kind of op needs C++ in IRGen and Codegen. What Pia does have:

- **Metaprograms** that run to a fixed point ([ADR 0007](0007-metaprogramming-fixed-point-expansion.md)), build items from quotes, compute strings, and are proved total when their output becomes a proof hypothesis ([ADR 0035](0035-substitution-failure-and-total-constraints.md)).
- **Theories** ([ADR 0036](0036-library-theories.md)): a library extends the *solver* with sorts, functions and axioms, made safe by a model or listed as trusted. This ADR is the same move for the *code generator*, and borrows its answer: whatever a library adds is either proved, or named in the trust report.
- **Foreign functions** (`= extern "sym"`, [docs/codegen.md](../codegen.md#foreign-functions)): the body is elsewhere and the contract is trusted; with no contract, every call is `unsafe`. Their contracts are trusted items in the certificate ([ADR 0024](0024-published-proof-certificates.md)).
- **Placement and dataflow** ([ADR 0015](0015-device-placement.md), [ADR 0050](0050-senders-and-receivers.md) section 7): `@place(gpu)` and GPU schedulers in a sender graph, which must never change the proved result. `spread` ([ADR 0060](0060-spread-v0-ownership-and-runtime.md)) reaches codegen as an `scf.for`, run by MLIR's async runtime.
- **Lean** ([ADR 0061](0061-lean-proved-facts.md)) for facts Z3 cannot prove, recorded by statement hash.

The soundness question is the whole design. A lowering replaces the code the verifier proved with code it did not see. If `matmul` is proved over its Pia body and then compiled as `linalg.matmul`, the proof is about a program that never runs, unless something shows that the op does what the body does.

### Prior art

- **Mojo** exposes MLIR directly: `__mlir_type[...]`, `__mlir_op.<name>` and `__mlir_attr` inside ordinary functions, and its standard library builds `Int`, `SIMD` and its tensor types on them. It is the most direct model for the surface, and has no proofs: what the op does is what MLIR does.
- **Rust intrinsics** (`#[rustc_intrinsic]`) are functions the backend implements. Since 2024 an intrinsic may have a *fallback body*, used by backends that do not override it; `-Z force-intrinsic-fallback` runs the fallback everywhere for testing, and `#[miri::intrinsic_fallback_is_spec]` marks a fallback that *is* the specification, a requirement the docs call strong. That is the shape Pia wants, with the claim proved instead of asserted.
- **Lean's `@[extern]` and `@[implemented_by]`** keep a Lean definition as the logical meaning and compile calls to other code. The kernel reasons about the definition; nothing checks the implementation, and a mismatched `implemented_by` is a known way to make compiled Lean disagree with proved Lean.
- **Zig `comptime`** computes types and code at compile time with no separate macro language, and exposes the backend's vectors and intrinsics as builtins (`@Vector`, `@reduce`). It shows how far ordinary compile-time code can go before a new form is needed.
- **Julia** reaches MLIR through MLIR.jl's bindings, and Reactant.jl traces Julia functions into StableHLO and compiles them with XLA: the lowering is a library, not the compiler.
- **Halide**, and MLIR's **transform dialect** after it, split the algorithm (what is computed) from the schedule (tiling, vectorisation, mapping to threads). The schedule is a script the author writes, and it cannot change the result, by construction of the transforms.
- **mlir-tv** (Bang et al., CAV 2022) translation-validates MLIR transformations, `linalg` and `tensor` included, by encoding both sides in SMT and proving refinement with Z3, with an abstraction of float arithmetic refined on failure. Inspired by Alive2, it found mismatches between MLIR's documented semantics and its implementation. It shows that `linalg` on tensors and memrefs has an SMT encoding that scales to real kernels.

## Decision

### 1. One attribute, `@lower`, on a function or a type

No new keyword. `@lower(e)` on a `let` gives the item an MLIR form, where `e` is a string of MLIR, or a call to a metaprogram that returns one. `$name` in the string splices a parameter of the function, the result, or a type, as MLIR values and types.

<!-- untested: proposed syntax; @lower does not exist yet -->
```ocaml
(** C[i, j] := sum over p of A[i, p] * B[p, j], row-major. *)
let matmul (m : usize) (n : usize) (k : usize)
    (a : [i8]) (b : [i8]) (c : out mutable [i32])
  requires len a = m * k && len b = k * n && len c = m * n
  ensures forall (i in 0..m). forall (j in 0..n).
    c.[i * n + j] = Linalg.dot a b k n i j k
  @lower("linalg.matmul ins($a, $b) outs($c)")
= for i in 0..m do ... done
```

- **The Pia body stays, and it is the specification.** The verifier proves the body against the contract, as for any function, and every caller proves from the contract. The body is also the fallback: the REPL's JIT runs it, a target without the lowering's dialects compiles it, and `--lower=off` compiles it everywhere, for differential tests ([ADR 0056](0056-tests-generated-from-contracts-and-theories.md) can run both forms on generated inputs). This is Rust's fallback body, with the "fallback is the spec" claim proved (section 3) instead of asserted.
- **The MLIR is checked when it is expanded.** piac splices the operands and parses the string with MLIR's own parser against the dialects the build registers, so a misspelt op or a type mismatch is an error at the attribute, with MLIR's diagnostic, and not a crash in codegen. A metaprogram that computes the string runs at expansion like any other, so a lowering can depend on the shape, the element type or the target (`@lower(matmul_for $t)`).
- **Operands are the function's parameters, by name and modifier.** An `out` or `inout` buffer may be written by the MLIR form, and an `in` buffer may not: a structural check on the op's memory effects (for `linalg`, its `outs`). A buffer lowers as it already does, a `memref`.
- **`@lower` on a type** names the MLIR type its values have and how the Pia fields map onto it. The Pia definition is again the meaning:

<!-- untested: proposed syntax -->
```ocaml
let matrix = let (t : type) => type {
  data : [t]; rows : usize; cols : usize
} where len data = rows * cols
  @lower("memref<?x?x$t>", data, [rows; cols])
```

  Codegen builds the descriptor from `data`'s pointer with sizes `[rows; cols]` and row-major strides, and the verifier proves that the `where` keeps the descriptor in bounds. Version 1 allows ranked `memref` and `tensor` of identity (row-major) layout over one buffer field; strided and affine layouts come with FPL ([ADR 0020](0020-presburger-for-affine-goals.md)). A value type such as `[t; n]` held as a `tensor` lowers through one-shot bufferisation, and Pia's ownership facts (a `moved` value has no other reader, a `borrowed` one is not written) are what tell bufferisation it may write in place, the way [ADR 0013](0013-auto-vectorisation.md) passes proved facts to the vectoriser.

Alternatives considered: `= extern mlir "linalg.matmul"` reuses a keyword, but `extern` means "no body, trusted contract", and the point here is to keep the body and prove the op against it. A quoted MLIR builder in metaprograms (``mlir`( ... )``, with ops as values) is more structured than strings, but needs a second quote language, and MLIR's own textual form is already the most stable interface MLIR has. Mojo's inline `__mlir_op` in expressions is the most flexible, and it would let MLIR ops appear anywhere in a body, where the verifier cannot see them.

### 2. `@schedule` says how, as a transform-dialect script

The algorithm is the lowered op. How it is tiled, vectorised and mapped onto threads is a **schedule**: a transform-dialect script that piac runs after lowering, written in `@schedule(e)` with the same string-or-metaprogram rule:

<!-- untested: proposed syntax -->
```ocaml
@schedule("
  %mm = transform.structured.match ops{[\"linalg.matmul\"]} in %root
  %tiled, %forall = transform.structured.tile_using_forall %mm tile_sizes [32, 32]
  transform.structured.vectorize %tiled")
```

A schedule can only call upstream transforms, which preserve meaning by construction, so it is trusted the way LLVM's `-O2` is trusted: as part of the compiler. It is still listed (section 4), because upstream transforms have had bugs (mlir-tv found some), and on integer kernels piac can check a schedule by translation validation (section 3, step 8). A transform that reassociates a reduction (`split_reduction`, vectorising a reduction, a GPU tree reduction) is an error on a float kernel under strict IEEE ([ADR 0012](0012-floating-point-reassociation.md)), and allowed under `@fp(reassoc)` or a tolerance contract ([ADR 0038](0038-float-kernels-against-real-theories.md)). This is the rule that placement never changes the proved result, applied to schedules.

### 3. Who proves the MLIR form matches the Pia definition

Each lowering is in one of three states, chosen by what the op is, not by the author:

1. **Proved (the default).** When piac knows the meaning of every op in the MLIR form, it proves the **refinement goal**: under the function's `requires`, the MLIR form's meaning implies its `ensures`, and it writes nothing but its `out` and `inout` operands. The goal is an ordinary obligation, reported, sliced and cached like any other. The ops piac gives a meaning to, in version 1: `arith` and `index` on integers, `memref` and `tensor` shape and element ops, `scf`, and **`linalg.generic`**, which covers every named `linalg` op, since piac first generalises a named op with MLIR's own `generalizeNamedOp`. A `linalg.generic` is a perfect loop nest over its iteration domain, in order, so its meaning is: for every point of the parallel dimensions, the output cell is a fold of the scalar body over the reduction dimensions. piac writes that as Pia spec functions (a `forall` over the parallel dimensions, and a recursive spec fold with a `decreases` measure over each reduction dimension, built from the indexing maps and the scalar region), and the refinement goal is proved from them. If the function's `ensures` is written with the matching library spec (section 5), the goal closes by unfolding the same definition; otherwise it needs a lemma, as any recursive spec does.
2. **Trusted.** An op piac has no meaning for (`gpu.*`, `spirv.*`, `nvvm.*`, `arm_sme.*`, any vendor intrinsic) can be the target of a lowering only in a `@trusted` module, and then the refinement goal is accepted, not proved: the lowering is a trusted item, exactly like an `extern` contract, and the body is still proved against the contract. Differential tests of the body against the lowering (`--lower=off`, section 1) are the check that remains.
3. **Proved in Lean.** A refinement goal Z3 cannot close, such as a fold equal to its specification only by a ring identity, can be proved in Lean against the generated statement, by [ADR 0061](0061-lean-proved-facts.md)'s rules, and recorded with the `lean` status and the statement's hash.

The meaning piac gives an op is the only new trusted component in state 1: it is piac's reading of MLIR's semantics. It is kept small and testable: each op's meaning is checked against MLIR's own reference lowering (`convert-linalg-to-loops`, then `scf` and `memref`, which piac already encodes) on generated kernels, in a test suite like the litmus battery of [ADR 0052](0052-atomics.md).

Floats wait on M11. With floats, a `linalg` reduction has a fixed order, so strict IEEE refinement is exact, but every useful schedule reorders it, so float kernels will in practice carry a tolerance contract (`c ~= spec within e`, ADR 0038) proved against a real-valued specification, with the reduction's error term derived by ADR 0038's automatic bound. Integer kernels need none of this, and include the quantised `i8 × i8 → i32` matmul that ML inference runs on GPUs, so they come first.

### 4. Trust report and certificates

Two new kinds of trusted item join the four of [docs/abi.md](../abi.md) (`extern` contract, `@assume`, `--allow-unproved` goal, `unsafe` call):

- **`lowering`**: a function or type whose MLIR form is trusted (section 3, state 2), recorded with the item, the ops it uses, and the SHA-256 of its spliced MLIR text.
- **`schedule`**: a transform script, recorded with the functions it applies to, the transforms it calls, and its hash.

A proved lowering is not a trusted item, and a Lean-proved one has the `lean` status. `piac --trust-report` lists both new kinds, and `--why` names the callers whose proofs went through a trusted lowering's contract. The lowering is not in the interface hash: like a body, it is the module's own business, so changing a kernel's tile sizes does not invalidate importers' proofs. It is in the certificate, so `pia-cert trust-report` on a shipped binary says which kernels ran as GPU code nobody proved.

### 5. `linalg` ops get Pia contracts from MLIR itself

`Pia.Linalg` declares each `linalg` named op as a Pia function: a Pia body, a contract written with spec functions that mirror the op's definition (`dot`, `conv_2d_nhwc_hwcf`, `pooling_nhwc_max`), and `@lower` to the op. These declarations are generated, not written by hand, as the POSIX bindings are ([ADR 0057](0057-posix-module-per-target-behind-one-interface.md)): a small tool links MLIR, builds each named op on symbolic shapes, generalises it, and writes the spec functions from the indexing maps and the scalar region. Each declaration's refinement goal is then proved by section 3, so a generator bug fails a proof instead of shipping a wrong contract. Named ops whose definitions moved from OpDSL to ODS (`linalg.matmul` with its `indexing_maps`, the elementwise ops) are handled the same way, since the tool reads the generalised op and not the YAML.

User code calls `Linalg.matmul` and proves from its contract, as from any library. A kernel author who wants their own op writes a Pia function with `@lower` to a `linalg.generic` and gets the same proof.

### 6. How it reaches the GPU through SPIR-V

The driving example is a tiled integer matmul on the GPU:

1. The function is proved over its Pia body.
2. `@lower` replaces the body with `linalg.matmul` on `memref`s, and the refinement goal is proved.
3. `@schedule` tiles it with `tile_using_forall` and maps the `scf.forall` onto GPU blocks and threads (`transform.gpu.map_forall_to_blocks`, `map_nested_forall_to_threads`). The tiles' disjoint writes are what `tile_using_forall` constructs; once the schedule's output is lifted back to `pia_par`, ADR 0060's ownership goal (each tile owns the cells of its slice) proves it, instead of trusting it.
4. `gpu-kernel-outlining`, the memref storage-class mapping, and `convert-gpu-to-spirv` produce a `spirv.module`, serialised to SPIR-V, then SPIRV-Cross writes MSL for Metal.
5. The host side, `gpu.launch_func`, calls a small trusted Metal shim through `extern` contracts, which is the GPU ADR's subject, along with `@place(gpu)` over these kernels and `Pia.Exec.Metal` ([ADR 0050](0050-senders-and-receivers.md), step 9).

The same function with no `@place(gpu)` lowers through the same `linalg` and a CPU schedule (tile, vectorise, `arm_neon` or AVX2), which is the SIMD half of Dean's motivation and needs no GPU work at all.

### Prototype

A 4x4 integer matmul (`u8 × u8 → u32`, row-major), with `dot` written as the spec that linalg's generalised `matmul` would give the verifier, a client `corner` that proves one cell from the contract alone, and an all-parallel elementwise add were run on the iMac with `piac --verify --verify-stats --jobs=4` (piac at `436306d`).

- **The fixed-shape case proves: 51 of 51 goals in 17.5 s** (48 by Z3, 3 by intervals, cost 102M). The costliest goals are `corner`'s last step relating `dot … 4` to the written-out sum (cost 53.9M, 10.5 s), the inner loop's invariant (20.7M, 10.6 s), `corner`'s postcondition (14.9M, 2.1 s), and the `+` in the constant-stride index `i * 4 + j` (7.1M, 4.4 s), which intervals should own. The elementwise add is trivial: 7 goals, cost 37K, under 10 ms each.
- **A generated reduction spec gets `@fuel(1)`.** With `@fuel(4)` the same file took 522 s and failed two goals, because Z3 unfolded `dot` under the nested quantifiers. Each loop step needs exactly one unfolding, so the generated spec and the loop invariants it implies are written for fuel 1.
- **Clients need an unrolling lemma for static extents.** Relating `dot … 4` to a closed form takes five unfoldings, which `corner` got from a chain of five `assert`s. The generator emits that lemma (`dot_unroll4`) for each static reduction extent instead.
- **Names collide with core builtins.** `add`, `sub`, `mul`, `div` and `max` are core builtins, and Pia has no shadowing ([ADR 0022](0022-metaprogram-hygiene.md)), so `Pia.Linalg` cannot use those op names. The generator names elementwise ops `ewise_<op>`, as linalg's own `elementwise` op does by kind.
- **Symbolic shapes do not prove as written.** With `m`, `n` and `k` as parameters and slices of length `m * k`, every nonlinear index goal (`i * k + p < len a`, the overflow of `i * k`) timed out at 30 s: 16 of 33 proved, cost 3.7G. So the generator proves each indexing map's bounds once, as a lemma per map (`i < m && p < k ==> i * k + p < m * k`, proved with range-typed dimensions, or in Lean by ADR 0061), and states the op's contract over an accessor that uses it, rather than leaving the products to every goal.

### Implementation order

Each step is one PR, and each is useful on its own.

1. **Link `linalg`, `tensor`, `bufferization` and `transform`** into piac, and lower a function marked `@lower` with a trusted lowering (state 2) only, on CPU: `linalg` to loops, then the existing path. The `lowering` trusted item, in the trust report and the certificate. `--lower=off`.
2. **The splice-and-parse check** at expansion, metaprograms that compute lowerings, and the operand-effect check.
3. **Proved lowerings for integer `linalg.generic`** and named ops through `generalizeNamedOp`: the meaning as spec functions at fuel 1, a bounds lemma per indexing map and an unrolling lemma per static extent (see the prototype), the refinement goal, and the reference-lowering test suite for piac's encodings.
4. **`Pia.Linalg`**, generated, starting with `matmul`, `batch_matmul`, `add`, `fill`, `conv_2d_nhwc_hwcf` and the poolings.
5. **`@schedule` on CPU**: tile and vectorise, the reassociation check, the `schedule` trusted item. Benchmarked against the Pia body's own codegen.
6. **`@lower` on types**: ranked `memref` and `tensor` over one buffer field, one-shot bufferisation fed by ownership facts.
7. **GPU**: the GPU ADR first (SPIR-V, SPIRV-Cross, the Metal shim, `@place(gpu)`), then the schedule's `scf.forall` mapped to threads, proved disjoint by ADR 0060's rule.
8. **Translation validation of schedules** on integer kernels: the refinement goal re-proved after the schedule, so a schedule stops being trusted.
9. **Floats**, after M11: tolerance contracts for `linalg` reductions under ADR 0038.

## Consequences

- Library code, not compiler C++, decides how kernels lower, and the compiler gains `linalg`, `tensor`, `transform` and, later, `gpu` and `spirv` without a new keyword.
- A lowering cannot quietly change what was proved: it is proved to refine the Pia definition, proved in Lean, or listed as trusted in every report and certificate that depends on it.
- Every lowered function keeps a body that the REPL runs and that differential tests compare against, so the REPL never needs the GPU pipeline.
- piac's reading of MLIR's semantics becomes part of the trusted base for proved lowerings. It is limited to integer `arith`, `index`, `scf`, `memref`, `tensor` and `linalg.generic`, and tested against MLIR's own reference lowering.
- piac links more of MLIR, which costs build time, a tracked benchmark ([ADR 0032](0032-parallel-sliced-cached-proving.md)); step 1 measures it.
- MLIR's textual syntax becomes part of Pia libraries' source, so an LLVM upgrade that changes an op's syntax breaks the lowerings that use it, at expansion time with MLIR's diagnostic. The generated `Pia.Linalg` is regenerated on each upgrade, as the POSIX bindings are on each SDK.

## Answers to the open questions

Dean answered all three on 2026-11-24, each with the recommended option:

1. **The surface:** one attribute, `@lower`, carrying MLIR text with `$` splices, or a metaprogram that returns it, on an ordinary `let` (section 1). There is no MLIR quote language, and no MLIR ops inline in expressions.
2. **The body:** every lowered function keeps a Pia body, as its specification and its fallback. There are no lowerings with only a contract, not even in `@trusted` modules. A foreign function without a body stays an `extern`.
3. **Schedules:** `@schedule` holds transform-dialect scripts, trusted as compiler passes and listed in the trust report until step 8 validates them (section 2). A friendlier Pia vocabulary, if one is wanted later, is metaprograms that write these scripts.

## Notes from step 1

Step 1 (trusted lowerings on the CPU) is implemented as decided, with these details settled in the code ([codegen.md](../codegen.md#lowerings-written-in-pia)):

- **Placement.** `@lower(...)` goes where every other function attribute goes, after the return type and before `requires`, as `@opaque` and `@variadic` do, not after `ensures` as the sketch in section 1 shows.
- **The wrapper.** MLIR's parser takes the text as the body of `func.func @pia_lowering` with the function's core signature, with `return` added for a function that returns nothing; a function that returns an integer or a bool writes its own `return`. The body is moved into the real function, every op located at the attribute.
- **Splices and results.** A spliced parameter is an integer, a bool or a buffer of them, since a record is several values once records are scalarized; a lowered function returns unit, an integer or a bool, since an array result becomes a buffer the caller makes after IRGen.
- **Named ops on memrefs.** `linalg.matmul` and the other named ops verify on memrefs, so step 1 needs no tensors: `memref.expand_shape` views a `[i8; 16]` as `memref<4x4xi8>`, and `convert-linalg-to-loops`, `expand-strided-metadata` and `lower-affine` take the result to the existing passes. `tensor` and `bufferization` are linked and registered but nothing bufferises yet (step 6). `transform` is linked and registered for step 5.
- **The certificate.** Format 2 adds a `trusted <kind> <name> <hash> <ops>` line, written only by an object that has a lowering, so every other object stays format 1 and older readers still read it. The other trusted kinds of docs/abi.md are not recorded in certificates yet.
