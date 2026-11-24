# 58. Spec buffers: spec-only arrays that code writes, contracts read and codegen erases

Date: 2026-11-23

Status: Accepted (2026-11-24)

## Context

ADR 0054 promises that the GIF and inflate decoders match a written specification over the whole stream, and that GIF round-trips exactly. Step 2a proved the GIF LZW decoder ([#338](https://github.com/deanberris/pia-lang/pull/338)) total and safe. It also proved that each code writes exactly its dictionary entry's string. It could not state the whole-stream claim: that the output equals what a reference LZW reading of the stream gives ([#339](https://github.com/deanberris/pia-lang/issues/339)). That claim needs the reference's state as a value, and its state evolves code by code. The dictionary after each code, and the sequence of indices so far, are both arrays.

What exists today:

- **Spec-only scalars.** `int`, `real` and the sorts of library theories can be held in spec-only parameters, locals and fields, and code can update them (`t.heap <- Alloc.take t.heap b`, [ADR 0041](0041-allocator-semantics-as-a-theory.md)).
- **Spec-only fields of buffer elements.** These come from [ADR 0048](0048-buffers-whose-elements-hold-slices.md) and `tests/verify/spec_buffers.pia`. A buffer of `{ slot : [u16]; state : int }` keeps `state` as a buffer of its own, which the verifier sees and codegen erases.
- **What is missing.** A buffer whose elements are wholly spec-only, such as `[int]`, is an error, because its length is in code ([verifier.md](../verifier.md), "Spec-only `int` and `real`"). There is no spec-only array whose length is spec-only too. Spec functions cannot return arrays.

The same gap will block three later proofs: the GIF encoder's round trip (ADR 0054 step 3), inflate's conformance against `Inflate.Spec` (step 5), where the sliding window and dynamic Huffman tables evolve over the stream, and any proof that relates a streaming algorithm to its batch specification.

## Decision

### 1. `spec` marks a spec-only local, parameter or field of any type, buffers included

```ocaml
let decode (s : [u8]) (dst : borrowed inout mutable [u8]) : result usize lzw_error
  ensures (match result with
           | Ok n -> forall (i in 0 .. n). dst.[i] = ref_out.[i]
           | Err _ -> true)
= let spec ref_out : mutable [u8; 65536] = zeros in
  let spec ref_dict : mutable [u16; 4096] = zeros in
  ...
```

- A `spec` binding is spec-only, whatever its type. That covers fixed arrays (`[t; n]`), whose length is a constant, and record fields marked `spec`.
- Code may write a spec binding: `ref_out.[o] <- b` and `ref_dict.[k] <- p`. Contracts, loop invariants, `assert`s and lemma calls may read it.
- Nothing that code computes may read a spec binding. Sema checks this by the same rule as spec-only `int`: a spec value can flow only into spec places and into contracts.
- Codegen erases every spec binding and every write to one, as it already erases spec-only state.
- A spec parameter lets a caller and a callee share spec state across a call. A spec result is out of scope for now.

### 2. The whole-stream specs are reference implementations kept in spec state

A whole-stream spec is the reference algorithm, written plainly and run in spec state beside the fast decoder. The theorem is that the two agree at every step. For LZW, the reference keeps its dictionary as explicit strings, in spec buffers of offsets and lengths, and its output as a spec buffer. The decoder's loop invariant says its tables expand to the same strings, and that its output so far equals the reference's.

For the round trip, the encoder keeps the input indices as spec state. The decoder's theorem, applied to the encoder's output, gives the round trip as `forall i. out.[i] = in.[i]`.

### 3. Encoding

A spec buffer is an SMT array, exactly like a real buffer, with no codegen. Writes and reads use the verifier's existing array encoding, so this is mostly a front-end change: the keyword, the flow check and erasure. Spec writes do not count as effects for purity or concurrency: a spec buffer is per-thread spec state.

### 4. Build order

1. `spec` on locals of fixed-array type, with the flow check, erasure and tests in `tests/verify/spec_locals.pia`.
2. Spec parameters.
3. Spec record fields. This generalises ADR 0048's spec-only fields.
4. Use it in `Gif.Lzw` for the whole-stream spec, then in the GIF round trip.

## Dean's answers (2026-11-24)

1. **Keyword: `spec`.** "I don't like the ghost spelling. Let's use spec instead to be consistent." `spec` already marks spec functions, so this adds no keyword: `let spec ref_out : mutable [u8; 65536] = zeros`. A `spec` binding is spec-only whatever its type.
2. **Fixed-size first.** Dean did not answer this one separately, so the proposed default stands until he says otherwise. `spec` buffers start as fixed arrays `[t; n]`, which cover LZW (4096 entries, bounded output) and inflate's 32 KiB window. Unbounded spec sequences need a `seq` sort and can come later as a library theory over Z3 sequences.

## Consequences

- ADR 0054's conformance and round-trip claims become provable, not only tested.
- One more spec-only form joins `int`, `real` and theory sorts. The rule stays one rule: spec-only values flow only into spec-only places.
- Spec state adds solver terms. A large spec buffer adds quantified invariants, so the proof-cost benchmark watches the codec modules that use it.

## Prior art

| Source | What Pia takes |
| --- | --- |
| Dafny `ghost var`, Why3 `ghost`, SPARK `Ghost` aspect | spec-only state that code updates and the compiler erases |
| VeriFast and Viper ghost fields | spec state attached to data structures |
| Senjak and Hofmann, "An implementation of Deflate in Coq" (2016) | a verified streaming codec whose specification is a relation over the whole stream |
