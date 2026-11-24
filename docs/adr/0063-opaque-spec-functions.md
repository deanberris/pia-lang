# 63. Opaque spec functions: a spec function marked `@opaque` keeps its definition out of every goal until a proof reveals it

Date: 2026-11-24

Status: Proposed

## Context

ADR 0058 made whole-stream specifications writable: a reference LZW decoder, or Huffman's canonical code, held in spec state beside the real decoder. Two proofs built on it have stalled in the same way:

- **GIF LZW against its whole-stream spec** (#339, branch `claude/lzw-whole-stream`) proves 229 of 234 goals. The 5 that fail are the step lemmas `emit_kwk` and `link_new`, and two loop invariants after an iteration. A 300 s solver timeout does not help. Changing one lemma's body moved the count from 5 to 17, so the proof is brittle, not merely slow.
- **Huffman's decode against the canonical code** (inflate step 2, branch `claude/huffman-proved`) proves 213 of 220. Putting `kraft l n <= 32768` in `decode`'s precondition made even its old u32 overflow goals time out. They proved again once the call was removed.

The cause is the same in both. [verifier.md](../verifier.md) ("Spec functions") encodes a call `f a` as `F a` with the fact `pre(a) ==> F a = body(a)`, and adds that fact wherever the call appears. A spec over a whole stream or table, such as `lzw_ok`, `kraft` or `tab_from`, has a large body that calls other spec functions. Once it is in a loop's context, every goal in the loop carries the unfolded body and its quantifier instances, including goals that never needed it. The workarounds so far fight this with lemmas whose contracts hide the body. That works, but only after many rounds, and it breaks again when an unrelated body changes.

Dafny, F* and Verus solved this the same way: a function can be opaque. Its definition is a fact only where a proof asks for it.

## Decision

### 1. `@opaque` on a spec function

```ocaml
let spec lzw_ok (s : [u8]) (x : [u8]) (k : usize) : bool @opaque
  requires ...
= ...
```

- At a call to an opaque `f`, the solver gets `F a`, its range and `pre(a) ==> post(a, F a)` (f's `ensures`), but **not** `F a = body(a)`.
- `f`'s own goals are unchanged: its body is still checked, and its `ensures` are proved from its body.
- An imported opaque spec function stays opaque in the importer. The interface carries the attribute.

### 2. `reveal f` makes the definition a fact, from that point to the end of the enclosing block

```ocaml
let lemma emit_kwk (s : [u8]) ... : unit
  requires lzw_ok s x k
  ensures ...
= reveal lzw_ok;
  ...
```

- `reveal f` is a statement in a lemma, a function body or a loop body. Codegen erases it, as it erases lemma calls.
- After it, calls to `f` in that scope get the definition fact as if `f` were not opaque, with the usual `@fuel` depth.
- The intended pattern is to reveal inside small step lemmas, never in the loop of the code itself. The loop then sees only `lzw_ok s x k` as an atom, and the lemmas' contracts.

### 3. Nothing changes for spec functions that are not marked

Default unfolding stays as it is, so every existing proof keeps its meaning and cost.

### 4. Build order

1. `@opaque` and `reveal`, with a test `tests/verify/opaque.pia`. The test covers a goal that fails without `reveal` and proves with it, a reveal scoped to a block, and an imported opaque function.
2. Retry LZW (#339) with `lzw_ok` and the trace functions opaque, revealed only in the step lemmas.
3. Retry Huffman step 2 with `kraft`, `tab_from` and `room` opaque.
4. Record the per-file goal counts and costs before and after, as the ADR 0032 benchmark does.

## Questions for Dean

1. **Should `reveal` be a keyword?** I recommend `reveal f` as a statement, a single imperative word like `assert`. The alternative needs no keyword: an attribute on the lemma or loop, `@reveal(lzw_ok)`, which reveals it in that whole body.
2. **Opt-in, or opaque by default?** I recommend opt-in `@opaque`. Opaque by default (F*'s later choice for big definitions) would change every existing proof, and most of Pia's spec functions are small enough to unfold for free.

## Consequences

- Whole-stream proofs can keep the spec as an atom in loops. A lemma's cost depends on the definitions it reveals, not on everything in scope.
- Proofs become less brittle: changing an opaque function's body affects only the lemmas that reveal it.
- One more attribute, and possibly one more keyword. A proof that forgets to reveal a definition fails with an unproved goal, so the error report should hint "`f` is opaque here; `reveal f` may prove it".

## Prior art

| Source | What Pia takes |
| --- | --- |
| Dafny `{:opaque}` and `reveal f()` | opaque definitions, revealed per proof |
| F* `[@@"opaque_to_smt"]` and `reveal_opaque` | keeping big definitions out of the SMT context |
| Verus `#[verifier::opaque]` and `reveal(f)` | the same, for Rust verification over Z3 |
