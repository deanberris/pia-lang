# Work in progress: Gif.Lzw's whole-stream theorem (#339, ADR 0058)

Not built or tested by Bazel. Prove with piac from this branch, after writing
the Bits and Gif.Spec interfaces into a directory `if`:

    piac --emit=interface -o if wip/lzw-whole-stream/Ref.pia
    piac --verify --iface-path=if wip/lzw-whole-stream/Ref.pia
    piac --verify --verify-only=sym_is_x --iface-path=if wip/lzw-whole-stream/Lzw.pia

- `Ref.pia` is GIF89a's LZW reading of a code stream as a trace spec:
  `lzw_ok s m x k tp tw tc to te` says that x is what s decodes to, by the
  trace of its k codes (bit position, width, code, output offset, epoch
  start). It is a recursion, `lzw_from j`, one code at a time, with no
  quantifier over the codes: a quantified `forall j. lzw_step j` swamped
  every goal of a loop whose context held it. Proved: 113 goals, about 3 s.
- `Lzw.pia` is Gif.Lzw plus:
  - `link`, entry kk of the table as the trace built it;
  - `sym_is_x`, an entry's string is the bytes of x the trace names, by
    induction on the prefix chain (proved; its forall ensures is costly);
  - `emit_code`, `emit_kwk` and `link_new`, one lemma per kind of step, each
    taking `clear` as a parameter so its terms match the loop's;
  - add_entry's frame;
  - `decode_ref`, decode with spec parameters for x, the trace and a guard
    h, and the theorem `h ==> result = Ok (len x) and dst = x`.
- **Status:** 229 of 234 goals prove (`--verify-only=decode_ref
  --verify-only=sym_is_x --verify-only=emit_code --verify-only=emit_kwk
  --verify-only=link_new`, 20 s timeout, about 6 min on 4 threads). Five
  time out: emit_kwk's two string postconditions and one stepping assert,
  link_new's postcondition, and two of the loop's invariants after an
  iteration (`dst = x` on [0, o), and `link` for every entry). More asserts
  in those places made things worse (12 failed): the next step is to make
  emit_kwk and link_new state their facts about x with explicit indices
  and no `if` chains (helpers in Ref for "x copies at a"), and to give the
  loop's two quantified invariants their own preservation lemmas.

## Two more rounds (2026-11-24), both worse than the best version

The best version is `Lzw.pia` here: 229 of 234 goals. `attempts/Lzw_wrappers.pia`
is the last attempt, 327 of 343 (16 unproved), which tried:

- `Ref.emit_entry` and `Ref.emit_root`: emit_ok's facts with the entry's index
  explicit and no `if` (these prove, and stay in `Ref.pia`);
- `put_entry_x`, `append_kwk_x` and `add_entry_x`: wrappers with spec
  parameters that carry `dst = x` and `link` through each call, so the loop's
  two quantified invariants are a callee's postcondition;
- `link` split into `link_tr`, which reads only the trace, and the table's
  two cells, so a write to other entries' cells leaves it as it was.

Each of these made more goals time out, not fewer: the wrappers' and lemmas'
own postconditions (put_entry_x, add_entry_x, emit_kwk, link_new) and the
preconditions at their call sites. The quantified facts in their contracts
match each other's terms poorly. What may work instead: state the copy
relation with an explicit witness index per byte (a spec function `src j d`
for "byte d of code j comes from position ..."), so every fact is about one
array cell and no proof needs to match two foralls.

## For issue #339 (not posted)

The five goals still unproved, in `wip/lzw-whole-stream/Lzw.pia`, all timeouts at 20 s:

1. `Lzw.pia:289`: emit_kwk's postcondition `S.elen t clear p + 1 = to.[q + 1] - to.[q]`
2. `Lzw.pia:296`: emit_kwk's assert `to.[q + 1] - to.[q] = to.[q] - to.[q - 1] + 1`
3. `Lzw.pia:313`: link_new's postcondition `link t clear x tc to te.[q] nx`
4. `Lzw.pia:361`: the loop invariant `h ==> forall (i in 0 .. o). dst.[i] = x.[i]`, after an iteration
5. `Lzw.pia:369`: the loop invariant that every entry below nx is as `link` says, after an iteration

What proves: `Ref.pia` (155 goals, about 3 s), `sym_is_x`, `emit_code`, and 229 of decode_ref's 234 goals. The GIF round trip, which needs the same kind of trace from the encoder, is not started.

## Rounds A and B (2026-11-24)

- A: the best version with a 300 s solver timeout instead of 20 s: the same
  five goals time out (13 min on 4 threads). They need a different proof,
  not more time.
- B: emit_kwk and link_new call the proved `Ref.emit_entry` and
  `Ref.emit_root` instead of unfolding emit_ok, with nothing else changed:
  17 unproved, including loop invariants that proved before. Changing one
  lemma's body moves which quantifier instances Z3 tries in the loop's
  goals, so this proof is brittle as it stands.

Not attempted: making the copy relation pointwise, a spec array `src` over
output positions with `x.[i] = x.[src.[i]]` or a root, which would replace
the `forall d` inside emit_ok and link with one cell per fact.

## With @opaque (ADR 0063), 2026-11-24

`lzw_ok`, `lzw_from`, `emit_ok` and `link_tr` are opaque, revealed only in
small lemmas (`Ref.from_step`, `ok_start`, `emit_entry`, `emit_root`,
`emit_overrun`; `sym_is_x`, `link_new`). The loop takes each code's facts
from `step_when` and `emit_when`, and the wrappers `put_entry_x`,
`append_kwk_x` and `add_entry_x` carry its `dst = x` and `link`
invariants through each call.

- Before opaque: 289 of 301 goals, cost 1.33e9, 3 min.
- Now: 477 of 481, cost 1.24e9, 2.5 min. Both loop invariants, and the
  postconditions of `sym_is_x` and `link_new`, prove.
- Left: four stepping asserts those postconditions rest on.
  - `Lzw.pia:299` and `:300`, in `sym_is_x`: the copy relation from `link_tr`,
    and its chain to `S.sym`.
  - `Lzw.pia:387` and `:394`, in `link_new`: `link_tr` for the new entry,
    in the root and entry branches.
