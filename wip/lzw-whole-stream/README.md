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
