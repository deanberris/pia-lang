# Work in progress: Gif.Lzw's whole-stream theorem (#339, ADR 0058)

Not built or tested by Bazel. Prove with piac from this branch, after writing
the Bits and Gif.Spec interfaces into a directory `if`:

    piac --emit=interface -o if wip/lzw-whole-stream/Ref.pia
    piac --verify --iface-path=if wip/lzw-whole-stream/Ref.pia
    piac --verify --verify-only=sym_is_x --iface-path=if wip/lzw-whole-stream/Lzw.pia

- `Ref.pia` is GIF89a's LZW reading of a code stream as a trace spec:
  `lzw_ok s m x k tp tw tc to te` says that x is what s decodes to, by the
  trace of its k codes (bit position, width, code, output offset, epoch
  start). Proved: 110 goals, about 9 s.
- `Lzw.pia` is Gif.Lzw plus `link` (entry kk of the table as the trace says
  it was built), the lemma `sym_is_x` (an entry's string is the bytes of x
  the trace names, by induction on the prefix chain; proved, 25 goals, one
  costly at 26% of the limit), add_entry's frame, and `decode_ref`, decode
  with spec parameters for x and the trace and the guarded theorem
  `h ==> result = Ok (len x) and dst = x`.
- **Not proved:** decode_ref's loop. With lzw_ok anywhere in its context
  (a spec local, or `requires h ==> lzw_ok ...`), even goals the plain decoder
  proves, such as `pos + width` not overflowing, time out. With an opaque
  guard they prove. Next step: keep lzw_ok out of the loop's context by
  moving each piece of trace reasoning into a function or lemma with a small
  contract (add_entry maintaining `link` through spec parameters; one lemma
  per kind of code giving `dst = x` on the new bytes), and handing the loop
  only quantifier-free per-step facts.
