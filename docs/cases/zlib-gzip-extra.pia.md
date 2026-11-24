# zlib's gzip extra field

In August 2022, zlib fixed CVE-2022-37434, a heap buffer overflow
in `inflate()`. The CVE record describes a heap-based buffer over-read or
overflow in `inflate.c`, triggered by a large gzip header extra field. Only
programs that ask for the gzip header with `inflateGetHeader()` are
affected, but zlib is in nearly everything, so the advisories ran from
Debian and Fedora to Apple and Siemens, and the record links a curl issue
it tags as an exploit.

The bug is one subtraction whose operands were assumed to be in order.

This page is a literate Pia file,
[`docs/cases/zlib-gzip-extra.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/zlib-gzip-extra.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

A gzip header can carry an extra field of up to 65535 bytes, announced by
a 16-bit length. A program that wants it gives zlib a buffer, `extra`, of
`extra_max` bytes, and zlib copies as much of the field as fits. The field
can arrive over several calls to `inflate()`, so the copy runs in pieces:
`state->length` counts the bytes still to come, and the piece goes at
offset `len = extra_len - state->length`. Before the fix, the code in
`inflate.c` was:

```c
if (state->head != Z_NULL &&
    state->head->extra != Z_NULL) {
    len = state->head->extra_len - state->length;
    zmemcpy(state->head->extra + len, next,
            len + copy > state->head->extra_max ?
            state->head->extra_max - len : copy);
}
```

The length clamps the copy to the space left, `extra_max - len`. That is
right while `len` is inside the buffer. Once the field's earlier pieces
have filled it, `len` is past `extra_max`, the subtraction wraps around to
a huge unsigned number, and `zmemcpy` writes it at `extra + len`, past the
end of the buffer. The [fix][fix], "Fix a bug when getting a gzip header
extra field with inflate()", adds the missing clause to the `if`:
`len < state->head->extra_max`.

## The same shape in Pia

This is not zlib's code; it is the shape of the bug. `have` is how much of
the field came before this piece, a 16-bit count like zlib's, and `chunk`
is the piece. The copy is clamped as zlib clamped it.

<!-- example: extra.pia -->
<!-- expect: fail -->
```ocaml
let copy_extra (extra : borrowed inout mutable [u8]) (have : u16) (chunk : [u8]) : unit
  requires len chunk <= 65535
= let n : usize = if have + len chunk > len extra then len extra - have else len chunk in
  for k in 0..n do extra.[have + k] <- chunk.[k] done
```

`piac` will not compile it:

```console
$ piac --verify extra.pia
extra.pia:3:27: proved: '+' does not overflow usize [smt]
extra.pia:3:66: failed: '-' does not overflow usize
  counterexample: len extra = 0, have = 61438, len chunk = 4101, result = -61438
extra.pia:4:32: proved: '+' does not overflow usize [smt]
extra.pia:4:40: proved: the index is within bounds [smt]
extra.pia:4:20: proved: the index is within bounds [smt]
4 proved, 1 failed, 0 skipped
```

The counterexample is CVE-2022-37434: a buffer smaller than the part of
the field already seen, so `len extra - have` is negative. In C that is a
huge `unsigned`; in Pia it is a goal that does not hold, so the program
never compiles. The copy's own bounds were proved: once `n` is the space
left, every write is inside `extra`. The only gap is the clamp itself.

## The fix, proved

The fixed version is zlib's: copy only while the buffer has room, and
return how far into it the field now reaches. The postcondition says that
never passes its end.

```pia
let copy_extra (extra : borrowed inout mutable [u8]) (have : usize) (chunk : [u8]) : usize
  ensures result <= len extra
= if have < len extra then (
    let n : usize = if len chunk > len extra - have then len extra - have else len chunk in
    for k in 0..n do extra.[have + k] <- chunk.[k] done;
    have + n)
  else len extra
```

Every goal on this page is proved:

```console
$ piac --verify zlib-gzip-extra.pia.md
...
zlib-gzip-extra.pia.md:89:3: proved: the postcondition holds [smt]
7 proved, 0 failed, 0 skipped
```

## Pia's own inflate

Pia's decoder for deflate and zlib, [`Pia.Compress.Inflate`][inflate] and
[`Pia.Compress.Zlib`][zlib] (ADR 0054, step 5), does not read gzip
headers yet, but it copies in the same way: a stored block's LEN bytes,
and every back-reference. Each copy is checked against the input left
and the output left before it starts, and the verifier proves every byte
of it is in bounds, for every input. A back-reference's distance is
proved at most the bytes written so far. When gzip framing comes, its
extra field will be one more copy that has to prove the same thing.

## Sources

- The CVE record, [CVE-2022-37434][cve], published 5 August 2022.
- zlib commit [eff308af425b67093bab25f80f1ae950166bece1][fix], "Fix a bug
  when getting a gzip header extra field with inflate()", by Mark Adler:
  the code before and after.
- The follow-up zlib commit
  [1eb7682f845ac9e9bf9ae35bbfb3bad5dacbd91d][fix2], listed in the CVE
  record.
- curl's report, [curl/curl#9271][curl].

[cve]: https://www.cve.org/CVERecord?id=CVE-2022-37434
[fix]: https://github.com/madler/zlib/commit/eff308af425b67093bab25f80f1ae950166bece1
[fix2]: https://github.com/madler/zlib/commit/1eb7682f845ac9e9bf9ae35bbfb3bad5dacbd91d
[curl]: https://github.com/curl/curl/issues/9271
[inflate]: https://github.com/deanberris/pia-lang/blob/main/lib/Pia/Compress/Inflate.pia
[zlib]: https://github.com/deanberris/pia-lang/blob/main/lib/Pia/Compress/Zlib.pia
