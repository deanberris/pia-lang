# libwebp's Huffman tables

In September 2023, Chrome shipped an urgent fix for CVE-2023-4863, a heap
buffer overflow in libwebp, the library that decodes WebP images in
Chrome, Firefox, Android, and countless apps that embed it. As Ben Hawkes
recounts in ["The WebP 0day"][hawkes], the bug was reported by Apple's
Security Engineering and Architecture team, and Chrome's release notes
said: "Google is aware that an exploit for CVE-2023-4863 exists in the
wild." A crafted image could write past the end of a heap buffer during
decoding, before any of it was displayed.

The code was not careless. Its table sizes came from a careful worst-case
analysis. The analysis just assumed the input was valid, and the code
checked that only after it had written.

This page is a literate Pia file,
[`docs/cases/libwebp.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/libwebp.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

Lossless WebP compresses pixels with Huffman codes, which the image itself
describes. The decoder turns each code into lookup tables: a root table,
plus second-level tables for the longer codes, all built into one
allocation. In `src/dec/vp8l_dec.c` that allocation had a fixed size per
image, taken from a table whose comment explains where its numbers came
from:

```c
// All values computed for 8-bit first level lookup with Mark Adler's tool:
// https://github.com/madler/zlib/blob/v1.2.5/examples/enough.c
#define FIXED_TABLE_SIZE (630 * 3 + 410)
static const uint16_t kTableSize[12] = {
  FIXED_TABLE_SIZE + 654,
```

`enough.c` computes the largest tables any *complete* Huffman code can
need. `BuildHuffmanTable` in `src/utils/huffman_utils.c` then fills the
second-level tables, moving `table` forward by each table's size as it
goes:

```c
if ((key & mask) != low) {
  table += table_size;
  table_bits = NextTableBitSize(count, len, root_bits);
  table_size = 1 << table_bits;
  total_size += table_size;
  ...
}
...
ReplicateValue(&table[key >> root_bits], step, table_size, code);
```

and only after every table is written does it check that the code was
complete:

```c
// Check if tree is full.
if (num_nodes != 2 * offset[MAX_ALLOWED_CODE_LENGTH] - 1) {
  return 0;
}
```

An incomplete code can need more second-level table space than any
complete one, so the worst case `enough.c` computed did not cover it. By
the time the check rejected the code, the writes had already gone past the
end of the allocation; Hawkes' proof of concept writes "as far as 400
bytes past the end". The [fix][fix], "Fix OOB write in BuildHuffmanTable",
reorders the work: "First, BuildHuffmanTable is called to check if the
data is valid. If it is and the table is not big enough, more memory is
allocated."

## The same shape in Pia

This is not libwebp's decoder; it is the shape of the bug. The input
determines a list of second-level table sizes. The builder writes each
table after the previous one, in a buffer whose size was fixed in
advance, and checks at the end whether the code was valid. The invariant
says what the buffer's size was chosen to guarantee: the tables fit.

<!-- example: tables.pia -->
<!-- expect: fail -->
```ocaml
let build (table : out mutable [u16]) (sizes : [u16]) (complete : bool) : usize =
  let pos : mutable usize = 0 in
  for t in 0..len sizes
    invariant pos <= len table
  do
    let size : usize = sizes.[t] in
    for k in 0..size do table.[pos + k] <- 1 done;
    pos <- pos + size
  done;
  if complete then pos else 0
```

`piac` will not compile it:

```console
$ piac --verify tables.pia
...
tables.pia:7:25: failed: the index is within bounds
  counterexample: len table = 1, len sizes = 1, complete = false, index = 1, length = 1
...
tables.pia:4:5: failed: the loop invariant holds after each iteration
  counterexample: len table = 65538, len sizes = 1, complete = false
2 proved, 4 failed, 0 skipped
```

The smallest counterexample is the whole bug: a one-entry buffer and an
input asking for a table bigger than that, so the first write past the
end happens at index 1. (The other two failures are the running offset
overflowing on absurdly large inputs.) Nothing in the builder connects
the sizes the input asks for to the space that was allocated. The worst-case analysis made that connection,
for valid inputs, outside the program, where no compiler could check it,
and the validity check came too late to matter.

## The fix, proved

The rest of this page is the fixed builder. Before writing each table it
checks that the table fits in the space left, and once one does not, it
writes nothing more and reports the input as invalid. That is the same
guarantee libwebp's fix gets from its first, size-only pass: no write
happens until the space for it is known. The postcondition says the
result never claims more space than the buffer has.

```pia
let build (table : out mutable [u16]) (sizes : [u16]) : usize
  ensures result <= len table
=
  let pos : mutable usize = 0 in
  let ok : mutable bool = true in
  for t in 0..len sizes
    invariant pos <= len table
  do
    let size : usize = sizes.[t] in
    if ok && size <= len table - pos then (
      for k in 0..size do table.[pos + k] <- 1 done;
      pos <- pos + size)
    else ok <- false
  done;
  if ok then pos else 0
```

Every goal on this page is proved:

```console
$ piac --verify libwebp.pia.md
...
libwebp.pia.md:135:5: proved: the loop invariant holds after each iteration [smt]
libwebp.pia.md:130:3: proved: the postcondition holds [smt]
8 proved, 0 failed, 0 skipped
```

In Pia, a precomputed worst case can still be used, but only as a
contract the code proves: if `kTableSize` were a precondition, the
builder would have to show its writes stay inside it for every input it
accepts, valid or not.

## What Pia needs for the rest

The real builder derives the table sizes from the code lengths, with
shifts and counts over a 16-entry histogram, and grows the allocation
when a valid code needs more room. Proving the size bound for the real
derivation is a good stress test for the verifier, and growing the
allocation needs the memory module
([ADR 0026](../adr/0026-memory-manager.md)). Pia's own image codecs, which
will have to get exactly this right, are milestone
[M13](https://github.com/deanberris/pia-lang/issues/14).

## Sources

- libwebp commit [902bc9190331343b2017211debcec8d2ab87e17a][fix], "Fix
  OOB write in BuildHuffmanTable.", by Vincent Rabaud, 7 September 2023.
- The code before the fix: [`src/utils/huffman_utils.c`][huff] and
  [`src/dec/vp8l_dec.c`][vp8l] at its parent commit.
- Ben Hawkes, ["The WebP 0day"][hawkes], 21 September 2023: the
  analysis, the report by Apple's SEAR team, the quotation from Chrome's
  release notes and the 400-byte overflow.
- Chrome's [stable channel update of 11 September 2023][chrome].

[fix]: https://github.com/webmproject/libwebp/commit/902bc9190331343b2017211debcec8d2ab87e17a
[huff]: https://github.com/webmproject/libwebp/blob/7ba44f80f3b94fc0138db159afea770ef06532a0/src/utils/huffman_utils.c#L80
[vp8l]: https://github.com/webmproject/libwebp/blob/7ba44f80f3b94fc0138db159afea770ef06532a0/src/dec/vp8l_dec.c#L87
[hawkes]: https://blog.isosceles.com/the-webp-0day/
[chrome]: https://chromereleases.googleblog.com/2023/09/stable-channel-update-for-desktop_11.html
