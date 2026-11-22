# Debugging C++ with the REPL

The REPL is useful for code that is not written in Pia yet. To find out whether a piece of C++ is correct, port it into a session one function at a time, try to prove it, and let each counterexample tell you what to look at next. Nothing is built: there is no `piac` run, no object file and no link, only cells. This page follows one such session. Claude ran it through the [MCP server](repl.md#mcp-server) with the `execute` tool, and the session is reproduced below with `pia repl`, which prints the same text.

## The suspect

A parser reads a little-endian length-prefixed field, and a caller finds the field through an offset stored in the file's header:

```cpp
// Copies the field at `pos` to `out` and returns the position after it,
// or 0 on malformed input.
size_t read_field(const uint8_t* buf, size_t n, size_t pos,
                  uint8_t* out, size_t cap) {
  if (pos + 2 > n) return 0;
  size_t len = buf[pos] | (buf[pos + 1] << 8);
  if (pos + 2 + len > n) return 0;
  if (len > cap) return 0;
  for (size_t i = 0; i < len; ++i) out[i] = buf[pos + 2 + i];
  return pos + 2 + len;
}

// The name field's offset is in the first 4 bytes of the file.
size_t read_name(const uint8_t* buf, size_t n, uint8_t* out, size_t cap) {
  if (n < 4) return 0;
  uint32_t off = buf[0] | buf[1] << 8 | buf[2] << 16 | (uint32_t)buf[3] << 24;
  return read_field(buf, n, off, out, cap);
}
```

Every access is behind a bounds check, and the checks look right. The question is whether they are.

The port is direct. A pointer and its length become a slice, so `buf, n` is `buf : [u8]` and `out, cap` is `dst : out mutable [u8]`. `size_t` is `usize`. The one difference that matters is that C++ wraps `size_t` arithmetic silently, while Pia proves that every `+` does not overflow, so a wraparound shows up as a failed obligation with the values that cause it.

## The investigation

Each step below is one cell of the session at the end of the page, and `[n]` in the output is its cell number.

1. **A literal port (cell 1)** fails twice. `pos + 2` overflows when `pos = 2^64 - 2`. In C++ that sum wraps to 0, the check `0 > n` is false, and `buf[pos]` reads far outside the buffer. The second failure, a shift of a `u8` by 8, is the port's fault, not the C++'s: C++ promotes `buf[pos + 1]` to `int` before it shifts. Putting the shift first, as `(buf.[pos + 1] << 8) | buf.[pos]`, types it at `usize`.
2. **With the shift fixed (cell 2)**, both failures are overflows of `pos + 2`. Whether they matter depends on what callers pass, so the next cells state assumptions as preconditions.
3. **The usual contract, `pos <= n` (cell 3).** Every counterexample now needs a buffer within a few kilobytes of 2^64 bytes. No C++ object is larger than `PTRDIFF_MAX`, 2^63 - 1 bytes on a 64-bit target, so that is a fact about the platform and can be stated too.
4. **With the object size limit (cell 4)**, `read_field` is proved: the C++ is correct for every caller that keeps `pos <= n`.
5. **The real caller (cell 5) does not.** Its offset comes from the file, so an 8 KB file can name any offset up to 4 GB, and the call fails `read_field`'s precondition.
6. **What the caller does guarantee (cells 6 and 7).** `:redef` keeps the body exactly as it was and states the caller's real guarantee instead, `pos < 2^32`. The body is proved again, and then `read_name` is proved against it. So on a 64-bit target the original C++ is safe: a 32-bit offset plus 2 cannot wrap a 64-bit `size_t`, so an offset past the end fails the first check and returns 0.
7. **A 32-bit target (cell 8).** The same code with `u32` for `size_t`, and the 32-bit `PTRDIFF_MAX`, fails with `pos = 4294967294`. That is the bug: on a 32-bit build, a file whose header says `0xFFFFFFFE` makes `pos + 2` wrap to 0, the check passes, and `buf[0xFFFFFFFE]` is read.
8. **The fix (cells 9 and 10)** compares against what is left of the buffer, `n - pos`, instead of adding to `pos`. It is proved for both widths with no precondition on `pos`, and the 64-bit version needs no object size limit either. It also ensures that the position it returns is never past the end. `:redef` proves `read_name` again against it, so the caller needs no change.

The verdict: `read_field` is correct whenever `pos <= n`, and `read_name` breaks that contract. On 64-bit targets that is harmless. On 32-bit targets it is an out-of-bounds read controlled by the file. The C++ fix is:

```cpp
if (pos > n || n - pos < 2) return 0;
size_t len = buf[pos] | (buf[pos + 1] << 8);
if (len > n - pos - 2 || len > cap) return 0;
```

## The session

<!-- repl: debug.pia -->
```ocaml
let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize =
  if pos + 2 > len buf then 0
  else (
    let size : usize = buf.[pos] | (buf.[pos + 1] << 8) in
    if pos + 2 + size > len buf then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize =
  if pos + 2 > len buf then 0
  else (
    let size : usize = (buf.[pos + 1] << 8) | buf.[pos] in
    if pos + 2 + size > len buf then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize
  requires pos <= len buf
= if pos + 2 > len buf then 0
  else (
    let size : usize = (buf.[pos + 1] << 8) | buf.[pos] in
    if pos + 2 + size > len buf then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize
  requires len buf <= 9223372036854775807
  requires pos <= len buf
= if pos + 2 > len buf then 0
  else (
    let size : usize = (buf.[pos + 1] << 8) | buf.[pos] in
    if pos + 2 + size > len buf then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
let read_name (buf : [u8]) (dst : out mutable [u8]) : usize
  requires len buf <= 9223372036854775807
= if len buf < 4 then 0
  else (
    let off : usize = (buf.[3] << 24) | (buf.[2] << 16) | (buf.[1] << 8) | buf.[0] in
    read_field buf off dst)
:redef let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize
  requires len buf <= 9223372036854775807
  requires pos <= 4294967295
= if pos + 2 > len buf then 0
  else (
    let size : usize = (buf.[pos + 1] << 8) | buf.[pos] in
    if pos + 2 + size > len buf then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
let read_name (buf : [u8]) (dst : out mutable [u8]) : usize
  requires len buf <= 9223372036854775807
= if len buf < 4 then 0
  else (
    let off : usize = (buf.[3] << 24) | (buf.[2] << 16) | (buf.[1] << 8) | buf.[0] in
    read_field buf off dst)
let read_field32 (buf : [u8]) (pos : u32) (dst : out mutable [u8]) : u32
  requires len buf <= 2147483647
= let n : u32 = len buf in
  if pos + 2 > n then 0
  else (
    let size : u32 = (buf.[pos + 1] << 8) | buf.[pos] in
    if pos + 2 + size > n then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
let read_field32 (buf : [u8]) (pos : u32) (dst : out mutable [u8]) : u32
  requires len buf <= 2147483647
= let n : u32 = len buf in
  if pos > n then 0
  else if n - pos < 2 then 0
  else (
    let size : u32 = (buf.[pos + 1] << 8) | buf.[pos] in
    if size > n - pos - 2 then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
:redef let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize
  ensures result = 0 || result <= len buf
= if pos > len buf then 0
  else if len buf - pos < 2 then 0
  else (
    let size : usize = (buf.[pos + 1] << 8) | buf.[pos] in
    if size > len buf - pos - 2 then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
:env
```

```console
$ pia repl < debug.pia
[1]:2:10: failed: '+' does not overflow usize
  counterexample: len buf = 0, pos = 18446744073709551614, len dst = 0, result = 18446744073709551616
[1]:4:51: failed: the shift amount is less than 8
  counterexample: len buf = 4393147680799327043, pos = 2087023196055266900, len dst = 0, amount = 8
[1]: error: 2 obligations failed; nothing was committed
[2]:2:10: failed: '+' does not overflow usize
  counterexample: len buf = 0, pos = 18446744073709551614, len dst = 0, result = 18446744073709551616
[2]:5:16: failed: '+' does not overflow usize
  counterexample: len buf = 18446744073709551615, pos = 18446744073709486081, len dst = 0, result = 18446744073709551618
[2]: error: 2 obligations failed; nothing was committed
[3]:3:10: failed: '+' does not overflow usize
  counterexample: len buf = 18446744073709551614, pos = 18446744073709551614, len dst = 0, result = 18446744073709551616
[3]:6:16: failed: '+' does not overflow usize
  counterexample: len buf = 18446744073709546496, pos = 18446744073709543167, len dst = 0, result = 18446744073709577512
[3]: error: 2 obligations failed; nothing was committed
read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize  (* 15 proved *)
[5]:6:5: failed: the precondition of 'read_field' holds
  counterexample: len buf = 8190, len dst = 0
[5]: error: 1 obligation failed; nothing was committed
read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize  (redefined)  (* 15 proved *)
read_name : (buf : [u8]) -> (dst : out mutable [u8]) -> usize  (* 15 proved *)
[8]:4:10: failed: '+' does not overflow u32
  counterexample: len buf = 0, pos = 4294967294, len dst = 0, result = 4294967296
[8]: error: 1 obligation failed; nothing was committed
read_field32 : (buf : [u8]) -> (pos : u32) -> (dst : out mutable [u8]) -> u32  (* 17 proved *)
read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize  (redefined)  (* 16 proved *)
[7] let read_name : (buf : [u8]) -> (dst : out mutable [u8]) -> usize
[9] let read_field32 : (buf : [u8]) -> (pos : u32) -> (dst : out mutable [u8]) -> u32
[10] let read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize
```

## What the REPL adds

- **Assumptions are explicit and cheap to change.** Each assumption, `pos <= n`, the object size limit and `pos < 2^32`, went in as a precondition in a cell of its own, and each counterexample showed which one was missing. A wrong guess costs one cell.
- **`:redef` answers "who relies on this?".** Changing `read_field`'s contract proved `read_name` again against it, which is how "safe on 64-bit, unsafe on 32-bit" was settled instead of argued.
- **Read each failure against C++'s rules.** The REPL reports a mistake in the port (the `u8` shift) the same way as a bug in the original. C++ promotes small integers before it shifts, but it really does wrap `size_t`, so only the second is a finding.
