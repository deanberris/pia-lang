# Debugging C++ with the REPL

The REPL can answer questions about code that isn't written in Pia yet. To find out whether a piece of C++ is correct, port it into a session one function at a time, try to prove it, and let each counterexample tell you what to look at next. Nothing is built: there's no `piac` run, no object file and no link, only cells.

This page follows such a session as Claude ran it, using the REPL's [MCP server](repl.md#mcp-server). Each step shows what Claude meant to try (**Claude:**), the cell it sent with the `execute` tool (**→**), the result the server sent back (**←**), and what Claude made of the result before the next call.

## The suspect

A parser reads a little-endian length-prefixed field. A caller finds the field through an offset stored in the file's header:

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

The port is direct. A pointer and its length become a slice: `buf, n` is `buf : [u8]`, and `out, cap` is `dst : out mutable [u8]`. `size_t` is `usize`. The difference that matters is overflow. C++ wraps `size_t` arithmetic silently, but Pia must prove that every `+` doesn't overflow. So a wraparound shows up as a failed obligation, with the values that cause it.

## The session

On the wire, a call is an ordinary MCP `tools/call`, and the result is the REPL's text:

```json
{"name": "execute", "arguments": {"code": "let read_field (buf : [u8]) (pos : usize) ..."}}
```

```json
{"content": [{"type": "text", "text": "[1]:2:10: failed: '+' does not overflow usize\n  counterexample: ..."}], "isError": true}
```

The steps below show the same calls with the code and the text laid out for reading. `[n]` in a result is the cell's number, and `[n]:line:col` is a place in that cell.

### 1. A literal port

**Claude:** I start with `read_field` alone, ported line for line, and send it as one cell.

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
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
```

**← result (isError)**

```text
[1]:2:10: failed: '+' does not overflow usize
  counterexample: len buf = 0, pos = 18446744073709551614, len dst = 0, result = 18446744073709551616
[1]:4:51: failed: the shift amount is less than 8
  counterexample: len buf = 4393147680799327043, pos = 2087023196055266900, len dst = 0, amount = 8
[1]: error: 2 obligations failed; nothing was committed
```

**Claude:** Two failures, and they are different kinds of failure.

The second is my mistake, not the C++'s. C++ promotes `buf[pos + 1]` to `int` before it shifts, but in my port the shift happens at `u8`. I'll put the shift first so that it is typed at `usize`, the type the result is declared with.

The first is worth taking seriously. `pos = 2^64 - 2` makes `pos + 2` overflow. In C++ that sum silently wraps to 0, so the check `0 > n` is false and `buf[pos]` reads far outside the buffer.


### 2. Fix the port

**Claude:** Same function, with the shift written so that it happens at `usize`:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
let read_field (buf : [u8]) (pos : usize) (dst : out mutable [u8]) : usize =
  if pos + 2 > len buf then 0
  else (
    let size : usize = (buf.[pos + 1] << 8) | buf.[pos] in
    if pos + 2 + size > len buf then 0
    else if size > len dst then 0
    else (
      for i in 0 .. size do dst.[i] <- buf.[pos + 2 + i] done;
      pos + 2 + size))
```

**← result (isError)**

```text
[2]:2:10: failed: '+' does not overflow usize
  counterexample: len buf = 0, pos = 18446744073709551614, len dst = 0, result = 18446744073709551616
[2]:5:16: failed: '+' does not overflow usize
  counterexample: len buf = 18446744073709551615, pos = 18446744073709486081, len dst = 0, result = 18446744073709551618
[2]: error: 2 obligations failed; nothing was committed
```

**Claude:** The shift is gone, and what's left are two overflows of `pos + 2`. They only matter if a caller can pass a `pos` that large, so the question is what `read_field` assumes about its callers. The usual contract for a function like this is that `pos` is somewhere inside the buffer. I'll state that as a precondition and see what's left.


### 3. Assume `pos <= n`

**Claude:** I add `requires pos <= len buf`. The body is unchanged:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
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
```

**← result (isError)**

```text
[3]:3:10: failed: '+' does not overflow usize
  counterexample: len buf = 18446744073709551614, pos = 18446744073709551614, len dst = 0, result = 18446744073709551616
[3]:6:16: failed: '+' does not overflow usize
  counterexample: len buf = 18446744073709546496, pos = 18446744073709543167, len dst = 0, result = 18446744073709577512
[3]: error: 2 obligations failed; nothing was committed
```

**Claude:** Better. Every counterexample now needs a buffer within a few kilobytes of 2^64 bytes, which no real program has. C++ promises as much: no object is larger than `PTRDIFF_MAX`, which is 2^63 - 1 on a 64-bit target. That is a fact about the platform, not a guess, so I'll state it too.


### 4. Add the object size limit

**Claude:** A second precondition, `len buf <= PTRDIFF_MAX`:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
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
```

**← result**

```text
read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize  (* 15 proved *)
```

**Claude:** Proved, all 15 obligations. So the C++ `read_field` is correct for every caller that keeps `pos <= n`. The next question is whether the real caller does that.


### 5. Port the caller

**Claude:** `read_name` takes the offset from the first four bytes of the file:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
let read_name (buf : [u8]) (dst : out mutable [u8]) : usize
  requires len buf <= 9223372036854775807
= if len buf < 4 then 0
  else (
    let off : usize = (buf.[3] << 24) | (buf.[2] << 16) | (buf.[1] << 8) | buf.[0] in
    read_field buf off dst)
```

**← result (isError)**

```text
[5]:6:5: failed: the precondition of 'read_field' holds
  counterexample: len buf = 8190, len dst = 0
[5]: error: 1 obligation failed; nothing was committed
```

**Claude:** It doesn't. The offset comes from the file, so an 8 KB file can name any offset up to 4 GB, and `read_field`'s precondition fails. That alone doesn't make the C++ wrong, though. `pos <= n` was my guess at a contract, not something the code needs. What the caller really guarantees is that `pos` fits in 32 bits. I'll ask whether the unchanged body is safe under that guarantee instead.


### 6. Ask about the caller's real guarantee

**Claude:** `:redef` replaces `read_field` with the same body and the precondition `pos <= 2^32 - 1`:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
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
```

**← result**

```text
read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize  (redefined)  (* 15 proved *)
```

**Claude:** The unchanged body is proved under that precondition too. Now I'll send the caller again.


### 7. Try the caller again

**Claude:** The same `read_name` as before:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
let read_name (buf : [u8]) (dst : out mutable [u8]) : usize
  requires len buf <= 9223372036854775807
= if len buf < 4 then 0
  else (
    let off : usize = (buf.[3] << 24) | (buf.[2] << 16) | (buf.[1] << 8) | buf.[0] in
    read_field buf off dst)
```

**← result**

```text
read_name : (buf : [u8]) -> (dst : out mutable [u8]) -> usize  (* 15 proved *)
```

**Claude:** Proved. So on a 64-bit target the original C++ is safe. A 32-bit offset plus 2 can't wrap a 64-bit `size_t`, so an offset past the end of the file fails the first check and `read_field` returns 0.

That argument depends on `size_t` being wider than the offset. On a 32-bit target it isn't, so I'll check that case next.


### 8. A 32-bit `size_t`

**Claude:** The same code with `u32` in place of `size_t`, and the 32-bit `PTRDIFF_MAX`:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
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
```

**← result (isError)**

```text
[8]:4:10: failed: '+' does not overflow u32
  counterexample: len buf = 0, pos = 4294967294, len dst = 0, result = 4294967296
[8]: error: 1 obligation failed; nothing was committed
```

**Claude:** That's the bug. On a 32-bit build, a file whose header says `0xFFFFFFFE` makes `pos + 2` wrap to 0. The check passes, and `buf[0xFFFFFFFE]` is read: an out-of-bounds read controlled by the file.

The fix is to compare against what's left of the buffer instead of adding to `pos`. `n - pos` can't wrap once `pos <= n` has been checked.


### 9. Fix it for 32 bits

**Claude:** The rewritten checks, with no precondition on `pos` at all:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
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
```

**← result**

```text
read_field32 : (buf : [u8]) -> (pos : u32) -> (dst : out mutable [u8]) -> u32  (* 17 proved *)
```

**Claude:** Proved. Now the same fix in the 64-bit version, which `read_name` already calls.


### 10. Fix it for 64 bits

**Claude:** `:redef` again, this time with no preconditions. I also add an `ensures` that the position returned is never past the end of the buffer:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
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
```

**← result**

```text
read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize  (redefined)  (* 16 proved *)
```

**Claude:** Proved, and with no assumption at all, not even the object size limit. `:redef` also proves everything that uses `read_field` again, so `read_name` still holds against the fixed version. Its call needs no change.


### 11. Check the environment

**Claude:** Last, I list the environment to see what the session ended with:

**→ `execute`**

<!-- untested: a REPL cell; the whole session is checked at the end of the page -->
```ocaml
:env
```

**← result**

```text
[7] let read_name : (buf : [u8]) -> (dst : out mutable [u8]) -> usize
[9] let read_field32 : (buf : [u8]) -> (pos : u32) -> (dst : out mutable [u8]) -> u32
[10] let read_field : (buf : [u8]) -> (pos : usize) -> (dst : out mutable [u8]) -> usize
```

**Claude:** The fixed `read_field` from cell 10, the 32-bit version, and `read_name`, all proved together.

## The verdict

`read_field` is correct whenever `pos <= n`, and `read_name` breaks that contract. On 64-bit targets that's harmless. On 32-bit targets it's an out-of-bounds read that the file controls. The fix, in C++:

```cpp
if (pos > n || n - pos < 2) return 0;
size_t len = buf[pos] | (buf[pos + 1] << 8);
if (len > n - pos - 2 || len > cap) return 0;
```

This is proved for both widths, with no assumptions about `pos`.

## What the REPL adds

- **Assumptions are explicit and cheap to change.** Each assumption (`pos <= n`, the object size limit, `pos < 2^32`) went in as a precondition in a cell of its own. Each counterexample showed which one was missing, and a wrong guess cost one cell.
- **`:redef` answers "who relies on this?".** Changing `read_field`'s contract proved `read_name` again against it. That's how "safe on 64-bit, unsafe on 32-bit" was settled instead of argued.
- **Read each failure against the source language's rules.** The REPL reports a mistake in the port (the `u8` shift) the same way as a bug in the original. C++ promotes small integers before it shifts, but it really does wrap `size_t`, so only the overflow is a finding.

## Replaying the session

The documentation tests replay the whole session through `pia repl`, which prints the same text as the MCP server, so the results above can't drift from what Pia really says:

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
