---
name: pia-proof-debugging
description: Find out whether C, C++ or other code is correct by porting it into Pia REPL cells and working through counterexamples one assumption at a time, then report a verdict and a fix. Use when asked if code has an overflow, out-of-bounds access or contract bug, or when a Pia proof fails and you need to find out why.
---

# The proof-debugging loop

A Pia REPL session can answer "is this code correct?" without building anything. Port the code into cells, try to prove it, and let each counterexample tell you what to look at next. Each assumption goes in as a precondition of its own, so the session ends with an exact statement of what the code needs from its callers, and whether its callers provide it.

Use the REPL through the `pia mcp` server (`pia-mcp` skill) or `pia repl` (`pia-repl` skill). The worked example in [docs/repl-debugging.md](../../docs/repl-debugging.md) follows a whole session on a length-prefixed parser that is safe on 64-bit and an out-of-bounds read on 32-bit.

## 1. Port faithfully, one function at a time

Port the callee first, line for line, with no contracts. Callers come later, because they are proved against the callee's contract.

| C / C++ | Pia |
| --- | --- |
| `const T* p, size_t n` | `p : [T]` (a slice; `n` is `len p`) |
| `T* out, size_t cap` | `out : out mutable [T]` (`cap` is `len out`) |
| `T* out` with no length | `out : out mutable [T]`, plus the assumption about its size as a `requires` later |
| `size_t`, `uint32_t`, `int` | `usize`, `u32`, `i32` |
| `for (i = 0; i < n; ++i)` | `for i in 0 .. n do ... done` |
| `while (c) { ... }` | `while c invariant ... decreases ... do ... done` |
| early `return 0` | `if ... then 0 else (...)` |
| unsigned arithmetic that is meant to wrap | the function marked `@overflow(wrap)` after its result type |

Keep the port's arithmetic as written. Do not "fix" it while porting: a wraparound in the original should show up as a failed goal.

## 2. Classify every failure before changing anything

For each failed goal, decide which of these it is, using the **source language's** rules:

1. **A porting artifact.** The port does something the original does not. Typical: C promotes small integers to `int` before shifting or adding, so `buf[i] << 8` is fine in C, but at `u8` in Pia it fails `the shift amount is less than 8`. Fix the port, not the code.
2. **Defined behaviour that is intended.** Unsigned wraparound in a checksum or hash is defined in C and meant. Port it with `@overflow(wrap)`, and it is no longer a goal.
3. **A missing assumption.** The counterexample needs inputs the callers never produce: a buffer near 2^64 bytes, a `pos` past the end. State it as a `requires`, *one per cell*, so each one is visible. Prefer assumptions that are platform facts (no object is larger than `PTRDIFF_MAX`) over guesses.
4. **A real bug.** The counterexample is an input a caller can produce. Keep it: it is the finding.

Do not read meaning into the exact numbers in a counterexample. Z3 picks whichever model it finds first. Ask what class of input they belong to.

## 3. Check each assumption against the real callers

An assumption is only a guess at a contract until a caller is proved against it. Port each caller and send it. If it fails `the precondition of 'f' holds`, the counterexample is a real input that breaks the assumption. Then ask what the caller *does* guarantee, and `:redef` the callee with that weaker precondition and the same body. `:redef` proves every user of the callee again, so one cell answers "is the original body safe for the inputs it really gets?".

## 4. Fix, and prove the fix without the assumption

Rewrite the code so the assumption is no longer needed: compare against what is left (`n - pos < 2`) instead of adding to a position (`pos + 2 > n`), clamp a count, check before subtracting. Prove the fix with as few `requires` as possible, ideally none, and with an `ensures` that callers can use. Re-send the callers, or rely on `:redef` having proved them again.

## 5. Report

Give the verdict in terms of the original code: what it is correct for, which caller or platform breaks it, the input that does it, and the fix in the original language. List the assumptions that remain (each `requires`) and whether each is a platform fact or a caller obligation. Keep the session: as a `pia repl` file with its output (see `pia-repl`), so anyone can replay it.

## Example: a tail copy and a checksum

```cpp
// Copies the last k bytes of src into dst.
void tail(const uint8_t* src, size_t n, uint8_t* dst, size_t k) {
  for (size_t i = 0; i < k; ++i) dst[i] = src[n - k + i];
}
void last4(const uint8_t* src, size_t n, uint8_t* dst) { tail(src, n, dst, 4); }

uint16_t checksum(const uint8_t* p, size_t n) {
  uint16_t s = 0;
  for (size_t i = 0; i < n; ++i) s += p[i];
  return s;
}
```

The cells, one `execute` each, replayed through `pia repl`:

<!-- repl: tail.pia -->
```ocaml
let tail (src : [u8]) (dst : out mutable [u8]) (k : usize) : unit =
  for i in 0 .. k do dst.[i] <- src.[len src - k + i] done
let tail (src : [u8]) (dst : out mutable [u8]) (k : usize) : unit
  requires k <= len dst
= for i in 0 .. k do dst.[i] <- src.[len src - k + i] done
let tail (src : [u8]) (dst : out mutable [u8]) (k : usize) : unit
  requires k <= len dst
  requires k <= len src
= for i in 0 .. k do dst.[i] <- src.[len src - k + i] done
let last4 (src : [u8]) (dst : out mutable [u8]) : unit
  requires len dst >= 4
= tail src dst 4
:redef let tail (src : [u8]) (dst : out mutable [u8]) (k : usize) : usize
  requires k <= len dst
  ensures result <= k && result <= len src
= let m : usize = if k < len src then k else len src in
  for i in 0 .. m do dst.[i] <- src.[len src - m + i] done;
  m
let last4 (src : [u8]) (dst : out mutable [u8]) : usize
  requires len dst >= 4
= tail src dst 4
let checksum (p : [u8]) : u16 =
  let s : mutable u16 = 0 in
  for i in 0 .. len p do s <- s + p.[i] done;
  s
let checksum (p : [u8]) : u16 @overflow(wrap) =
  let s : mutable u16 = 0 in
  for i in 0 .. len p do s <- s + p.[i] done;
  s
```

```console
$ pia repl < tail.pia
...
```

What each step shows:

- **Cell 1**, the literal port, fails at `dst.[i]` (C has no `cap`, so the port has no reason to believe `dst` holds `k` bytes) and at `len src - k` (it underflows when `k > n`).
- **Cell 2** states the first as an assumption: callers allocate `dst` for `k` bytes. The underflow remains, and that one is real: in C, `n - k` wraps to a huge index when `k > n`.
- **Cell 3** assumes `k <= n` as well, and proves. So `tail` is correct exactly when callers keep `k <= n`.
- **Cell 4**, the real caller, fails `the precondition of 'tail' holds` with `len src` below 4: `last4` on a short buffer is the out-of-bounds read.
- **Cell 5** fixes `tail` by clamping, with no assumption about `src`, and returns how many bytes it copied. **Cell 6**, the same caller, proves.
- **Cell 7**, `checksum`, fails at `s + p.[i]`. That is not a bug: unsigned wraparound is defined in C, and a checksum means it. **Cell 8** says so with `@overflow(wrap)`, and proves.

Verdict: `tail` reads out of bounds whenever `k > n`, which `last4` allows for any input shorter than 4 bytes. Fix: copy `min(k, n)` bytes and return the count. `checksum` is correct.
