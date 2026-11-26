# Rust's `str::repeat`

Rust is memory-safe by default, and that default is what makes this case
worth studying. On 21 September 2018 the Rust team
[announced][blog] "a security vulnerability affecting the standard
library's `str::repeat` function. When passed a large number this function
has an integer overflow which can lead to an out of bounds write." It
became [CVE-2018-1000810][ghsa]. The [full announcement][announce] calls it
"an instance of CWE-680: Integer Overflow to Buffer Overflow", says it
entered the standard library in a pull request merged on 6 March 2018,
first shipped in Rust 1.26.0, and was fixed in 1.29.1. It credits Scott
McMurray with finding it.

The overflow was in safe code. The out-of-bounds write was in an `unsafe`
block a few lines further down, which trusted what the safe code had
computed.

This page is a literate Pia file,
[`docs/cases/rust-str-repeat.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/rust-str-repeat.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

`str::repeat` calls `[u8]::repeat`, which in Rust 1.29.0
(`src/liballoc/slice.rs`) begins:

```rust
pub fn repeat(&self, n: usize) -> Vec<T> where T: Copy {
    if n == 0 {
        return Vec::new();
    }
    ...
    // Using `Vec` to access `set_len()`.
    let mut buf = Vec::with_capacity(self.len() * n);
```

and then fills the buffer by doubling it, with raw copies:

```rust
            unsafe {
                ptr::copy_nonoverlapping(
                    buf.as_ptr(),
                    (buf.as_mut_ptr() as *mut T).add(buf.len()),
                    buf.len(),
                );
                // `buf` has capacity of `self.len() * n`.
                let buf_len = buf.len();
                buf.set_len(buf_len * 2);
            }
```

The comment is the whole story: "`buf` has capacity of `self.len() * n`."
The unsafe block depends on it, and it is false when `self.len() * n`
overflows. In a release build, Rust's integer arithmetic wraps on
overflow by default, so the capacity silently comes out small, and the
copies write past the end of the allocation. The program the borrow
checker accepted could write anywhere.

## The same code in Pia

The capacity calculation, written as plainly as Rust wrote it:

<!-- example: capacity.pia -->
<!-- expect: fail -->
```ocaml
let capacity (size : usize) (n : usize) : usize = size * n
```

```console
$ piac --verify capacity.pia
capacity.pia:1:56: failed: '*' does not overflow usize
  counterexample: size = 10879383879352893286, n = 17176544054727634905, result = 186870216491998611994851295411633747830
0 proved, 1 failed, 0 skipped
```

By default every Pia multiplication is a goal: it must be proved to fit.
This one does not, and the counterexample is the attack.

## Wrapping does not make it safe

Rust's release builds give overflow a meaning, wrapping, so the
multiplication is "defined". Pia can say the same with
`@overflow(wrap)`, and then the multiplication has nothing left to prove.
But the comment in the Rust source is a claim about the result, so write
it down as one:

<!-- example: capacity_wrap.pia -->
<!-- expect: fail -->
```ocaml
let capacity (size : usize) (n : usize) : usize @overflow(wrap)
  ensures result = size * n
= size * n
```

```console
$ piac --verify capacity_wrap.pia
capacity_wrap.pia:2:3: failed: the postcondition holds
  counterexample: size = 18418166063394745921, n = 12079500963941582858
0 proved, 1 failed, 0 skipped
```

Arithmetic in a contract is exact, so `size * n` in the postcondition is
the true product, and the wrapped result is not equal to it. The comment
the unsafe code relied on becomes a goal, and the goal fails. Defined
behaviour is not correct behaviour.

## The fix, proved

Rust's fix, in 1.29.1, was one line:

```rust
let mut buf = Vec::with_capacity(self.len().checked_mul(n).expect("capacity overflow"));
```

`checked_mul` reports the overflow instead of hiding it, and `expect`
panics on it. The same idea in Pia returns whether the product fits along
with the product, and the postconditions say exactly when it fits and what
it is. A caller cannot get a capacity without the proof that it is the
true one.

The check itself is a saturating multiplication: in an
`@overflow(saturate)` function, a product too big for a `usize` comes out
as the largest `usize`. So a result below that is the true product, and
the largest value itself is treated as overflow, which costs nothing,
since Rust never allocates more than `isize::MAX` bytes anyway.

```pia
let capacity = type { ok : bool; bytes : usize }

let checked_capacity (size : usize) (n : usize) : capacity @overflow(saturate)
  ensures result.ok = (size * n < 18446744073709551615)
  ensures result.ok ==> result.bytes = size * n
=
  let bytes : usize = size * n in
  { ok = bytes < 18446744073709551615; bytes = bytes }
```

Every goal on this page is proved:

```console
$ piac --verify rust-str-repeat.pia.md
rust-str-repeat.pia.md:133:3: proved: the postcondition holds [smt]
rust-str-repeat.pia.md:134:3: proved: the postcondition holds [smt]
2 proved, 0 failed, 0 skipped
```

The postconditions are exact, even in a saturating function: `size * n`
in a contract is the true product, so the first one says `ok` is set
exactly when the product fits. That is the property the Rust code needed
and stated only in a comment.

While this page was being written, the verifier itself had this bug: it
applied a function's overflow mode to the arithmetic in its contracts, so
the wrapping `capacity` above was wrongly proved. The fix landed with this
page, and a test in `tests/verify/spec_exact.pia` keeps it fixed.

## What this says about `unsafe`

Rust's guarantee stops at `unsafe`, and the code inside an `unsafe` block
is only as sound as the facts it assumes. Here the fact was in a comment.
Pia has no `unsafe` for arithmetic or indexing: a fact the code relies on
is a contract, every contract is proved, and a fact that could be false is
a compile error ([ADR 0004](../adr/0004-strongest-guarantee-by-default.md)).

Pia's version of the rest of `repeat`, which allocates the buffer and
fills it, needs the memory module
([ADR 0026](../adr/0026-memory-manager.md)), where every allocation can
fail and the caller must handle it.

## Sources

- The Rust Core Team, ["Security advisory for the standard
  library"][blog], 21 September 2018.
- The full announcement, ["Security advisory for the Rust standard
  library, 2018-09-21"][announce], on the rustlang-security-announcements
  list: the affected versions (1.26.0 to 1.29.0), the fix in 1.29.1, the
  CWE classification, and the credit to Scott McMurray. A later reply on
  the same thread gives the CVE number.
- The code: [`src/liballoc/slice.rs` at 1.29.0][before] and
  [at 1.29.1][after].
- [GitHub Advisory GHSA-2cg9-g249-7mf2][ghsa] for CVE-2018-1000810.

[blog]: https://blog.rust-lang.org/2018/09/21/Security-advisory-for-std/
[announce]: https://groups.google.com/g/rustlang-security-announcements/c/CmSuTm-SaU0
[before]: https://github.com/rust-lang/rust/blob/1.29.0/src/liballoc/slice.rs#L409
[after]: https://github.com/rust-lang/rust/blob/1.29.1/src/liballoc/slice.rs#L423
[ghsa]: https://github.com/advisories/GHSA-2cg9-g249-7mf2
