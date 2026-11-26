# Rust's `VecDeque::reserve`

On 24 September 2017 a Rust user reported
["seg fault pushing on either side of a VecDeque"][issue], in safe code,
on Rust 1.19 and 1.20. Steven Fackler reduced it to four lines the same
day:

```rust
let mut deque = VecDeque::with_capacity(32);
deque.push_front(0);
deque.reserve(31);
deque.push_back(0);
```

Valgrind reported an "Invalid write of size 4", "0 bytes after a block of
size 256 alloc'd". The standard library's double-ended queue was writing
past the end of its own buffer. The bug, later
[CVE-2018-1000657][ghsa], had been there since Rust 1.3.0, and the
advisory lists 1.22.0 as the first fixed release.

The fix was one comparison.

This page is a literate Pia file,
[`docs/cases/rust-vecdeque.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/rust-vecdeque.pia.md).
The `pia` blocks are the fixed program, which the test suite proves, and
the other code blocks are the broken versions, each checked to fail
exactly as shown.

## The bug

A `VecDeque` is a ring buffer: a buffer of `cap` slots, a power of two,
with the elements running from `tail` round to `head`, possibly wrapping
past the end. When the buffer grows, the elements that wrapped must be
moved so they are contiguous again. That is `handle_cap_increase`, an
`unsafe` function in `src/liballoc/vec_deque.rs`. Its middle case moves
the wrapped part to just after the old end:

```rust
} else if self.head < old_cap - self.tail {
    // B
    self.copy_nonoverlapping(old_cap, 0, self.head);
    self.head += old_cap;
    debug_assert!(self.head > self.tail);
}
```

That is only safe if the buffer really did grow, to at least twice its
old size. `reserve` decides whether it did. In Rust 1.20.0:

```rust
pub fn reserve(&mut self, additional: usize) {
    let old_cap = self.cap();
    let used_cap = self.len() + 1;
    let new_cap = used_cap.checked_add(additional)
        .and_then(|needed_cap| needed_cap.checked_next_power_of_two())
        .expect("capacity overflow");

    if new_cap > self.capacity() {
        self.buf.reserve_exact(used_cap, new_cap - used_cap);
        unsafe {
            self.handle_cap_increase(old_cap);
        }
    }
}
```

`self.capacity()` is not the buffer's size: it is `self.cap() - 1`, the
number of elements the user can store, since a ring buffer keeps one slot
free. So when `new_cap` equals `old_cap`, the test `new_cap >
self.capacity()` is still true, nothing is allocated, and
`handle_cap_increase` runs on a buffer that did not grow. In the
four-line example the buffer has 64 slots, `reserve(31)` asks for 64, and
case B moves `head` to 64, one past the end, where the next `push_back`
writes. The [fix][pr], "Fix capacity comparison in reserve", changed one
line:

```rust
if new_cap > old_cap {
```

The PR's description: "You can otherwise end up in a situation where you
don't actually resize but still call into handle_cap_increase which then
corrupts head/tail."

## The same code in Pia

Here is `handle_cap_increase` in Pia. The ring's ends are a record, and
`buf` is the buffer after the allocator has run, so `len buf` is the new
capacity. The precondition says only what the Rust code's types say: the
old capacity fits in the buffer, and both ends are inside it.

<!-- example: grow.pia -->
<!-- expect: fail -->
```ocaml
let ring = type { head : usize; tail : usize }

let handle_cap_increase (buf : inout mutable [u32]) (old_cap : usize) (r : ring) : ring
  requires 0 < old_cap && old_cap <= len buf
  requires r.tail < old_cap && r.head < old_cap
  ensures result.head < len buf && result.tail < len buf
=
  if r.tail <= r.head then r
  else if r.head < old_cap - r.tail then (
    for i in 0..r.head do buf.[old_cap + i] <- buf.[i] done;
    { head = r.head + old_cap; tail = r.tail })
  else (
    let new_tail : usize = len buf - (old_cap - r.tail) in
    for j in 0..old_cap - r.tail do buf.[new_tail + j] <- buf.[r.tail + j] done;
    { head = r.head; tail = new_tail })
```

The postcondition is Rust's own `debug_assert!(self.head < self.cap())`,
which debug builds checked at run time. `piac` checks it, and the copy,
for every input:

```console
$ piac --verify grow.pia
...
grow.pia:10:40: failed: '+' does not overflow usize
  counterexample: len buf = 18221564092244557822, old_cap = 17996384110746009596, r.head = 1441151880758558720, r.tail = 14627691589472878591, result = 19437535991504568314
grow.pia:10:48: proved: the index is within bounds [smt]
grow.pia:10:27: failed: the index is within bounds
  counterexample: len buf = 16233511021939330180, old_cap = 15098680658861804673, r.head = 3530892493789154496, r.tail = 4541436590208057858, index = 17879290520661494913, length = 16233511021939330180
grow.pia:11:21: failed: '+' does not overflow usize
  counterexample: len buf = 18446726485818605566, old_cap = 18446726481523507198, r.head = 4611650834055299072, r.tail = 4611668426241343489, result = 23058377315578806270
...
grow.pia:6:3: failed: the postcondition holds
  counterexample: len buf = 12677269138058477485, old_cap = 11124079053479378995, r.head = 1757134085014192249, r.tail = 9315894506577822301
9 proved, 4 failed, 0 skipped
```

The index failure and the postcondition failure are both buffers that
did not grow enough: `len buf` only a little above `old_cap`, so case B
moves `head` past the end and the copy writes there. (The two overflow
failures are the same mistake on enormous buffers, where `r.head +
old_cap` does not even fit in a `usize`.) In Rust that assumption lived in the word `unsafe`. In Pia it
has to be written down, or the function does not compile.

## The assumption, stated

So say what `handle_cap_increase` needs: the buffer at least doubled.
Then it proves, and the obligation moves to its caller, `reserve`. Here
is `reserve` with Rust 1.20's comparison. The allocator either leaves
the buffer alone or grows it to a power of two at least twice as big,
which the second precondition says:

<!-- example: reserve.pia -->
<!-- expect: fail -->
```ocaml
let ring = type { head : usize; tail : usize }

let handle_cap_increase (buf : inout mutable [u32]) (old_cap : usize) (r : ring) : ring
  requires 0 < old_cap && old_cap + old_cap <= len buf
  requires r.tail < old_cap && r.head < old_cap
  ensures result.head < len buf && result.tail < len buf
=
  if r.tail <= r.head then r
  else if r.head < old_cap - r.tail then (
    for i in 0..r.head do buf.[old_cap + i] <- buf.[i] done;
    { head = r.head + old_cap; tail = r.tail })
  else (
    let new_tail : usize = len buf - (old_cap - r.tail) in
    for j in 0..old_cap - r.tail do buf.[new_tail + j] <- buf.[r.tail + j] done;
    { head = r.head; tail = new_tail })

let reserve (buf : inout mutable [u32]) (old_cap : usize) (r : ring) : ring
  requires 0 < old_cap && r.tail < old_cap && r.head < old_cap
  requires len buf = old_cap || old_cap + old_cap <= len buf
=
  let capacity : usize = old_cap - 1 in
  if len buf > capacity then handle_cap_increase buf old_cap r else r
```

```console
$ piac --verify reserve.pia
...
reserve.pia:22:30: failed: the precondition of 'handle_cap_increase' holds
  counterexample: len buf = 16583426343899006287, old_cap = 16583426343899006287, r.head = 433509266868928512, r.tail = 0
reserve.pia:22:30: proved: the precondition of 'handle_cap_increase' holds [smt]
15 proved, 1 failed, 0 skipped
```

The verifier finds the bug report's case: the buffer did not grow, the
comparison against `capacity` still passed, and the unsafe move would
have run. A call reports one goal per precondition of the callee, in
order, so the failure is the first one, the doubling; the second holds.

## The fix, proved

The rest of this page is the fixed program. `handle_cap_increase` states
the growth it needs:

```pia
let ring = type { head : usize; tail : usize }

let handle_cap_increase (buf : inout mutable [u32]) (old_cap : usize) (r : ring) : ring
  requires 0 < old_cap && old_cap + old_cap <= len buf
  requires r.tail < old_cap && r.head < old_cap
  ensures result.head < len buf && result.tail < len buf
=
  if r.tail <= r.head then r
  else if r.head < old_cap - r.tail then (
    for i in 0..r.head do buf.[old_cap + i] <- buf.[i] done;
    { head = r.head + old_cap; tail = r.tail })
  else (
    let new_tail : usize = len buf - (old_cap - r.tail) in
    for j in 0..old_cap - r.tail do buf.[new_tail + j] <- buf.[r.tail + j] done;
    { head = r.head; tail = new_tail })
```

and `reserve` compares against the old capacity, as Rust's fix does:

```pia
let reserve (buf : inout mutable [u32]) (old_cap : usize) (r : ring) : ring
  requires 0 < old_cap && r.tail < old_cap && r.head < old_cap
  requires len buf = old_cap || old_cap + old_cap <= len buf
  ensures result.head < len buf && result.tail < len buf
=
  if len buf > old_cap then handle_cap_increase buf old_cap r else r
```

Every goal on this page is proved:

```console
$ piac --verify rust-vecdeque.pia.md
...
rust-vecdeque.pia.md:199:3: proved: the postcondition holds [smt]
...
rust-vecdeque.pia.md:217:3: proved: the postcondition holds [smt]
16 proved, 0 failed, 0 skipped
```

Two numbers named "capacity", one of them off by one from the other, is
an ordinary way to write a bug. What made it a memory-safety bug was that
the function trusting the number was `unsafe`, so nothing checked what it
trusted. In Pia, what a function trusts is its precondition, and every
caller proves it.

## Sources

- [rust-lang/rust#44800][issue], "seg fault pushing on either side of a
  VecDeque", 24 September 2017: the report, the four-line reduction and
  the Valgrind output.
- [rust-lang/rust#44802][pr], "Fix capacity comparison in reserve", by
  Steven Fackler, merged 27 September 2017.
- The code before the fix: [`src/liballoc/vec_deque.rs` at
  1.20.0][before].
- [GitHub Advisory GHSA-7877-m5c6-fgmx][ghsa] for CVE-2018-1000657, which
  gives the affected range as "stable release 1.3.0 and later" and the fix
  as "stable release 1.22.0 and later".

[issue]: https://github.com/rust-lang/rust/issues/44800
[pr]: https://github.com/rust-lang/rust/pull/44802
[before]: https://github.com/rust-lang/rust/blob/1.20.0/src/liballoc/vec_deque.rs#L552
[ghsa]: https://github.com/advisories/GHSA-7877-m5c6-fgmx
