# Binary search

Binary search is the first algorithm many programmers learn to prove
correct. In June 2006 Joshua Bloch, who wrote `java.util.Arrays`, published
["Nearly All Binary Searches and Mergesorts are Broken"][bloch]: the binary
search he wrote for the JDK had a bug, and so did the one in Jon Bentley's
*Programming Pearls*. It had sat in the
JDK, in his words, "lying in wait for nine years or so" before it broke
someone's program.

The bug is one line, and it is not in the logic of the search. It is in
the arithmetic.

This page is a literate Pia file,
[`docs/cases/binary-search.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/cases/binary-search.pia.md).
The `pia` blocks are the fixed search, which the test suite proves, and the
other code blocks are the broken versions, each checked to fail exactly as
shown.

## The bug

Here is the JDK's search as Bloch's post shows it, lightly reformatted:

```java
public static int binarySearch(int[] a, int key) {
    int low = 0;
    int high = a.length - 1;

    while (low <= high) {
        int mid = (low + high) / 2;
        int midVal = a[mid];

        if (midVal < key)
            low = mid + 1;
        else if (midVal > key)
            high = mid - 1;
        else
            return mid; // key found
    }
    return -(low + 1);  // key not found.
}
```

`int mid = (low + high) / 2;` "fails if the sum of `low` and `high` is
greater than the maximum positive `int` value (2^31 - 1)." The sum wraps
around to a negative number, `mid` is negative, and `a[mid]` throws
`ArrayIndexOutOfBoundsException`. In C, where signed overflow is undefined
behaviour, anything can happen. It takes an array of 2^30 elements or more,
"roughly a billion", which few test suites ever build.

## The same code in Pia

Pia has no early `return`, so the loop records what it found and stops by
closing the range. Otherwise this is the JDK's code, with `i32` for Java's
`int`. A Java array has at most 2^31 - 1 elements, which the precondition
says:

<!-- example: search.pia -->
<!-- expect: fail -->
```ocaml
let search (xs : [i32]) (key : i32) : i32
  requires len xs <= 2147483647
=
  let n : i32 = len xs in
  let low : mutable i32 = 0 in
  let high : mutable i32 = n - 1 in
  let found : mutable i32 = -1 in
  while low <= high
    invariant 0 <= low && low <= n && -1 <= high && high < n
    decreases high - low + 1
  do
    let mid : i32 = (low + high) / 2 in
    let v = xs.[mid] in
    if v < key then low <- mid + 1
    else if v > key then high <- mid - 1
    else (found <- mid; low <- high + 1)
  done;
  if found >= 0 then found else -(low + 1)
```

`piac` will not compile it:

```console
$ piac --verify search.pia
...
search.pia:12:26: failed: '+' does not overflow i32
  counterexample: len xs = 2147483647, key = 0, result = 2147483648
...
search.pia:18:39: failed: '+' does not overflow i32
  counterexample: len xs = 2147483647, key = 2131628096, result = 2147483648
...
13 proved, 2 failed, 0 skipped
```

The first failure is Bloch's bug: on the largest array, `low + high`
reaches 2^31, one more than an `i32` holds.

The second is one the post does not mention. When the key is larger than
every element, the search ends with `low = len xs`, and the "not found"
result `-(low + 1)` overflows too, on an array of exactly 2^31 - 1
elements. In Java the result wraps to `Integer.MIN_VALUE`, which is still
negative but encodes the wrong insertion point. Whether a JVM will
allocate an array that large at all varies, which is how a bug like this
stays hidden. The verifier does not need to know; it only needs the
contract to allow it.

## Unsigned is no escape

The usual C fix is to use `size_t`, an unsigned type as wide as a pointer.
That moves the edge, but the edge is still there:

<!-- example: search_usize.pia -->
<!-- expect: fail -->
```ocaml
let search (xs : [i32]) (key : i32) : usize =
  let low : mutable usize = 0 in
  let high : mutable usize = len xs in
  let found : mutable usize = len xs in
  while low < high
    invariant low <= high && high <= len xs
    decreases high - low
  do
    let mid : usize = (low + high) / 2 in
    let v = xs.[mid] in
    if v < key then low <- mid + 1
    else if v > key then high <- mid
    else (found <- mid; low <- high)
  done;
  found
```

```console
$ piac --verify search_usize.pia
...
search_usize.pia:9:28: failed: '+' does not overflow usize
  counterexample: len xs = 18446744073709420544, key = 0, result = 18455470898401229053
...
7 proved, 1 failed, 0 skipped
```

No real machine has a buffer of 2^64 elements, but the type allows one, and
Pia proves what the types and contracts say, not what seems likely. A
precondition such as `requires len xs <= 9223372036854775807` would prove
it; so does computing the midpoint without the sum.

## The fix, proved

Bloch's fix is `int mid = low + ((high - low) / 2);`. Since `low <= high`,
`high - low` cannot overflow, and adding half of it to `low` stays at or
below `high`. The "not found" result becomes `-low - 1`, which cannot
overflow because `low` is never negative.

With the arithmetic fixed, the search can also be held to its full
specification. The precondition says the slice is sorted. The
postconditions say what the result means: a non-negative result is an
index holding the key, and a negative one means the key is nowhere in the
slice. The two invariants that make the second one true say that
everything left of `low` is smaller than the key and everything right of
`high` is larger.

```pia
let search (xs : [i32]) (key : i32) : i32
  requires len xs <= 2147483647
  requires forall (i in 0..len xs). forall (j in i..len xs). xs.[i] <= xs.[j]
  ensures result >= 0 ==> result < len xs && xs.[result] = key
  ensures result < 0 ==> forall (k in 0..len xs). xs.[k] <> key
=
  let n : i32 = len xs in
  let low : mutable i32 = 0 in
  let high : mutable i32 = n - 1 in
  let found : mutable i32 = -1 in
  while low <= high
    invariant 0 <= low && low <= n && -1 <= high && high < n
    invariant found = -1 || (0 <= found && found < n && xs.[found] = key)
    invariant found = -1 ==> forall (k in 0..low). xs.[k] < key
    invariant found = -1 ==> forall (k in high + 1..n). xs.[k] > key
    decreases high - low + 1
  do
    let mid : i32 = low + (high - low) / 2 in
    let v = xs.[mid] in
    if v < key then low <- mid + 1
    else if v > key then high <- mid - 1
    else (found <- mid; low <- high + 1)
  done;
  if found >= 0 then found else -low - 1
```

Every goal on this page is proved, including that the loop ends:

```console
$ piac --verify binary-search.pia.md
...
binary-search.pia.md:177:5: proved: the measure decreases [smt]
...
binary-search.pia.md:165:3: proved: the postcondition holds [smt]
binary-search.pia.md:166:3: proved: the postcondition holds [smt]
24 proved, 0 failed, 0 skipped
```

In a 2008 update, Bloch corrected his own C fix, which was not guaranteed
to work under C99's rules for signed overflow, and wrote: "Now that we've
made this change, we know that the program is correct;)". With Pia, the
compiler is the one who knows.

## Sources

- Joshua Bloch, ["Extra, Extra - Read All About It: Nearly All Binary
  Searches and Mergesorts are Broken"][bloch], Google Research blog, 2 June
  2006. The JDK code, the buggy line, the 2^30-element threshold and the
  fixes are quoted from it.
- Jon Bentley, *Programming Pearls*, chapter 5 (Addison-Wesley, 1986;
  second edition 2000), which the post names as the source of the same
  bug.

[bloch]: https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/
