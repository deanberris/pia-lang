---
name: pia-contracts
description: Write Pia contracts that prove - requires, ensures, old, quantifiers, loop invariants, decreases measures, spec functions and lemmas - and turn each kind of failed goal into the right fix. Use when writing or repairing Pia code whose goals fail or are skipped.
---

# Writing contracts and loop invariants

The verifier proves each function on its own, from its own contracts and the *contracts* of what it calls. So a contract is an interface: `requires` is what every caller must prove and the body may assume, and `ensures` is what the body must prove and every caller may assume. The reference is the Contracts section of [docs/tour.md](../../docs/tour.md#contracts) and [docs/verifier.md](../../docs/verifier.md).

| Clause | Meaning |
| --- | --- |
| `requires p` | precondition |
| `ensures p` | postcondition; `result` is the returned value |
| `old e` | in an `ensures`, `e` as it was on entry |
| `forall (i in lo..hi). p`, `exists (i in lo..hi). p` | bounded quantifiers |
| `assert p`, `assume p` | proved here; assumed here without proof (avoid `assume`) |
| `invariant p` | on a loop: holds on entry and after every iteration |
| `decreases m` | on a `while` loop or a recursive function: never negative, and goes down |

Arithmetic *inside* a contract is exact mathematics, so `ensures result = a + b` cannot overflow. Arithmetic in code is checked.

## Start bare, let the goals tell you

Write the body with no contracts, run it (`piac --verify`, or a REPL cell), and fix one failed goal at a time. For each failure, choose:

| The failure says | If | Then |
| --- | --- | --- |
| `'+' does not overflow T` | callers never pass such values | `requires` that bounds the inputs |
| | it can happen | change the body: a wider result type, saturating `+|`, a guard, or compare by subtraction (`n - pos < 2` rather than `pos + 2 > n`) |
| `the index is within bounds` | the length is the caller's business | `requires len xs >= ...` |
| | | otherwise guard the access with an `if` |
| `the precondition of 'f' holds` | | prove it at the call: a guard, a `requires` on this function, or an `ensures` on whatever produced the argument |
| `the postcondition holds` | the claim is wrong | weaken the `ensures` |
| | the claim is right but not derivable | the body lost information: add a loop invariant, or an `ensures` on a callee |
| `the loop terminates` / `the recursion terminates` (skipped) | | add `decreases` |

A `requires` that only restates the failure (`requires x < 255` for `x + 1`) is right when the caller really owns that fact. If no caller can meet it, it has only moved the bug. Check callers by proving them too.

## Loop invariants

The verifier never unrolls a loop. It checks the invariant on entry, then walks **one arbitrary iteration** in which the loop variable and every value the loop changes are fresh, and only the invariant is known about them. After the loop, again only the invariant (and, for a `for`, that the loop variable reached its bound) is known.

So an invariant has to say everything the body and the code after the loop need about the changing values. Without one, an accumulator is unknown and its update can overflow:

<!-- example: total_bare.pia -->
<!-- expect: fail -->
```ocaml
let total (xs : [u8]) : u32
  requires len xs <= 1000
= let s : mutable u32 = 0 in
  for i in 0 .. len xs do s <- s + xs.[i] done;
  s
```

```console
$ piac --verify total_bare.pia
total_bare.pia:4:36: proved: the index is within bounds [smt]
total_bare.pia:4:34: failed: '+' does not overflow u32
  counterexample: len xs = 1, result = 4294967550
1 proved, 1 failed, 0 skipped
```

Bound the accumulator by the loop variable. The same fact then gives the postcondition after the loop:

<!-- example: total.pia -->
```ocaml
let total (xs : [u8]) : u32
  requires len xs <= 1000
  ensures result <= 255000
= let s : mutable u32 = 0 in
  for i in 0 .. len xs
    invariant s <= 255 * i
  do s <- s + xs.[i] done;
  s
```

```console
$ piac --verify total.pia
total.pia:6:5: proved: the loop invariant holds on entry [smt]
total.pia:7:15: proved: the index is within bounds [smt]
total.pia:7:13: proved: '+' does not overflow u32 [smt]
total.pia:6:5: proved: the loop invariant holds after each iteration [smt]
total.pia:3:3: proved: the postcondition holds [smt]
5 proved, 0 failed, 0 skipped
```

Patterns that come up again and again:

- **Accumulators:** `s <= max_step * i`, or `s = spec_sum xs i` with a spec function (below) when callers need the exact value.
- **Index ranges in `while` loops:** `i <= len xs`, so that `xs.[i]` behind `i < len xs` is in bounds and the code after the loop knows `i <= len xs`.
- **What has been written:** `forall (k in 0..i). dst.[k] = src.[k]`, so that the `ensures` can say the whole buffer was copied.
- **What has not changed:** a value the loop does not write needs no invariant, but a buffer the loop writes is fresh after the loop: state what stays the same about it.

## Termination

A `for` loop always ends. A `while` loop needs `decreases`:

<!-- example: find.pia -->
```ocaml
let find (xs : [i32]) (x : i32) : usize
  ensures result <= len xs
= let i : mutable usize = 0 in
  while i < len xs && xs.[i] <> x
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  i
```

The measure is checked at the end of each iteration: never negative, and smaller than before. A recursive function takes `decreases` on its header, checked at each recursive call.

## `old`, quantifiers and spec functions

`old e` names a value on entry, for functions that change a buffer:

<!-- example: swap.pia -->
```ocaml
let swap (xs : borrowed inout mutable [u8; 2]) : unit
  ensures xs.[0] = old (xs.[1]) && xs.[1] = old (xs.[0])
= let t = xs.[0] in xs.[0] <- xs.[1]; xs.[1] <- t
```

A **spec function** (`let spec`) is pure, total and erased by codegen. It is the way to name a property in contracts: to the solver it is a function with its `ensures` and one unfolding of its body. A **lemma** (`let lemma`, returns `unit`) is proved once, and a call to it adds its `ensures` as a fact; a recursive lemma with `decreases` is a proof by induction. `@fuel(n)` on a spec function's return type unfolds it `n` levels. See [docs/verifier.md](../../docs/verifier.md#spec-functions-and-lemmas).

## Pitfalls

- **Calls to ordinary functions or constants inside contracts are unknown values.** `requires a < limit`, where `limit` is a `let` constant, does not give the solver `limit`'s value. Write the literal, or use a spec function.
- **A call in a callee's `ensures` is unconstrained at the caller.** If callers need what it means, express it with a spec function.
- **No shadowing.** A `let` inside a body cannot reuse any name in scope, including a parameter's.
- **Narrow operands shift at their own width.** `buf.[i] << 8` on a `u8` fails `the shift amount is less than 8`. C promotes before shifting, Pia does not. Widening is implicit, so bind the operand to a wider `let` first (`let hi : usize = buf.[i] in hi << 8`), or write the shift first under a wide annotation, as in `let size : usize = (buf.[i + 1] << 8) | buf.[i]`.
- **Wrap and saturate only on purpose.** `+|` saturates; overflow behaviour is otherwise a goal, not a silent wrap.
- **`assume` is a hole in the proof.** Prefer `requires`, which moves the obligation to callers, where it is proved.
