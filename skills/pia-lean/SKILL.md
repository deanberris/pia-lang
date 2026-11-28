---
name: pia-lean
description: Prove a Pia lemma in Lean 4 when Z3 cannot - `= by lean T`, `piac --emit=lean`, writing the Lean proof against the generated statements, the pia_lean_proof Bazel rule and `--lean-receipt`, and what a stale receipt means. Use when a lemma needs induction, nonlinear arithmetic or a theorem Z3 gives up on, or when a by-lean goal fails with "no receipt" or "stale receipt".
---

# Lemmas proved in Lean

Z3 proves most Pia goals. Some facts it cannot prove, such as an induction over a recursive spec function, a nonlinear identity or a theorem from mathematics. Such a fact can be stated as a Pia lemma and proved in Lean 4 instead (ADR 0061). Only the statement is shared: `piac` writes it, and the specification it uses, as Lean, and Lean checks a proof of it. Code is never translated, so Lean never gives a second meaning to what a program does.

Lean never runs inside `piac`, the REPL or the language server. A Bazel target runs it once and writes a *receipt*, which `piac --verify` reads. A receipt names the statement by a hash, so when the lemma or anything it uses changes, the receipt is stale and the goal fails until the proof is checked again.

## 1. State the lemma

Write the lemma as usual, with `requires` and `ensures` only, and `= by lean T` for its body, where `T` is the Lean theorem that will prove it:

<!-- untested: proved only with its Lean receipt, from a pia_lean_proof target (tests/lean) -->
```ocaml
let rec spec sum (n : int) : int
  requires n >= 0
  decreases n
= if n = 0 then 0 else n + sum (n - 1)

let lemma sum_nonneg (n : int) : unit
  requires n >= 0
  ensures sum n >= 0
= by lean Proofs.sum_nonneg

(* Callers use it like any lemma, and Z3 proves this from it. *)
let lemma sum_plus_one (m : int) : unit
  requires m >= 0
  ensures sum m + 1 > 0
= sum_nonneg m
```

What the translation supports: `int` and `bool`, machine integers (`u8` ... `u64`, `usize`, `i8` ... `i64`, `isize`) and range types (`int{0..9}`), slices and fixed arrays of them (`[u8]`, `[u8; 16]`, with `len` and `xs.[i]`), records of `int` and `bool`, `+ - *`, comparisons, `&& || ==> <==>`, `if`, `let ... in`, record literals, fields and updates, calls of spec functions in the same file, recursion with a `decreases` measure, and `forall`/`exists` in a lemma's contracts. A machine integer is a Lean `Int`, never a `BitVec`, because Pia's integers never wrap; its range is a hypothesis, `((0 : Int) ≤ a ∧ a ≤ (255 : Int))`, first among the lemma's, in a spec function's `h_req` guard, and after a bound variable (`∃ x, range ∧ p`). A suffix such as `9u8` names only the type, and `int x` is `x`. A slice is a `Slice' t` with fields `len` and `get`, so `xs.[i]` is `xs.get i`; the lemma has the length's range and `∀ i', 0 ≤ i' ∧ i' < xs.len → range (xs.get i')` as hypotheses, and a spec function's guard tests only the length. A fixed array is a `Slice'` too, with `xs.len = 16` as its hypothesis. Anything else, such as `/`, a record field of type `u8`, a slice of slices, a quantifier in a spec function's body or a `decreases` on the lemma, is an error from `--emit=lean` that says it has no translation yet. Only what a `by lean` lemma uses is translated.

## 2. Read the statements

```sh
piac --emit=lean sums.pia -o Statements.lean
```

The file is in the namespace of the module, or of the file name (`sums` here). Each lemma becomes a `Prop`, each spec function a `def` and each record a `structure`:

```lean
opaque sum'outside : Int → Int

def sum (n : Int) : Int :=
  if h_req : (n ≥ (0 : Int)) then
    (if h_1 : (n = (0 : Int)) then (0 : Int) else (n + (sum (n - (1 : Int)))))
  else sum'outside n
termination_by (n).toNat
decreasing_by all_goals first | omega | (simp_wf; omega)

@[reducible] def sum_nonneg : Prop :=
  ∀ (n : Int),
    (n ≥ (0 : Int)) → ((sum n) ≥ (0 : Int))
```

- Lean functions are total, so outside its `requires` a spec function is an opaque constant, `sum'outside n`. Pia says nothing about it there, and so Lean can prove nothing about it either: give the lemma the `requires` its spec calls need. In a proof, the branch outside the precondition is closed by its contradictory hypothesis, as `omega` does below.
- A `bool` spec function is a `Bool`: in a statement, `f x` reads `f x = true`, and `&&` inside a body is Lean's `&&` over `decide`.
- `let` values are put in place of their names, so `omega` sees them when it proves that a recursion ends.
- Every literal is an `Int`, `(0 : Int)`, since a term of literals alone would otherwise be a `Nat`, where `0 - 1 = 0`.

## 3. Write the proof

The proof file imports `Statements` and proves each theorem against its statement. No Mathlib yet: core Lean, `omega`, `simp`, `decide`, `split` and induction.

```lean
import Statements

namespace Proofs

theorem sum_nat (k : Nat) : sums.sum (k : Int) ≥ 0 := by
  induction k with
  | zero =>
    rw [sums.sum]
    split <;> (try split) <;> omega
  | succ k ih =>
    have h : sums.sum (((k + 1 : Nat) : Int) - 1) = sums.sum (k : Int) := by
      congr 1
      omega
    rw [sums.sum]
    split <;> (try split) <;> omega

theorem sum_nonneg : sums.sum_nonneg := by
  intro n hn
  have h := sum_nat n.toNat
  rwa [Int.toNat_of_nonneg hn] at h

end Proofs
```

`tests/lean/Proofs.lean` is a complete, checked example, with a record and a `bool` spec function too.

Machine integers need no more than `omega` when the goal is linear, since each range is a hypothesis. A spec function over them unfolds to its guard, which `split` and `omega` close, and a product is bounded by `Int.mul_le_mul` first (`tests/lean/Bytes.lean`):

```lean
theorem total_fits : bytes.total_fits := by
  intro a b h
  unfold bytes.total
  split <;> omega

theorem square_fits : bytes.square_fits := by
  intro a ⟨h0, h1⟩
  have h : a * a ≤ 255 * 255 := Int.mul_le_mul h1 h1 h0 (by omega)
  omega
```

A fact about a recursion over a slice's prefix, which Z3 unfolds only as far as its fuel, is induction on the length as a `Nat`. Give `omega` the element at the new index, through the hypothesis on every element, and the same `xs.get` term as the unfolded body writes it (`tests/lean/Slices.lean`).

## 4. Check it and pass the receipt

```python
load("//tools/lean:lean.bzl", "pia_lean_proof")

pia_lean_proof(
    name = "sums_proof",
    src = "sums.pia",
    proofs = "Proofs.lean",
)
```

```sh
bazel build //tests/lean:sums_proof
piac --verify --lean-receipt=bazel-bin/tests/lean/sums_proof.receipt sums.pia
```

The target writes Statements.lean with `piac --emit=lean`, compiles it and the proofs with the pinned Lean release, checks `example : sums.sum_nonneg := Proofs.sum_nonneg`, and prints the axioms each theorem uses. A receipt holds the lemma, the statement hash, the theorem, the Lean version and the axioms. `--lean-receipt` may be given more than once.

## Reading the goal

Each `by lean` lemma is one goal, `the Lean theorem 'T' proves 'l'`:

| Report | Means | Fix |
| --- | --- | --- |
| `proved ... [lean]` | a receipt proves the statement as it is now | nothing |
| `failed ... [no receipt]` | no `--lean-receipt` names the lemma | build its `pia_lean_proof` target and pass the receipt |
| `failed ... [stale receipt]` | the lemma, or a spec function or record it uses, changed since the proof was checked | build the target again; fix the proof if Lean now rejects it |
| `failed ... [receipt for another theorem]` | the receipt proves the lemma with another theorem than `by lean` names | rename one of them |
| `failed ... [axiom X]` | the proof depends on an axiom other than Lean's own, `sorryAx` included | prove it without the axiom |
| `failed ... [native_decide]` | the proof uses `native_decide` in a file not marked `@trusted` | prove it with `decide`, or mark the file `@trusted` |

A proof may use Lean's axioms (`propext`, `Classical.choice`, `Quot.sound`). `native_decide`, which trusts Lean's compiler (its axioms are `Lean.ofReduceBool`, or, from Lean 4.36, `T._native.native_decide.ax_1_1` per use), is allowed only in a file marked `@trusted`, and is then a trusted item. Anything else fails, both in the receipt writer and in `piac`.

## What the build records

A proved `by lean` lemma is not trusted, but it rests on Lean's kernel and on piac's translation of its statement, so `--trust-report` lists it in a section of its own, and `--why` names the goals that use it:

```sh
piac --verify --trust-report --why --lean-receipt=bazel-bin/tests/lean/sums_proof.receipt sums.pia
```

Each object's certificate lists it too, as `proved lean <lemma> <statement hash> <theorem> <toolchain> <axioms>`, which `pia-cert dump` prints. Importers need no `trusting` for it. tests/lean/native_trusted.pia and native_untrusted.pia show `native_decide` with and without `@trusted`.

Callers assume a `by lean` lemma's `ensures` whether or not its goal is proved, as for any lemma: the build still fails until it is. In the REPL and the language server there are no receipts, so these goals show as failed there.

## Pitfalls

- **Keep the statement small.** Every spec function the lemma uses is part of its hash, so a change to any of them makes the receipt stale. A lemma about one function stays valid while others change.
- **Name clashes.** A spec function named like a Lean root declaration (`max`, `id`) can be ambiguous in the generated file; qualify it in the proof, as `sums.max`.
- **The measure must be linear** for `omega` to prove that a translated recursion ends, as the verifier proved it does. A recursion that only Z3's nonlinear reasoning bounds fails in Lean's `decreasing_by`.
