/-
The Lean proofs of slices.pia's lemmas (ADR 0061, step 3): `total xs n`,
the sum of the first `n` bytes of `xs`, is at most `255 * n`, and `count`,
over a fixed array, is at most `n`. Z3 unfolds a
recursive spec function only as far as its fuel, so it needs induction,
which is on `n` as a natural number, as in Proofs.lean.
-/
import Statements

namespace Slices

theorem total_nat (xs : slices.Slice' Int)
    (hel : ∀ (i' : Int), 0 ≤ i' ∧ i' < xs.len → 0 ≤ xs.get i' ∧ xs.get i' ≤ 255) :
    ∀ (k : Nat), (k : Int) ≤ xs.len → xs.len ≤ 18446744073709551615 →
      slices.total xs k ≤ 255 * k := by
  intro k
  induction k with
  | zero =>
    intro _ _
    rw [slices.total]
    split <;> (try split) <;> omega
  | succ k ih =>
    intro hk hmax
    have hprev := ih (by omega) hmax
    have he := hel k ⟨by omega, by omega⟩
    have h : slices.total xs (((k + 1 : Nat) : Int) - 1) = slices.total xs (k : Int) := by
      congr 1
      omega
    have g : xs.get (((k + 1 : Nat) : Int) - 1) = xs.get (k : Int) := by
      congr 1
      omega
    rw [slices.total]
    split <;> (try split) <;> omega

theorem total_le : slices.total_le := by
  intro xs n ⟨hlen, hel, hn, hnl⟩
  have h := total_nat xs hel n.toNat (by omega) hlen.2
  rwa [Int.toNat_of_nonneg hn.1] at h

theorem count_nat (xs : slices.Slice' Int) (v : Int) (hl : xs.len = 16)
    (hv : 0 ≤ v ∧ v ≤ 255) :
    ∀ (k : Nat), (k : Int) ≤ 16 → slices.count xs v k ≤ k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [slices.count]
    split <;> (try split) <;> omega
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have h : slices.count xs v (((k + 1 : Nat) : Int) - 1) = slices.count xs v (k : Int) := by
      congr 1
      omega
    rw [slices.count]
    split <;> (try split) <;> (try split) <;> omega

theorem count_le : slices.count_le := by
  intro xs v n ⟨hl, _, hv, hn, hn16⟩
  have h := count_nat xs v hl hv n.toNat (by omega)
  rwa [Int.toNat_of_nonneg hn.1] at h

end Slices
