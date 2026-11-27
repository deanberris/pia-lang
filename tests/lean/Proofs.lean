/-
The Lean proofs of the lemmas of sums.pia (ADR 0061). `Statements` is what
`piac --emit=lean sums.pia` writes: the lemmas' statements, in the
namespace `sums`, and the spec functions and records they use. Each
theorem proves one statement, and the sums_proof target checks that it
does and writes the receipts.
-/
import Statements

namespace Proofs

/-- `sum k` for a natural `k`, by induction; `sum` is a total Lean function
that agrees with the Pia one where its precondition holds. -/
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

theorem dist_of : sums.dist_of := by
  intro a b
  rfl

theorem origin_within : sums.origin_within := by
  intro n hn
  simp [sums.within] <;> omega

end Proofs
