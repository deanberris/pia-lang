/-
The Lean proofs of variants.pia's lemmas (ADR 0061, step 3). `cases` takes
a value of a variant apart by its constructor; the payload's range is then
the hypothesis `match` reduces to.
-/
import Statements

namespace Variants

-- Core Lean has no `mul_self_nonneg`, so the two signs are taken apart.
theorem square_nonneg (r : Int) : 0 ≤ r * r := by
  rcases Int.le_total 0 r with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

theorem area_nonneg : variants.area_nonneg := by
  intro s
  cases s with
  | Circle r =>
    show 3 * r * r ≥ 0
    rw [Int.mul_assoc]
    have h := square_nonneg r
    omega
  | Square w => exact square_nonneg w
  | Empty => decide

theorem level_fits : variants.level_fits := by
  intro r h
  constructor
  · cases r with
    | Missing => decide
    | Level v =>
      have hv : 0 ≤ v ∧ v ≤ 255 := h
      show v ≤ 255
      omega
  · rfl

end Variants
