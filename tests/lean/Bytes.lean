/-
The Lean proofs of the lemmas of bytes.pia (ADR 0061, step 3). A machine
integer is an `Int` whose range is a hypothesis, so `omega` proves the
linear lemmas from the ranges alone.
-/
import Statements

namespace Bytes

theorem total_fits : bytes.total_fits := by
  intro a b h
  unfold bytes.total
  split <;> omega

-- `omega` is linear; the product is bounded by monotonicity.
theorem square_fits : bytes.square_fits := by
  intro a ⟨h0, h1⟩
  have h : a * a ≤ 255 * 255 := Int.mul_le_mul h1 h1 h0 (by omega)
  omega

theorem signed_gap : bytes.signed_gap := by
  intro a b h
  omega

theorem digit_byte : bytes.digit_byte := by
  intro d ⟨h0, h9⟩
  exact ⟨d, ⟨by omega, by omega⟩, rfl, by omega⟩

end Bytes
