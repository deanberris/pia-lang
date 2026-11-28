-- The Lean proofs of Pia.Float.Exp (ADR 0061): the model of its theory
-- RealExp, Mathlib's Real.exp with pw n = 2^-n, which meets every axiom,
-- and scaled_lin. pia_lean_proof checks them against `piac --emit=lean`
-- of Exp.pia and writes the receipts its pia_library is proved with.

import Statements
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ExpProofs

open Pia.Float.Exp

private theorem near_iff (a b c : ℝ) : near a b c = true ↔ |a - b| ≤ c := by
  simp [near, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem bit_f_pos (k b : ℤ) (c : ℝ) (h : 0 < c) : 0 < bit_f k b c := by
  unfold bit_f; split <;> linarith

theorem scaled_lin : Pia.Float.Exp.scaled_lin := by
  intro v n _
  refine ⟨by simp only [scaled]; ring, ?_⟩
  unfold scaled
  repeat' apply mul_pos
  all_goals first | (apply bit_f_pos; norm_num) | norm_num

private theorem scaled_pow (n : ℤ) (h0 : 0 ≤ n) (h1 : n ≤ 150) :
    scaled 1 n = ((1:ℝ)/2) ^ n.toNat := by
  interval_cases n <;> norm_num [scaled, bit_f, bit_r]

-- |log 2 - L| for the decimal L the theory uses.
private theorem log_two_near :
    |Real.log 2 - 6931471805599453/10000000000000000| ≤ 11/100000000000 := by
  have h := Real.log_two_near_10
  have e : |(287209 / 414355 : ℝ) - 6931471805599453/10000000000000000| ≤ 1/100000000000 := by
    rw [abs_le]; constructor <;> norm_num
  calc |Real.log 2 - 6931471805599453/10000000000000000|
      = |(Real.log 2 - 287209/414355) + ((287209 / 414355 : ℝ) - 6931471805599453/10000000000000000)| := by ring_nf
    _ ≤ |Real.log 2 - 287209/414355| + |(287209 / 414355 : ℝ) - 6931471805599453/10000000000000000| := abs_add_le _ _
    _ ≤ 1/10^10 + 1/100000000000 := add_le_add h e
    _ = 11/100000000000 := by norm_num

theorem reals : Pia.Float.Exp.reals := by
  refine ⟨{ rexp := Real.exp, pw := fun n => scaled 1 n,
            pos_le1 := ?_, lower := ?_, taylor := ?_, pw_def := ?_,
            reduce := ?_, tiny_below := ?_ }⟩
  · intro x hx
    exact ⟨Real.exp_pos x, Real.exp_le_one_iff.mpr hx⟩
  · intro x; linarith [Real.add_one_le_exp x]
  · intro r ⟨h0, h1⟩
    rw [near_iff]
    have hr : |r| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hb := Real.exp_bound hr (n := 8) (by norm_num)
    have hs : (∑ i ∈ Finset.range 8, r ^ i / (Nat.factorial i : ℝ)) = t7 r := by
      simp [Finset.sum_range_succ, Nat.factorial, t7]; ring
    rw [hs] at hb
    have hp : |r| ^ 8 ≤ (36/100 : ℝ) ^ 8 := by
      apply pow_le_pow_left₀ (abs_nonneg r); rw [abs_le]; constructor <;> linarith
    calc |Real.exp r - t7 r| ≤ |r| ^ 8 * (↑(Nat.succ 8) / (↑(Nat.factorial 8) * ↑8)) := hb
      _ ≤ (36/100 : ℝ) ^ 8 * (↑(Nat.succ 8) / (↑(Nat.factorial 8) * ↑8)) := by
          apply mul_le_mul_of_nonneg_right hp; positivity
      _ ≤ 8/1000000000 := by norm_num [Nat.factorial]
  · intro n _; rfl
  · intro x n r ⟨h0, h1, hn⟩
    rw [near_iff] at hn ⊢
    rw [scaled_pow n h0 h1]
    set k := n.toNat with hk
    have hnk : (n : ℝ) = (k : ℝ) := by
      have : (k : ℤ) = n := Int.toNat_of_nonneg h0
      rw [← this]; norm_cast
    have hk150 : (k : ℝ) ≤ 150 := by rw [← hnk]; exact_mod_cast h1
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set D := x + k * Real.log 2 - r with hD
    -- exp x = exp r * exp D * (1/2)^k
    have hx : Real.exp x = Real.exp r * Real.exp D * ((1:ℝ)/2) ^ k := by
      have h2 : Real.exp (k * Real.log 2) = 2 ^ k := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      have : x = r + D - k * Real.log 2 := by rw [hD]; ring
      rw [this, Real.exp_sub, Real.exp_add, h2, one_div, inv_pow]
      ring
    have hDb : |D| ≤ 17/1000000000 := by
      have hl := log_two_near
      rw [hnk] at hn
      have e1 : D = (x + k * (6931471805599453/10000000000000000) - r) + k * (Real.log 2 - 6931471805599453/10000000000000000) := by
        rw [hD]; ring
      rw [e1]
      calc |(x + k * (6931471805599453/10000000000000000) - r) + k * (Real.log 2 - 6931471805599453/10000000000000000)|
          ≤ |x + k * (6931471805599453/10000000000000000) - r| + |k * (Real.log 2 - 6931471805599453/10000000000000000)| := abs_add_le _ _
        _ ≤ 1/1000000000000 + 150 * (11/100000000000) := by
            apply add_le_add
            · rw [abs_sub_comm]; convert hn using 2
            · rw [abs_mul, abs_of_nonneg hk0]
              exact mul_le_mul hk150 hl (abs_nonneg _) (by norm_num)
        _ ≤ 17/1000000000 := by norm_num
    have hD1 : |D| ≤ 1 := le_trans hDb (by norm_num)
    have he := Real.exp_bound hD1 (n := 2) (by norm_num)
    simp [Finset.sum_range_succ] at he
    have hd2 : |Real.exp D - 1| ≤ 2/100000000 := by
      have : |Real.exp D - 1| ≤ |Real.exp D - (1 + D)| + |D| := by
        calc |Real.exp D - 1| = |(Real.exp D - (1 + D)) + D| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have hsq : |D| ^ 2 ≤ (17/1000000000) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hDb 2
      have h3 : |Real.exp D - (1 + D)| ≤ |D| ^ 2 * (3 / (2 * 2)) := by
        rw [sq_abs]; exact he
      have h4 : |D| ^ 2 * (3 / (2 * 2)) ≤ (17/1000000000) ^ 2 * (3 / (2 * 2)) :=
        mul_le_mul_of_nonneg_right hsq (by norm_num)
      have h5 : (17/1000000000 : ℝ) ^ 2 * (3 / (2 * 2)) + 17/1000000000 ≤ 2/100000000 := by
        norm_num
      linarith
    have hP : 0 < Real.exp r * ((1:ℝ)/2) ^ k := by positivity
    rw [hx]
    have : Real.exp r * Real.exp D * (1 / 2) ^ k - Real.exp r * (1 / 2) ^ k
        = (Real.exp r * (1/2) ^ k) * (Real.exp D - 1) := by ring
    rw [this, abs_mul, abs_of_pos hP]
    nlinarith
  · intro x hx
    have h1 : Real.exp x ≤ Real.exp (-104) := Real.exp_le_exp.mpr hx
    have h2 : (271/100 : ℝ) ^ 104 ≤ Real.exp 104 := by
      have e : Real.exp 104 = Real.exp 1 ^ 104 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 104
    have h3 : Real.exp (-104) = (Real.exp 104)⁻¹ := by rw [Real.exp_neg]
    rw [h3] at h1
    have h4 : (Real.exp 104)⁻¹ ≤ ((271/100 : ℝ) ^ 104)⁻¹ :=
      inv_anti₀ (by positivity) h2
    have h5 : ((271/100 : ℝ) ^ 104)⁻¹ ≤ 1/1000000000000000000000000000000000000000000000 := by
      norm_num
    linarith

end ExpProofs
