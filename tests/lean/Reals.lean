import Statements
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Reals

theorem halves : reals.halves := by
  intro x n hn
  refine ⟨?_, ?_⟩
  · simp only [reals.half]; ring
  · have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    positivity

theorem exps : reals.exps :=
  ⟨{ cell := Unit, size := fun _ => 0, rate := Real.exp,
     rate_pos := fun x => Real.exp_pos x,
     rate_mono := fun _ _ h => Real.exp_le_exp.mpr h }⟩

end Reals
