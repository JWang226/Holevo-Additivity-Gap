/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-! # Simultaneous scalar parameters for the Gaussian construction -/
noncomputable section

namespace Nonadditivity.GaussianScalar

/-- One sufficiently large integer makes the one-use upper bound arbitrarily
small and the two-use ratio lower bound arbitrarily large, simultaneously. -/
theorem exists_parameter {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ K : ℕ, 4096 ≤ K ∧
      (512:ℝ)^2 / ((K:ℝ) * Real.log 2) ≤ ε ∧
      R ≤ (Real.log K - 1) / (2 * (512:ℝ)^2) ∧
      0 ≤ Real.log K - 1 := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := (512:ℝ)^2
  have hC : 0 < C := by norm_num [C]
  obtain ⟨K, hK⟩ := exists_nat_gt
    (max (4096:ℝ) (max (C / (ε * Real.log 2)) (Real.exp (2*C*max R 0+1))))
  have hsize : (4096:ℝ) ≤ K := (le_max_left _ _).trans hK.le
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le (by norm_num) hsize
  have hsmall : C / (ε * Real.log 2) ≤ K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hK.le)
  have hexp : Real.exp (2*C*max R 0+1) ≤ K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hK.le)
  have hlarge : 2*C*max R 0+1 ≤ Real.log K := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hsize
  · change C / ((K:ℝ) * Real.log 2) ≤ ε
    apply (div_le_iff₀ (mul_pos hKpos hlogtwo)).mpr
    have hs := (div_le_iff₀ (mul_pos hε hlogtwo)).mp hsmall
    nlinarith
  · change R ≤ (Real.log K - 1) / (2*C)
    apply (le_div_iff₀ (mul_pos (by norm_num) hC)).mpr
    have hm := mul_le_mul_of_nonneg_left (le_max_left R 0) (le_of_lt (mul_pos (by norm_num : (0:ℝ)<2) hC))
    linarith
  · have hm : 0 ≤ max R 0 := le_max_right _ _
    have hcmax : 0 ≤ 2*C*max R 0 := mul_nonneg (by positivity) hm
    linarith

end Nonadditivity.GaussianScalar
