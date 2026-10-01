/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Scalar

/-! # An explicit remainder for the guaranteed gap fraction

The error bound below proves the manuscript's stated big-O expansion with
constant 162, without introducing an unspecified asymptotic constant.
-/

noncomputable section
namespace Nonadditivity.Scalar

theorem gap_fraction_identity {K : ℝ} (hK : 1 < K) :
    deltaK K / log2 K = 1 / K - 2 * Real.log (1 + 9 / K) / Real.log K := by
  have hlog := (Real.log_pos hK).ne'
  unfold deltaK aK log2
  field_simp

private theorem log_remainder_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - Real.log (1 + x) ∧ x - Real.log (1 + x) ≤ x^2 := by
  have hp : 0 < 1 + x := by linarith
  have hu := Real.log_le_sub_one_of_pos hp
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hrec : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [hrec] at hl
  have hb : x - x / (1 + x) ≤ x^2 := by
    apply (le_of_mul_le_mul_right (a := 1+x) ?_ hp)
    field_simp
    nlinarith [sq_nonneg x]
  exact ⟨by linarith, by linarith⟩

/-- In particular `r_K = (1 - 18 / ln K) / K + O(1/(K² ln K))`. -/
theorem gap_fraction_explicit_remainder {K : ℝ} (hK : 1 < K) :
    0 ≤ deltaK K / log2 K - (1 - 18 / Real.log K) / K ∧
    deltaK K / log2 K - (1 - 18 / Real.log K) / K ≤
      162 / (K^2 * Real.log K) := by
  have hK0 : 0 < K := by linarith
  have hl : 0 < Real.log K := Real.log_pos hK
  have hx := log_remainder_bounds (by positivity : 0 ≤ 9 / K)
  have he : deltaK K / log2 K - (1 - 18 / Real.log K) / K =
      2 * (9 / K - Real.log (1 + 9 / K)) / Real.log K := by
    rw [gap_fraction_identity hK]
    ring
  rw [he]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hx.1) hl.le
  · calc
      2 * (9 / K - Real.log (1 + 9 / K)) / Real.log K ≤
          2 * (9 / K)^2 / Real.log K := by gcongr; exact hx.2
      _ = 162 / (K^2 * Real.log K) := by ring

end Nonadditivity.Scalar
