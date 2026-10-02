/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMomentConstants
import Mathlib.Tactic.IntervalCases

/-! # The sharp scalar budget at the original Haar dimension threshold

The polynomial prefactor is bounded uniformly for every integer moment
order at least two. Together with the original square-root dimension
budget this yields the final inverse-square-root error without increasing
the prescribed constant `2^32`.
-/

noncomputable section
namespace Nonadditivity.HaarSharpConstants

set_option maxHeartbeats 0 in
/-- A uniform bound on the moment-order prefactor. The finite initial range
is checked by exact rational arithmetic; the tail uses `exp 1 < 3`. -/
theorem polynomial_prefactor_bound (p : ℕ) (hp : 2 ≤ p) :
    (1 + 64 / (p : ℝ)) ^ p ≤ 16 * (p : ℝ) ^ 14 := by
  by_cases hlarge : 128 ≤ p
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp)
    have hbase : 1 + 64 / (p : ℝ) ≤ Real.exp (64 / (p : ℝ)) := by
      simpa only [add_comm] using Real.add_one_le_exp (64 / (p : ℝ))
    have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + 64 / (p : ℝ) by positivity) hbase p
    have hexp : (Real.exp (64 / (p : ℝ))) ^ p = Real.exp 64 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have he64 : Real.exp (64 : ℝ) ≤ (3 : ℝ) ^ 64 := by
      calc
        Real.exp (64 : ℝ) = (Real.exp 1) ^ (64 : ℕ) := by
          rw [← Real.exp_nat_mul]
          norm_num
        _ ≤ (3 : ℝ) ^ 64 := pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_three.le _
    have hfinite : (3 : ℝ) ^ 64 ≤ 16 * (128 : ℝ) ^ 14 := by norm_num
    have hp128 : (128 : ℝ) ≤ p := by exact_mod_cast hlarge
    exact (hpow.trans_eq hexp).trans (he64.trans (hfinite.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hp128 14) (by norm_num))))
  · have hsmall : p ≤ 127 := by omega
    interval_cases p <;> norm_num

/-- The corrected full prefactor fits the original prescribed dimension
bound, with no enlargement of its numerical constant. -/
theorem sharp_final_error_bound {p : ℕ} {N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * (p : ℝ) ^ 80 ≤ N) :
    4096 * (p : ℝ) ^ 26 / N * (1 + 64 / (p : ℝ)) ^ p ≤
      N ^ (-(1 / 2 : ℝ)) := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hN0 := HaarMomentConstants.dimension_pos hpr hN
  have hs := HaarMomentConstants.square_root_lower hpr hN
  have hsmall : 4096 * (p : ℝ) ^ 26 * (1 + 64 / (p : ℝ)) ^ p ≤
      N ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ 4096 * (p : ℝ) ^ 26 * (16 * (p : ℝ) ^ 14) :=
        mul_le_mul_of_nonneg_left (polynomial_prefactor_bound p hp) (by positivity)
      _ = 65536 * (p : ℝ) ^ 40 := by ring
      _ ≤ _ := hs
  have hroot : N ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN0]
    norm_num
  have hrewrite : 4096 * (p : ℝ) ^ 26 / N * (1 + 64 / (p : ℝ)) ^ p =
      (4096 * (p : ℝ) ^ 26 * (1 + 64 / (p : ℝ)) ^ p) / N := by ring
  rw [hrewrite, Real.rpow_neg hN0.le, ← one_div]
  apply (div_le_div_iff₀ hN0 (Real.rpow_pos_of_pos hN0 _)).mpr
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hN0.le (1 / 2 : ℝ))).trans_eq hroot

end Nonadditivity.HaarSharpConstants
