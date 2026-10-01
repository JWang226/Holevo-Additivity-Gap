/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMomentConstants

/-! # Polynomial slack in the prescribed-dimension moment estimate

The tracked dimension hypothesis absorbs up to sixteen additional powers
of the moment order. In particular, a corrected path encoding may use an
extra factor `m^3` without changing the prescribed dimension or the final
`N^(-1/2)` error. These are numerical implications; no path count is assumed
to have been proved by this module.
-/

noncomputable section
namespace Nonadditivity.HaarMomentConstants
open scoped BigOperators

theorem final_error_bound_with_overhead {p N : ℝ} {k : ℕ}
    (hp : 2 ≤ p) (hN : 2 ^ 32 * p ^ 80 ≤ N) (hk : k ≤ 16) :
    6400 * Real.exp 1 * p ^ (24 + k) / N ≤ N ^ (-(1 / 2 : ℝ)) := by
  have hN0 := dimension_pos hp hN
  have hs := square_root_lower hp hN
  have hpow : p ^ (24 + k) ≤ p ^ 40 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hsmall : 6400 * Real.exp 1 * p ^ (24 + k) ≤ N ^ (1 / 2 : ℝ) := by
    have he := Real.exp_one_lt_three
    have hp0 : 0 ≤ p ^ (24 + k) := by positivity
    have hmul := mul_le_mul_of_nonneg_right he.le hp0
    nlinarith
  have hroot : N ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [Real.rpow_neg hN0.le, ← one_div]
  apply (div_le_div_iff₀ hN0 (Real.rpow_pos_of_pos hN0 _)).2
  nlinarith [mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hN0.le (1 / 2 : ℝ))]

theorem length_sum_bound_with_overhead (p k : ℕ) :
    (∑ t ∈ Finset.Icc 1 p, (t : ℝ) ^ (12 + k)) ≤ (p : ℝ) ^ (13 + k) := by
  calc
    _ ≤ ∑ _t ∈ Finset.Icc 1 p, (p : ℝ) ^ (12 + k) := by
      apply Finset.sum_le_sum
      intro t ht
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (Finset.mem_Icc.mp ht).2
    _ = _ := by
      rw [show 13 + k = (12 + k) + 1 by omega, pow_succ]
      simp [mul_comm]

/-- The complete length sum remains within the same target error after a
polynomial overhead of degree at most sixteen in the path count. -/
theorem sum_length_errors_le_with_overhead {p k : ℕ} {N ρ : ℝ}
    (hp : 2 ≤ p) (hN : 2 ^ 32 * (p : ℝ) ^ 80 ≤ N)
    (hk : k ≤ 16) (hρ : 0 ≤ ρ)
    (D : ℕ → ℝ) (a b : ℕ → ℕ)
    (hD : ∀ t ∈ Finset.Icc 1 p,
      |D t| ≤ (t : ℝ) ^ k * lengthMajorant p N t (a t) (b t) * ρ ^ p) :
    |∑ t ∈ Finset.Icc 1 p, D t| ≤ N ^ (-(1 / 2 : ℝ)) * ρ ^ p := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hN0 := dimension_pos hpr hN
  have hpoint : ∀ t ∈ Finset.Icc 1 p,
      |D t| ≤ (6400 * Real.exp 1 * (p : ℝ) ^ 11 / N * (t : ℝ) ^ (12+k)) * ρ ^ p := by
    intro t ht
    apply (hD t ht).trans
    have hb := lengthMajorant_le hpr hN (by positivity : (0:ℝ) ≤ t)
      (by exact_mod_cast (Finset.mem_Icc.mp ht).2) (a t) (b t)
    calc
      _ ≤ (t : ℝ)^k * (6400 * Real.exp 1 * (p : ℝ)^11 / N * (t : ℝ)^12) * ρ^p := by
        gcongr
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 p, |D t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 p,
        (6400 * Real.exp 1 * (p : ℝ)^11 / N * (t : ℝ)^(12+k)) * ρ^p :=
      Finset.sum_le_sum hpoint
    _ = (6400 * Real.exp 1 * (p : ℝ)^11 / N *
        (∑ t ∈ Finset.Icc 1 p, (t : ℝ)^(12+k))) * ρ^p := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (6400 * Real.exp 1 * (p : ℝ)^11 / N * (p : ℝ)^(13+k)) * ρ^p := by
      gcongr
      exact length_sum_bound_with_overhead p k
    _ = (6400 * Real.exp 1 * (p : ℝ)^(24+k) / N) * ρ^p := by
      rw [show 24+k = 11+(13+k) by omega, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (final_error_bound_with_overhead hpr hN hk) (pow_nonneg hρ p)

end Nonadditivity.HaarMomentConstants
