/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMomentConstants
import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact scalar factors for Haar tensor replacement

This file connects the actual prescribed moment order to the dimension
condition used by the growing-moment estimate. It also expresses the tensor
iteration's moment multiplier in the precise logarithmic form consumed by
the channel construction.
-/

noncomputable section
namespace Nonadditivity.HaarTensorConstants
open scoped BigOperators

/-- The prescribed even order has sufficient slack for the tracked
two-generator growing-moment estimate. -/
theorem moment_parameter_dimension_bound {h n : ℝ}
    (hh : (2 : ℝ) / 3 ≤ h) (hn : 2 ≤ n) :
    2 ^ 32 * (Quantitative.momentParameter h n : ℝ) ^ 80 ≤
      (Quantitative.dimensionChoice h n : ℝ) := by
  obtain ⟨_, _, _, hp⟩ := Quantitative.moment_parameter_bounds hh hn
  have hD : 0 < (Quantitative.dimensionChoice h n : ℝ) :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have htwop : 2 * (Quantitative.momentParameter h n : ℝ) ≤
      Real.exp (Real.log (Quantitative.dimensionChoice h n : ℝ) / 80) := by
    linarith
  have he : (Real.exp (Real.log (Quantitative.dimensionChoice h n : ℝ) / 80)) ^ 80 =
      (Quantitative.dimensionChoice h n : ℝ) := by
    rw [← Real.exp_nat_mul]
    have ha : (80 : ℝ) * (Real.log (Quantitative.dimensionChoice h n : ℝ) / 80) =
        Real.log (Quantitative.dimensionChoice h n : ℝ) := by ring
    norm_num only [Nat.cast_ofNat]
    rw [ha]
    rw [Real.exp_log hD]
  calc
    _ ≤ (2 * (Quantitative.momentParameter h n : ℝ)) ^ 80 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ _ := he ▸ pow_le_pow_left₀ (by positivity) htwop 80

def triangle (n : ℕ) : ℕ := n * (n + 1) / 2

theorem triangle_cast (n : ℕ) :
    (triangle n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  rw [triangle, Nat.cast_div (Nat.two_dvd_mul_add_one n) (by norm_num)]
  push_cast
  rfl

/-- The generous power-form multiplier in the manuscript's expectation
bound, before taking the `p`th root. -/
def momentMultiplier (m D : ℝ) (p n : ℕ) : ℝ :=
  (2 * m) ^ (n + 1) * D ^ triangle n * (p : ℝ) ^ (3 * triangle n) *
    (1 + D ^ (-(1 / 2 : ℝ))) ^ (n * p)

theorem momentMultiplier_pos {m D : ℝ} (hm : 0 < m) (hD : 0 < D)
    {p n : ℕ} (hp : 0 < p) : 0 < momentMultiplier m D p n := by
  unfold momentMultiplier
  positivity

/-- Exact conversion to the logarithmic factor already used by the explicit
dimension proof; no asymptotic simplification is made here. -/
theorem momentMultiplier_root_eq_exp {h m : ℝ} {n : ℕ}
    (hh : (2 : ℝ) / 3 ≤ h) (hn : 2 ≤ n) (hm : 0 < m) :
    (momentMultiplier m (Quantitative.dimensionChoice h n)
      (Quantitative.momentParameter h n) n) ^
        (1 / (Quantitative.momentParameter h n : ℝ)) =
      Real.exp (Quantitative.haarLogMultiplier h n (Real.log (2 * m))) := by
  obtain ⟨_, hp, _, _⟩ := Quantitative.moment_parameter_bounds (n := (n : ℝ)) hh
    (by exact_mod_cast hn)
  have hp0 : 0 < Quantitative.momentParameter h (n : ℝ) := by omega
  have hD : 0 < (Quantitative.dimensionChoice h n : ℝ) :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have hR : 0 < 1 + (Quantitative.dimensionChoice h n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    positivity
  rw [Real.rpow_def_of_pos (momentMultiplier_pos hm hD hp0)]
  congr 1
  unfold momentMultiplier
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
    triangle_cast]
  have hroot : (Quantitative.dimensionChoice h n : ℝ) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-(Real.log (Quantitative.dimensionChoice h n : ℝ) / 2)) := by
    rw [Real.rpow_def_of_pos hD]
    congr 1
    ring
  rw [hroot]
  unfold Quantitative.haarLogMultiplier
  have hpnz : (Quantitative.momentParameter h (n : ℝ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The smaller multiplier obtained by replacing one coordinate at a time. -/
def replacementMultiplier (m D : ℝ) (p n : ℕ) : ℝ :=
  (2 * m) ^ n * D ^ triangle n * (p : ℝ) ^ (3 * (n * (n - 1) / 2)) *
    (1 + D ^ (-(1 / 2 : ℝ))) ^ n

/-- The actual iteration leaves slack in the coefficient, free-coordinate,
and error factors, all in the favorable direction. -/
theorem replacementMultiplier_le {m D : ℝ} (hm : 1 ≤ m) (hD : 0 ≤ D)
    {p n : ℕ} (hp : 1 ≤ p) :
    replacementMultiplier m D p n ≤ momentMultiplier m D p n := by
  have ht : n * (n - 1) / 2 ≤ triangle n := by
    unfold triangle
    exact Nat.div_le_div_right (Nat.mul_le_mul_left n (by omega))
  have he : n ≤ n * p := by nlinarith
  have hc : (2 * m) ^ n ≤ (2 * m) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hpow : (p : ℝ) ^ (3 * (n * (n - 1) / 2)) ≤
      (p : ℝ) ^ (3 * triangle n) :=
    pow_le_pow_right₀ (by exact_mod_cast hp) (Nat.mul_le_mul_left 3 ht)
  have hr : (1 + D ^ (-(1 / 2 : ℝ))) ^ n ≤
      (1 + D ^ (-(1 / 2 : ℝ))) ^ (n * p) :=
    pow_le_pow_right₀ (by linarith [Real.rpow_nonneg hD (-(1 / 2 : ℝ))]) he
  unfold replacementMultiplier momentMultiplier
  have hab := mul_le_mul_of_nonneg_right hc (pow_nonneg hD (triangle n))
  have habc := mul_le_mul hab hpow (by positivity) (by positivity)
  exact mul_le_mul habc hr (by positivity) (by positivity)

/-- The dimension exponents accumulate to the triangular number. -/
theorem sum_stage_dimension (n : ℕ) :
    (∑ k ∈ Finset.range n, (k + 1)) = triangle n := by
  have h := Finset.sum_range_id (n + 1)
  rw [Finset.sum_range_succ'] at h
  simpa [triangle, Nat.mul_comm] using h

/-- The count of free coordinates decreases once at every replacement. -/
theorem sum_stage_free (n : ℕ) :
    (∑ k ∈ Finset.range n, 3 * (n - (k + 1))) = 3 * (n * (n - 1) / 2) := by
  calc
    _ = ∑ k ∈ Finset.range n, 3 * (n - 1 - k) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_reflect (fun k : ℕ => k), Finset.sum_range_id]

/-- Exact product of the costs at all forward replacement stages. -/
theorem prod_stage_factors (m D : ℝ) (p n : ℕ) :
    (∏ k ∈ Finset.range n,
      (2 * m * D ^ (k + 1) * (p : ℝ) ^ (3 * (n - (k + 1))) *
        (1 + D ^ (-(1 / 2 : ℝ))))) = replacementMultiplier m D p n := by
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    sum_stage_dimension, sum_stage_free]
  simp [replacementMultiplier, mul_pow]

theorem triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + n + 1 := by
  rw [← sum_stage_dimension, Finset.sum_range_succ, sum_stage_dimension]
  omega

theorem triangle_eq_lower_add (n : ℕ) :
    triangle n = n * (n - 1) / 2 + n := by
  rw [← sum_stage_dimension, Finset.sum_add_distrib, Finset.sum_range_id]
  simp

theorem replacementMultiplier_nonneg {m D : ℝ} (hm : 0 ≤ m) (hD : 0 ≤ D)
    (p n : ℕ) : 0 ≤ replacementMultiplier m D p n := by
  unfold replacementMultiplier
  positivity

/-- The coefficient index grows by one matrix factor at every recursive
replacement. This identity records that growth without any loss. -/
theorem replacementMultiplier_succ (m D : ℝ) (p n : ℕ) :
    replacementMultiplier (m * D) D p n *
      (2 * m * D * (p : ℝ) ^ (3 * n) * (1 + D ^ (-(1 / 2 : ℝ)))) =
        replacementMultiplier m D p (n + 1) := by
  have hl : (n + 1) * ((n + 1) - 1) / 2 = triangle n := by
    simp [triangle, Nat.mul_comm]
  unfold replacementMultiplier
  rw [hl, triangle_succ, triangle_eq_lower_add]
  simp only [mul_pow, pow_add, pow_one, Nat.mul_add]
  ring

end Nonadditivity.HaarTensorConstants
