/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Quantitative
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.GCongr

/-! # The tracked scalar constants in the two-generator Haar moment estimate

These are numerical inequalities and finite-sum consequences.  No Haar
moment estimate is assumed or asserted here: the final assembly consumes
explicit bounds for each nonzero word-length contribution.
-/
noncomputable section
namespace Nonadditivity.HaarMomentConstants
open scoped BigOperators

def alpha (p N : ℝ) : ℝ := 128 * p ^ 20 / N ^ (1 / 4 : ℝ)
def beta (p N : ℝ) : ℝ := 4096 * p ^ 38 / N

/-- The prefactor in the unitary entry-moment estimate of BC Lemma 5.4. -/
theorem entry_prefactor_bound {r N : ℝ} (hN : 0 < N)
    (hr : 2 * r ^ (7 / 2 : ℝ) ≤ N ^ 2) :
    1 + 3 * r ^ (7 / 2 : ℝ) / N ^ 2 ≤ 5 / 2 := by
  have : 3 * r ^ (7 / 2 : ℝ) / N ^ 2 ≤ 3 / 2 := by
    apply (div_le_iff₀ (pow_pos hN 2)).2
    linarith
  linarith

/-- Two independent Haar matrices give exactly the prefactor `25/4`;
adjoint entries remain in their original independent family. -/
theorem two_entry_prefactors_bound {x y : ℝ} (hx : x ≤ 5 / 2)
    (hy0 : 0 ≤ y) (hy : y ≤ 5 / 2) : x * y ≤ 25 / 4 := by
  calc
    x * y ≤ (5 / 2) * y := mul_le_mul_of_nonneg_right hx hy0
    _ ≤ (5 / 2) * (5 / 2) := mul_le_mul_of_nonneg_left hy (by norm_num)
    _ = _ := by norm_num

theorem local_alpha_le {p N t : ℝ} (hp : 0 ≤ p) (hN : 0 ≤ N)
    (ht0 : 0 ≤ t) (ht : t ≤ p) :
    128 * t ^ 11 * p ^ 9 / N ^ (1 / 4 : ℝ) ≤ alpha p N := by
  unfold alpha
  calc
    _ ≤ 128 * p ^ 11 * p ^ 9 / N ^ (1 / 4 : ℝ) := by gcongr
    _ = _ := by ring

theorem local_beta_le {p N t : ℝ} (hN : 0 ≤ N)
    (ht0 : 0 ≤ t) (ht : t ≤ p) :
    4096 * t ^ 20 * p ^ 18 / N ≤ beta p N := by
  unfold beta
  calc
    _ ≤ 4096 * p ^ 20 * p ^ 18 / N := by gcongr
    _ = _ := by ring

theorem dimension_pos {p N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) : 0 < N := by
  have : 0 < 2 ^ 32 * p ^ 80 := by positivity
  linarith

theorem fourth_root_lower {p N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) :
    256 * p ^ 20 ≤ N ^ (1 / 4 : ℝ) := by
  have hN0 := (dimension_pos hp hN).le
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
    (Real.rpow_nonneg hN0 _)
  have he : (N ^ (1 / 4 : ℝ)) ^ 4 = N := by
    simpa using Real.rpow_inv_natCast_pow hN0 (by norm_num : (4 : ℕ) ≠ 0)
  rw [he]
  convert hN using 1
  ring

theorem square_root_lower {p N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) :
    65536 * p ^ 40 ≤ N ^ (1 / 2 : ℝ) := by
  have hN0 := (dimension_pos hp hN).le
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num)
    (Real.rpow_nonneg hN0 _)
  have he : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    simpa using Real.rpow_inv_natCast_pow hN0 (by norm_num : (2 : ℕ) ≠ 0)
  rw [he]
  convert hN using 1
  ring

theorem alpha_bounds {p N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) : 0 ≤ alpha p N ∧ alpha p N ≤ 1 / 2 := by
  have hN0 := dimension_pos hp hN
  have hr := fourth_root_lower hp hN
  unfold alpha
  constructor
  · positivity
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)).2
    linarith

theorem beta_bounds {p N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) : 0 ≤ beta p N ∧ beta p N ≤ 1 / 2 := by
  have hN0 := dimension_pos hp hN
  have hpow : p ^ 38 ≤ p ^ 80 := pow_le_pow_right₀ (by linarith) (by norm_num)
  unfold beta
  constructor
  · positivity
  · apply (div_le_iff₀ hN0).2
    have hpow0 : 0 ≤ p ^ 80 := by positivity
    norm_num at hN
    nlinarith

theorem exponential_bound {p N t : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) (ht0 : 0 ≤ t) (ht : t ≤ p) :
    Real.exp (t ^ 2 / N ^ (1 / 4 : ℝ)) ≤ Real.exp 1 := by
  have hN0 := dimension_pos hp hN
  have hr := fourth_root_lower hp hN
  have ht2 : t ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ ht0 ht _
  have hp2 : p ^ 2 ≤ p ^ 20 := pow_le_pow_right₀ (by linarith) (by norm_num)
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)).2
  nlinarith [show 0 ≤ p ^ 20 by positivity]

theorem geometric_sum_bound {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (s : ℕ) :
    (∑ i ∈ Finset.range s, q ^ i) ≤ 2 := by
  have hs : ∀ s : ℕ, (∑ i ∈ Finset.range s, q ^ i) ≤ 2 * (1 - q ^ s) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left hq (pow_nonneg hq0 s)]
  exact (hs s).trans (by nlinarith [pow_nonneg hq0 s])

/-- The exact constant after the two geometric sums and the length sum. -/
theorem final_error_bound {p N : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) :
    6400 * Real.exp 1 * p ^ 24 / N ≤ N ^ (-(1 / 2 : ℝ)) := by
  have hN0 := dimension_pos hp hN
  have hs := square_root_lower hp hN
  have hpow : p ^ 24 ≤ p ^ 40 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsmall : 6400 * Real.exp 1 * p ^ 24 ≤ N ^ (1 / 2 : ℝ) := by
    have he := Real.exp_one_lt_three
    have hp0 : 0 ≤ p ^ 24 := by positivity
    have hmul := mul_le_mul_of_nonneg_right he.le hp0
    nlinarith
  have hroot : N ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [Real.rpow_neg hN0.le, ← one_div]
  apply (div_le_div_iff₀ hN0 (Real.rpow_pos_of_pos hN0 _)).2
  nlinarith [mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hN0.le (1 / 2 : ℝ))]

/-- The literal scalar majorant in the proof of BC Theorem 5.1 at two
generators, with finite partial geometric sums. -/
def lengthMajorant (p N t : ℝ) (a b : ℕ) : ℝ :=
  (25 / 4) * (4 * t ^ 3) ^ 4 * p ^ 11 / N *
    Real.exp (t ^ 2 / N ^ (1 / 4 : ℝ)) *
    (∑ i ∈ Finset.range a, (alpha p N) ^ i) *
    (∑ i ∈ Finset.range b, (beta p N) ^ i)

theorem lengthMajorant_le {p N t : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * p ^ 80 ≤ N) (ht0 : 0 ≤ t) (ht : t ≤ p) (a b : ℕ) :
    lengthMajorant p N t a b ≤ 6400 * Real.exp 1 * p ^ 11 / N * t ^ 12 := by
  have hN0 := dimension_pos hp hN
  obtain ⟨ha0, ha⟩ := alpha_bounds hp hN
  obtain ⟨hb0, hb⟩ := beta_bounds hp hN
  have hea := geometric_sum_bound ha0 ha a
  have heb := geometric_sum_bound hb0 hb b
  have he := exponential_bound hp hN ht0 ht
  unfold lengthMajorant
  calc
    _ ≤ (25 / 4) * (4 * t ^ 3) ^ 4 * p ^ 11 / N * Real.exp 1 * 2 * 2 := by
      gcongr
    _ = _ := by ring

theorem length_sum_bound (p : ℕ) :
    (∑ t ∈ Finset.Icc 1 p, (t : ℝ) ^ 12) ≤ (p : ℝ) ^ 13 := by
  calc
    _ ≤ ∑ _t ∈ Finset.Icc 1 p, (p : ℝ) ^ 12 := by
      apply Finset.sum_le_sum
      intro t ht
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (Finset.mem_Icc.mp ht).2
    _ = (p : ℝ) ^ 13 := by simp [pow_succ]; ring

/-- Conditional assembly of the path-length estimates; the supplied premise
is precisely the separate analytic/combinatorial work, not the final claim. -/
theorem sum_length_errors_le {p : ℕ} {N ρ : ℝ} (hp : 2 ≤ p)
    (hN : 2 ^ 32 * (p : ℝ) ^ 80 ≤ N) (hρ : 0 ≤ ρ)
    (D : ℕ → ℝ) (a b : ℕ → ℕ)
    (hD : ∀ t ∈ Finset.Icc 1 p,
      |D t| ≤ lengthMajorant p N t (a t) (b t) * ρ ^ p) :
    |∑ t ∈ Finset.Icc 1 p, D t| ≤ N ^ (-(1 / 2 : ℝ)) * ρ ^ p := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hN0 := dimension_pos hpr hN
  have hpoint : ∀ t ∈ Finset.Icc 1 p,
      |D t| ≤ (6400 * Real.exp 1 * (p : ℝ) ^ 11 / N * (t : ℝ) ^ 12) * ρ ^ p := by
    intro t ht
    exact (hD t ht).trans (mul_le_mul_of_nonneg_right
      (lengthMajorant_le hpr hN (by positivity)
        (by exact_mod_cast (Finset.mem_Icc.mp ht).2) (a t) (b t)) (pow_nonneg hρ p))
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 p, |D t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 p,
        (6400 * Real.exp 1 * (p : ℝ) ^ 11 / N * (t : ℝ) ^ 12) * ρ ^ p :=
      Finset.sum_le_sum hpoint
    _ = (6400 * Real.exp 1 * (p : ℝ) ^ 11 / N *
        (∑ t ∈ Finset.Icc 1 p, (t : ℝ) ^ 12)) * ρ ^ p := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (6400 * Real.exp 1 * (p : ℝ) ^ 11 / N * (p : ℝ) ^ 13) * ρ ^ p := by
      gcongr
      exact length_sum_bound p
    _ = (6400 * Real.exp 1 * (p : ℝ) ^ 24 / N) * ρ ^ p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (final_error_bound hpr hN) (pow_nonneg hρ p)

end Nonadditivity.HaarMomentConstants
