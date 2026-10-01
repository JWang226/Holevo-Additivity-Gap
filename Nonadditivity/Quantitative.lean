/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact scalar estimates in the quantitative approximation argument

This file proves scalar estimates from the appendix of `nonadditivity.tex`.
All constants and inequalities below are checked by Lean.  Operator-algebraic
and random-matrix input is deliberately kept separate from these estimates.
-/

namespace Nonadditivity.Quantitative

noncomputable section

open Real

/-- A degree twelve Taylor term suffices to control every exponential tail
used in the appendix.  This avoids using unformalized derivative arguments. -/
theorem exp_dominates_power {x b C : ℝ} (k : ℕ) (hk : k ≤ 12)
    (hx : 64 ≤ x) (hb : 0 ≤ b)
    (hC : 64 * C * (Nat.factorial 12 : ℝ) ≤ b ^ 12 * 64 ^ (12 - k)) :
    64 * C * x ^ k ≤ Real.exp (b * x) := by
  have hx0 : 0 ≤ x := by linarith
  have hpower : (64 : ℝ) ^ (12 - k) ≤ x ^ (12 - k) :=
    pow_le_pow_left₀ (by norm_num) hx _
  have hcoeff : 64 * C * (Nat.factorial 12 : ℝ) ≤ b ^ 12 * x ^ (12 - k) :=
    hC.trans (mul_le_mul_of_nonneg_left hpower (pow_nonneg hb _))
  have hmul := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hx0 k)
  have hp : x ^ (12 - k) * x ^ k = x ^ 12 := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hf : (0 : ℝ) < Nat.factorial 12 := by norm_num
  calc
    64 * C * x ^ k ≤ (b * x) ^ 12 / (Nat.factorial 12 : ℝ) := by
      apply (le_div_iff₀ hf).2
      calc
        64 * C * x ^ k * (Nat.factorial 12 : ℝ) =
            64 * C * (Nat.factorial 12 : ℝ) * x ^ k := by ring
        _ ≤ b ^ 12 * x ^ (12 - k) * x ^ k := hmul
        _ = (b * x) ^ 12 := by rw [mul_assoc, hp, mul_pow]
    _ ≤ Real.exp (b * x) :=
      Real.pow_div_factorial_le_exp (b * x) (mul_nonneg hb hx0) 12

theorem exponential_tail_le {x b C : ℝ} (k : ℕ) (hk : k ≤ 12)
    (hx : 64 ≤ x) (hb : 0 ≤ b)
    (hC : 64 * C * (Nat.factorial 12 : ℝ) ≤ b ^ 12 * 64 ^ (12 - k)) :
    C * x ^ k * Real.exp (-(b * x)) ≤ (1 : ℝ) / 64 := by
  have h := exp_dominates_power k hk hx hb hC
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  linarith

/-- The precise three-tail expression occurring in the final norm error. -/
def tailBound (n : ℝ) : ℝ :=
  12 * n ^ 3 * Real.exp (-n / 2) +
    1494 * n ^ 4 * Real.exp (-3 * n / 2) + n ^ 2 * Real.exp (-n)

theorem final_three_tails_lt {n : ℝ} (hn : 64 ≤ n) : tailBound n < 1 / 16 := by
  have h₁ := exponential_tail_le (x := n) (b := (1 : ℝ) / 2)
    (C := 12) 3 (by norm_num) hn (by norm_num) (by norm_num)
  have h₂ := exponential_tail_le (x := n) (b := (3 : ℝ) / 2)
    (C := 1494) 4 (by norm_num) hn (by norm_num) (by norm_num)
  have h₃ := exponential_tail_le (x := n) (b := (1 : ℝ))
    (C := 1) 2 (by norm_num) hn (by norm_num) (by norm_num)
  have he₁ : -((1 : ℝ) / 2 * n) = -n / 2 := by ring
  have he₂ : -((3 : ℝ) / 2 * n) = -3 * n / 2 := by ring
  simp only [he₁] at h₁
  simp only [he₂] at h₂
  simp only [one_mul] at h₃
  dsimp [tailBound]
  linarith

def gamma (h : ℝ) : ℝ := 3 / 2 * h + 1 / 2
def zeta (h : ℝ) : ℝ := 2 * h + 1 / 2
def dimensionExponent (h : ℝ) : ℝ := 40 * (7 * h + 2)
def tolerance (h n : ℝ) : ℝ := Real.exp (-(gamma h * n)) / n
def dimensionChoice (h n : ℝ) : ℕ := ⌈Real.exp (dimensionExponent h * n)⌉₊
def momentChoice (t : ℝ) : ℕ := 2 * ⌊t / 4⌋₊

theorem parameter_alignment (h : ℝ) :
    dimensionExponent h / 80 = gamma h + zeta h := by
  dsimp [dimensionExponent, gamma, zeta]
  ring

theorem dimensionExponent_le {h : ℝ} (hh : 0 ≤ h) :
    dimensionExponent h ≤ 160 * zeta h := by
  dsimp [dimensionExponent, zeta]
  linarith

theorem coefficient_exponent_alignment (h : ℝ) :
    2 * h + gamma h - dimensionExponent h / 80 = -(1 / 2 : ℝ) := by
  dsimp [dimensionExponent, gamma]
  ring

theorem remainder_exponent_gap {h : ℝ} (hh : 0 ≤ h) :
    1 ≤ dimensionExponent h / 2 - gamma h := by
  dsimp [dimensionExponent, gamma]
  linarith

theorem dimension_choice_bounds {h n : ℝ} (hh : 0 ≤ h) (hn : 0 ≤ n) :
    Real.exp (dimensionExponent h * n) ≤ (dimensionChoice h n : ℝ) ∧
    (dimensionChoice h n : ℝ) ≤ 2 * Real.exp (dimensionExponent h * n) := by
  have hb : 0 ≤ dimensionExponent h := by dsimp [dimensionExponent]; positivity
  have he : 1 ≤ Real.exp (dimensionExponent h * n) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hb hn)
  refine ⟨Nat.le_ceil _, ?_⟩
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (dimensionExponent h * n)).le
  dsimp [dimensionChoice]
  linarith

theorem dimension_choice_log_bounds {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    dimensionExponent h * n ≤ Real.log (dimensionChoice h n : ℝ) ∧
    Real.log (dimensionChoice h n : ℝ) ≤ 2 * dimensionExponent h * n := by
  have hh0 : 0 ≤ h := by linarith
  have hn0 : 0 ≤ n := by linarith
  obtain ⟨hlo, hhi⟩ := dimension_choice_bounds hh0 hn0
  have hNpos : 0 < (dimensionChoice h n : ℝ) := (Real.exp_pos _).trans_le hlo
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  rw [Real.log_exp] at hl
  have hu := Real.log_le_log hNpos hhi
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hu
  have hb : 80 ≤ dimensionExponent h := by dsimp [dimensionExponent]; linarith
  have hbn : 160 ≤ dimensionExponent h * n := by
    nlinarith [mul_nonneg (show 0 ≤ dimensionExponent h - 80 by linarith) hn0]
  refine ⟨hl, ?_⟩
  linarith [Real.log_two_lt_d9]

theorem dimension_choice_log_upper {h n : ℝ} (hh : 0 ≤ h) (hn : 0 ≤ n) :
    Real.log (dimensionChoice h n : ℝ) ≤ dimensionExponent h * n + Real.log 2 := by
  obtain ⟨hlo, hhi⟩ := dimension_choice_bounds hh hn
  have hNpos : 0 < (dimensionChoice h n : ℝ) := (Real.exp_pos _).trans_le hlo
  have hu := Real.log_le_log hNpos hhi
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hu
  linarith

theorem moment_choice_bounds {t : ℝ} (ht : 8 ≤ t) :
    Even (momentChoice t) ∧ 2 ≤ momentChoice t ∧
    t / 4 ≤ (momentChoice t : ℝ) ∧ (momentChoice t : ℝ) ≤ t / 2 := by
  have ht0 : 0 ≤ t / 4 := by linarith
  have hf := Nat.floor_le ht0
  have hg := Nat.sub_one_lt_floor (t / 4)
  have hn : 1 ≤ ⌊t / 4⌋₊ := (Nat.one_le_floor_iff _).2 (by linarith)
  dsimp [momentChoice]
  refine ⟨even_two_mul _, by omega, ?_, ?_⟩ <;>
    simp only [Nat.cast_mul, Nat.cast_ofNat] <;> linarith

/-- `exp (log N / 80)` is exactly `N^(1/80)` for positive `N`. -/
def momentParameter (h n : ℝ) : ℕ :=
  momentChoice (Real.exp (Real.log (dimensionChoice h n : ℝ) / 80))

theorem moment_parameter_bounds {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    Even (momentParameter h n) ∧ 2 ≤ momentParameter h n ∧
    (Real.exp (Real.log (dimensionChoice h n : ℝ) / 80) / 4 ≤
      (momentParameter h n : ℝ)) ∧
    ((momentParameter h n : ℝ) ≤
      Real.exp (Real.log (dimensionChoice h n : ℝ) / 80) / 2) := by
  obtain ⟨hN, _⟩ := dimension_choice_log_bounds hh hn
  have hb : 80 * (10 : ℝ) / 3 ≤ dimensionExponent h := by
    dsimp [dimensionExponent]
    linarith
  have hn0 : 0 ≤ n := by linarith
  have hbig : 6 ≤ Real.log (dimensionChoice h n : ℝ) / 80 := by
    have hm := mul_le_mul_of_nonneg_right hb hn0
    nlinarith
  have he : Real.exp 6 ≤ Real.exp (Real.log (dimensionChoice h n : ℝ) / 80) :=
    Real.exp_le_exp.mpr hbig
  have h6 := Real.pow_div_factorial_le_exp (6 : ℝ) (by norm_num) 2
  norm_num at h6
  have ht : 8 ≤ Real.exp (Real.log (dimensionChoice h n : ℝ) / 80) := by linarith
  exact moment_choice_bounds ht

theorem moment_parameter_inverse_bound {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    1 / (momentParameter h n : ℝ) ≤
      4 * Real.exp (-(dimensionExponent h * n / 80)) := by
  obtain ⟨_, hp, hlo, _⟩ := moment_parameter_bounds hh hn
  have hp0 : (0 : ℝ) < momentParameter h n := by exact_mod_cast (by omega : 0 < momentParameter h n)
  obtain ⟨hN, _⟩ := dimension_choice_log_bounds hh hn
  have he := Real.exp_le_exp.mpr (show dimensionExponent h * n / 80 ≤
    Real.log (dimensionChoice h n : ℝ) / 80 by linarith)
  have hlow : Real.exp (dimensionExponent h * n / 80) / 4 ≤
      (momentParameter h n : ℝ) := (div_le_div_of_nonneg_right he (by norm_num)).trans hlo
  have hbound : 1 / (momentParameter h n : ℝ) ≤
      1 / (Real.exp (dimensionExponent h * n / 80) / 4) :=
    one_div_le_one_div_of_le (by positivity) hlow
  rw [Real.exp_neg]
  convert hbound using 1
  field_simp

theorem moment_parameter_log_bound {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    Real.log (momentParameter h n : ℝ) ≤
      Real.log (dimensionChoice h n : ℝ) / 80 := by
  obtain ⟨_, hp, _, hhi⟩ := moment_parameter_bounds hh hn
  have hp0 : (0 : ℝ) < momentParameter h n := by exact_mod_cast (by omega : 0 < momentParameter h n)
  have he := Real.exp_pos (Real.log (dimensionChoice h n : ℝ) / 80)
  have hle : (momentParameter h n : ℝ) ≤
      Real.exp (Real.log (dimensionChoice h n : ℝ) / 80) := by linarith
  have hl := Real.log_le_log hp0 hle
  simpa only [Real.log_exp] using hl

theorem remainder_log_bound {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    Real.log (1 + Real.exp (-(Real.log (dimensionChoice h n : ℝ) / 2))) ≤
      Real.exp (-(dimensionExponent h * n / 2)) := by
  have he := Real.exp_pos (-(Real.log (dimensionChoice h n : ℝ) / 2))
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1 +
    Real.exp (-(Real.log (dimensionChoice h n : ℝ) / 2)) by linarith)
  obtain ⟨hN, _⟩ := dimension_choice_log_bounds hh hn
  have hm := Real.exp_le_exp.mpr (show
    -(Real.log (dimensionChoice h n : ℝ) / 2) ≤ -(dimensionExponent h * n / 2) by linarith)
  linarith

theorem dimension_rpow_eq_exp (h n : ℝ) :
    (dimensionChoice h n : ℝ) ^ (1 / 80 : ℝ) =
      Real.exp (Real.log (dimensionChoice h n : ℝ) / 80) := by
  have hp : 0 < (dimensionChoice h n : ℝ) :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem moment_parameter_eq_original (h n : ℝ) :
    momentParameter h n =
      2 * ⌊((dimensionChoice h n : ℝ) ^ (1 / 80 : ℝ)) / 4⌋₊ := by
  rw [dimension_rpow_eq_exp]
  rfl

theorem moment_parameter_haar_range {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    Even (momentParameter h n) ∧ 2 ≤ momentParameter h n ∧
    (momentParameter h n : ℝ) ≤
      (2 : ℝ) ^ (-(2 / 5 : ℝ)) * (dimensionChoice h n : ℝ) ^ (1 / 80 : ℝ) := by
  obtain ⟨heven, hp, _, hhi⟩ := moment_parameter_bounds hh hn
  have hhalf : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-(2 / 5 : ℝ)) := by
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (-1 : ℝ) ≤ -(2 / 5 : ℝ))
    simpa only [Real.rpow_neg_one, one_div] using he
  have hm := mul_le_mul_of_nonneg_right hhalf
    (Real.exp_pos (Real.log (dimensionChoice h n : ℝ) / 80)).le
  rw [dimension_rpow_eq_exp]
  refine ⟨heven, hp, ?_⟩
  linarith

theorem tolerance_pos {h n : ℝ} (hn : 0 < n) : 0 < tolerance h n :=
  div_pos (Real.exp_pos _) hn

theorem tolerance_lt_one {h n : ℝ} (hh : 0 ≤ h) (hn : 2 ≤ n) :
    tolerance h n < 1 := by
  have hn0 : 0 < n := by linarith
  have hg : 0 ≤ gamma h := by dsimp [gamma]; linarith
  have he : Real.exp (-(gamma h * n)) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg hg hn0.le))
  dsimp [tolerance]
  apply (div_lt_iff₀ hn0).2
  linarith

/-- Tangency of the logarithm, applied to the square root. -/
theorem log_le_twice_sqrt_sub_one {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 2 * (Real.sqrt t - 1) := by
  have hs := Real.sqrt_pos.2 ht
  have hl := Real.log_le_sub_one_of_pos hs
  calc
    Real.log t = Real.log (Real.sqrt t ^ 2) :=
      congrArg Real.log (Real.sq_sqrt ht.le).symm
    _ = 2 * Real.log (Real.sqrt t) := by rw [Real.log_pow]; norm_num
    _ ≤ 2 * (Real.sqrt t - 1) := by linarith

theorem threshold_base_log {y : ℝ} (hy : (5 : ℝ) / 3 ≤ y) :
    y + Real.log (256 * y ^ 2) ≤ 5 * y := by
  have hy0 : 0 < y := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hy0 (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div hy0.ne' (by norm_num)] at hl
  have h2 : Real.log 2 < (7 : ℝ) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    have he : (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hy0.ne'), h256, Real.log_pow]
  norm_num
  linarith

/-- The threshold absorption estimate (equation `threshold-absorption`).
The proof uses an elementary logarithm inequality in place of monotonicity
of `x / (y + log x)^2`. -/
theorem threshold_absorption {y n : ℝ} (hy : (5 : ℝ) / 3 ≤ y)
    (hn : 256 * y ^ 2 ≤ n) :
    (y + Real.log n) ^ 2 ≤ (25 : ℝ) / 256 * n := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < 256 * y ^ 2 := by positivity
  have hn0 : 0 < n := hx0.trans_le hn
  have hr : 1 ≤ n / (256 * y ^ 2) := by
    apply (le_div_iff₀ hx0).2
    simpa using hn
  have hr0 : 0 < n / (256 * y ^ 2) := by linarith
  have hs1 : 1 ≤ Real.sqrt (n / (256 * y ^ 2)) := by
    exact (Real.le_sqrt (by norm_num) hr0.le).2 (by simpa using hr)
  have hlog := log_le_twice_sqrt_sub_one hr0
  rw [Real.log_div hn0.ne' hx0.ne'] at hlog
  have hbase := threshold_base_log hy
  have hprod : 0 ≤ (5 * y - 2) * (Real.sqrt (n / (256 * y ^ 2)) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hub : y + Real.log n ≤ 5 * y * Real.sqrt (n / (256 * y ^ 2)) := by
    nlinarith
  have hn1 : 1 ≤ n := by nlinarith [sq_nonneg (y - 5 / 3)]
  have hu0 : 0 ≤ y + Real.log n := add_nonneg hy0.le (Real.log_nonneg hn1)
  have hsq := sq_le_sq₀ hu0 (by positivity : 0 ≤ 5 * y * Real.sqrt (n / (256 * y ^ 2)))
  have hsquare : (5 * y * Real.sqrt (n / (256 * y ^ 2))) ^ 2 =
      (25 : ℝ) / 256 * n := by
    rw [mul_pow, Real.sq_sqrt hr0.le]
    field_simp
    ring
  rw [← hsquare]
  exact hsq.2 hub

/-- The two numerical absorptions used for the total error factor and
matrix coefficient cost, with the manuscript's exact constants. -/
theorem error_cost_absorption {u n : ℝ} (hu : (15 : ℝ) / 2 ≤ u)
    (hn : u ^ 2 ≤ (25 : ℝ) / 256 * n) :
    7 / 4 * u ^ 2 + 14 * u < n / 2 := by
  have hquad : 14 * u ≤ (28 : ℝ) / 15 * u ^ 2 := by
    nlinarith
  have hn0 : 0 < n := by nlinarith
  nlinarith

theorem coefficient_cost_absorption {u n : ℝ} (hu : (15 : ℝ) / 2 ≤ u)
    (hn : u ^ 2 ≤ (25 : ℝ) / 256 * n) :
    7 / 4 * u ^ 2 + 21 / 2 * u < n / 3 := by
  have hquad : 21 / 2 * u ≤ (7 : ℝ) / 5 * u ^ 2 := by
    nlinarith
  have hn0 : 0 < n := by nlinarith
  nlinarith

/-- The paper's explicit integer threshold, with natural-number ceiling. -/
def n₀ (K : ℕ) : ℕ := ⌈256 * (1 + Real.log (K : ℝ)) ^ 2⌉₊

theorem threshold_consequences {K n : ℕ} (hK : 2 ≤ K) (hn : n₀ K ≤ n) :
    (0 ≤ Real.log (K : ℝ)) ∧
    ((64 : ℝ) ≤ n) ∧
    ((15 : ℝ) / 2 ≤ 1 + Real.log (K : ℝ) + Real.log (n : ℝ)) ∧
    ((1 + Real.log (K : ℝ) + Real.log (n : ℝ)) ^ 2 ≤
      (25 : ℝ) / 256 * n) := by
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hKreal
  have hh : (2 : ℝ) / 3 ≤ Real.log (K : ℝ) := by
    linarith [Real.log_two_gt_d9]
  have hy : (5 : ℝ) / 3 ≤ 1 + Real.log (K : ℝ) := by linarith
  have hbase : 256 * (1 + Real.log (K : ℝ)) ^ 2 ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn512 : (512 : ℝ) ≤ n := by
    nlinarith [sq_nonneg (1 + Real.log (K : ℝ) - 5 / 3)]
  have hv0 := Real.log_le_log (by norm_num : (0 : ℝ) < 512) hn512
  have h512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
    have he : (512 : ℝ) = 2 ^ (9 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
  rw [h512] at hv0
  have hv : 6 ≤ Real.log (n : ℝ) := by linarith [Real.log_two_gt_d9]
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  exact threshold_absorption hy hbase

/-- Summed support estimates imply the total relative-error logarithm
bound.  The premises are the distinct elementary support/counting estimates,
not the desired final error estimate. -/
theorem reduction_error_log_bound {h n u initial overhead tensor shortening : ℝ}
    (hu : (15 : ℝ) / 2 ≤ u)
    (hthreshold : u ^ 2 ≤ (25 : ℝ) / 256 * n)
    (hinitial : initial ≤ n * h / 2 + u)
    (hoverhead : overhead ≤ 5 * u)
    (htensor : tensor ≤ n * h + 3 / 4 * u ^ 2 + 2 * u)
    (hshortening : shortening ≤ u ^ 2 + 6 * u) :
    initial + overhead + tensor + shortening < gamma h * n := by
  have ha := error_cost_absorption hu hthreshold
  dsimp [gamma]
  nlinarith

theorem reduction_coefficient_log_bound {h n u overhead tensor shortening : ℝ}
    (hu : (15 : ℝ) / 2 ≤ u)
    (hthreshold : u ^ 2 ≤ (25 : ℝ) / 256 * n)
    (hoverhead : overhead ≤ 5 / 2 * u)
    (htensor : tensor ≤ n * h + 3 / 4 * u ^ 2 + 2 * u)
    (hshortening : shortening ≤ u ^ 2 + 6 * u) :
    overhead + tensor + shortening < n * h + n / 3 := by
  have ha := coefficient_cost_absorption hu hthreshold
  nlinarith

theorem log_one_add_two_mul_le {n : ℝ} (hn : 2 ≤ n) :
    Real.log (1 + 2 * n) ≤ n := by
  have hn0 : 0 ≤ n := by linarith
  have hs := Real.sum_le_exp_of_nonneg hn0 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    pow_one] at hs
  norm_num at hs
  have he : 1 + 2 * n ≤ Real.exp n := by nlinarith
  exact (Real.log_le_iff_le_exp (by linarith : 0 < 1 + 2 * n)).2 he

/-- Exact scalar replacement for the manuscript's monotonicity argument for
`t ↦ t * exp (-n*t)`. -/
theorem zeta_exponential_comparison {n z : ℝ} (hn : 2 ≤ n)
    (hz : (3 : ℝ) / 2 ≤ z) :
    z * Real.exp (-(z * n)) ≤
      (3 : ℝ) / 2 * Real.exp (-(3 / 2 * n)) := by
  have hd : 0 ≤ z - 3 / 2 := by linarith
  have he := Real.add_one_le_exp (n * (z - 3 / 2))
  have hm : z ≤ 3 / 2 * Real.exp (n * (z - 3 / 2)) := by
    nlinarith [mul_nonneg (show 0 ≤ n - 2 by linarith) hd]
  have hmul := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-(z * n))).le
  have heq : Real.exp (n * (z - 3 / 2)) * Real.exp (-(z * n)) =
      Real.exp (-(3 / 2 * n)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, heq] using hmul

/-- The three separate bounds obtained from the Haar estimate imply the
final scalar error estimate.  These hypotheses expose the precise analytic
inputs needed from the operator/random-matrix argument. -/
theorem final_error_from_contributions {n h ε A D R : ℝ}
    (hn : 64 ≤ n) (hh : (2 : ℝ) / 3 ≤ h) (hε : 0 < ε)
    (hA : A / ε ≤ 8 * n * (n + 1) * Real.log (1 + 2 * n) * Real.exp (-n / 2))
    (hD : D / ε ≤ 664 * zeta h * n ^ 3 * (n + 1) * Real.exp (-(zeta h * n)))
    (hR : R / ε ≤ n ^ 2 * Real.exp (-n)) :
    A + D + R ≤ ε / 16 := by
  have hn0 : 0 ≤ n := by linarith
  have hntwo : 2 ≤ n := by linarith
  have hn1 : n + 1 ≤ 3 / 2 * n := by linarith
  have hlog := log_one_add_two_mul_le hntwo
  have hlog0 : 0 ≤ Real.log (1 + 2 * n) := Real.log_nonneg (by linarith)
  have hz : (3 : ℝ) / 2 ≤ zeta h := by dsimp [zeta]; linarith
  have hz0 : 0 ≤ zeta h := by linarith
  have hzexp := zeta_exponential_comparison hntwo hz
  have hA' : A / ε ≤ 12 * n ^ 3 * Real.exp (-n / 2) := by
    have h₁ := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ 8 * n by positivity)
    have h₂ := mul_le_mul h₁ hlog hlog0 (by positivity : 0 ≤ 8 * n * (3 / 2 * n))
    have h₃ := mul_le_mul_of_nonneg_right h₂ (Real.exp_pos (-n / 2)).le
    nlinarith
  have hD' : D / ε ≤ 1494 * n ^ 4 * Real.exp (-3 * n / 2) := by
    have h₁ := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ 664 * n ^ 3 by positivity)
    have h₂ := mul_le_mul h₁ hzexp
      (by positivity : 0 ≤ zeta h * Real.exp (-(zeta h * n)))
      (by positivity : 0 ≤ 664 * n ^ 3 * (3 / 2 * n))
    have heq : -(3 / 2 * n) = -3 * n / 2 := by ring
    rw [heq] at h₂
    nlinarith
  have ht := final_three_tails_lt hn
  dsimp [tailBound] at ht
  have htotal : (A + D + R) / ε < 1 / 16 := by
    rw [add_div, add_div]
    linarith
  have h := (div_lt_iff₀ hε).1 htotal
  linarith

theorem exp_dominates_linear {x : ℝ} (hx : 0 ≤ x) :
    (9 : ℝ) / 2 * x ≤ Real.exp (2 * x) := by
  have he := Real.add_one_le_exp (2 * x - 1)
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos 1).le
  have heq : Real.exp 1 * Real.exp (2 * x - 1) = Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hm
  have hconst := Real.exp_one_gt_d9
  nlinarith

theorem coefficient_remainder_absorption {h n : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 2 ≤ n) :
    Real.log 4 + 2 * n * h + n / 3 ≤
      Real.exp (2 * n * h) * Real.log (1 + 2 * n) := by
  have hn0 : 0 ≤ n := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hnh : (4 : ℝ) / 3 ≤ n * h := by
    nlinarith [mul_nonneg (show 0 ≤ n - 2 by linarith) hh0]
  have hlog4 : Real.log 4 < (7 : ℝ) / 5 := by
    have he : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [he, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlog : 1 ≤ Real.log (1 + 2 * n) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < 1 + 2 * n)).2
    linarith [Real.exp_one_lt_three]
  have habsorb : Real.log 4 + 2 * n * h + n / 3 ≤ 9 / 2 * (n * h) := by
    nlinarith
  have he := exp_dominates_linear (mul_nonneg hn0 hh0)
  have he' : Real.exp (2 * (n * h)) = Real.exp (2 * n * h) := by congr 1; ring
  rw [he'] at he
  have hm := mul_le_mul_of_nonneg_left hlog (Real.exp_pos (2 * n * h)).le
  nlinarith

theorem final_coefficient_size {h n J reductions L : ℝ}
    (hh : (2 : ℝ) / 3 ≤ h) (hn : 2 ≤ n)
    (hJ : J ≤ (Real.exp (2 * n * h) - 1) * Real.log (1 + 2 * n))
    (hred : reductions ≤ n * h + n / 3)
    (hL : L ≤ Real.log 4 + J + n * h + reductions) :
    L ≤ 2 * Real.exp (2 * n * h) * Real.log (1 + 2 * n) := by
  have hr := coefficient_remainder_absorption hh hn
  have hlog0 : 0 ≤ Real.log (1 + 2 * n) := Real.log_nonneg (by linarith)
  nlinarith

theorem tolerance_times_error_factor {h n T : ℝ} (hn : 0 < n)
    (hT : T ≤ Real.exp (gamma h * n)) :
    T * tolerance h n ≤ 1 / n := by
  have he := mul_le_mul_of_nonneg_right hT (tolerance_pos (h := h) hn).le
  have heq : Real.exp (gamma h * n) * tolerance h n = 1 / n := by
    dsimp [tolerance]
    rw [← mul_div_assoc, ← Real.exp_add]
    simp
  exact heq ▸ he

theorem coefficient_error_contribution {h n L invp : ℝ}
    (hn : 0 < n) (_hL0 : 0 ≤ L) (hip0 : 0 ≤ invp)
    (hL : L ≤ 2 * Real.exp (2 * h * n) * Real.log (1 + 2 * n))
    (hip : invp ≤ 4 * Real.exp (-(dimensionExponent h * n / 80))) :
    ((n + 1) * L * invp) / tolerance h n ≤
      8 * n * (n + 1) * Real.log (1 + 2 * n) * Real.exp (-n / 2) := by
  have hlog0 : 0 ≤ Real.log (1 + 2 * n) := Real.log_nonneg (by linarith)
  have hm := mul_le_mul hL hip hip0 (by positivity :
    0 ≤ 2 * Real.exp (2 * h * n) * Real.log (1 + 2 * n))
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ n + 1 by linarith)
  have hexp : Real.exp (2 * h * n) *
      Real.exp (-(dimensionExponent h * n / 80)) =
      Real.exp (-(gamma h * n)) * Real.exp (-n / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [gamma, dimensionExponent]
    ring
  apply (div_le_iff₀ (tolerance_pos hn)).2
  calc
    (n + 1) * L * invp ≤ (n + 1) *
      (2 * Real.exp (2 * h * n) * Real.log (1 + 2 * n) *
        (4 * Real.exp (-(dimensionExponent h * n / 80)))) := by
      simpa only [mul_assoc] using hm'
    _ = 8 * (n + 1) * Real.log (1 + 2 * n) *
      (Real.exp (2 * h * n) * Real.exp (-(dimensionExponent h * n / 80))) := by ring
    _ = (8 * n * (n + 1) * Real.log (1 + 2 * n) * Real.exp (-n / 2)) *
      tolerance h n := by
      rw [hexp]
      dsimp [tolerance]
      field_simp

theorem dimension_error_contribution {h n logN logp invp : ℝ}
    (hh : 0 ≤ h) (hn : 0 < n)
    (_hN0 : 0 ≤ logN) (_hp0 : 0 ≤ logp) (hip0 : 0 ≤ invp)
    (hN : logN ≤ 2 * dimensionExponent h * n)
    (hp : logp ≤ logN / 80)
    (hip : invp ≤ 4 * Real.exp (-(dimensionExponent h * n / 80))) :
    ((n * (n + 1) / 2) * (logN + 3 * logp) * invp) / tolerance h n ≤
      664 * zeta h * n ^ 3 * (n + 1) * Real.exp (-(zeta h * n)) := by
  have hlog : logN + 3 * logp ≤ (83 : ℝ) / 40 * dimensionExponent h * n := by
    linarith
  have hblog : 0 ≤ (83 : ℝ) / 40 * dimensionExponent h * n := by
    dsimp [dimensionExponent]
    positivity
  have hm := mul_le_mul hlog hip hip0 hblog
  have hfactor : 0 ≤ n * (n + 1) / 2 := by positivity
  have hm' := mul_le_mul_of_nonneg_left hm hfactor
  have hb := dimensionExponent_le hh
  have hz0 : 0 ≤ zeta h := by dsimp [zeta]; positivity
  have hexp : Real.exp (-(dimensionExponent h * n / 80)) =
      Real.exp (-(gamma h * n)) * Real.exp (-(zeta h * n)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [dimensionExponent, gamma, zeta]
    ring
  apply (div_le_iff₀ (tolerance_pos hn)).2
  calc
    n * (n + 1) / 2 * (logN + 3 * logp) * invp ≤
      n * (n + 1) / 2 * ((83 : ℝ) / 40 * dimensionExponent h * n *
        (4 * Real.exp (-(dimensionExponent h * n / 80)))) := by
      simpa only [mul_assoc] using hm'
    _ = (83 : ℝ) / 20 * dimensionExponent h * n ^ 2 * (n + 1) *
      Real.exp (-(dimensionExponent h * n / 80)) := by ring
    _ ≤ 664 * zeta h * n ^ 2 * (n + 1) *
      Real.exp (-(dimensionExponent h * n / 80)) := by
      have hm'' := mul_le_mul_of_nonneg_right hb (show 0 ≤
        (83 : ℝ) / 20 * n ^ 2 * (n + 1) *
          Real.exp (-(dimensionExponent h * n / 80)) by positivity)
      nlinarith
    _ = (664 * zeta h * n ^ 3 * (n + 1) * Real.exp (-(zeta h * n))) *
      tolerance h n := by
      rw [hexp]
      dsimp [tolerance]
      field_simp

theorem remainder_error_contribution {h n remainderLog : ℝ}
    (hh : 0 ≤ h) (hn : 0 < n)
    (hR : remainderLog ≤ Real.exp (-(dimensionExponent h * n / 2))) :
    (n * remainderLog) / tolerance h n ≤ n ^ 2 * Real.exp (-n) := by
  have hgap := remainder_exponent_gap hh
  have hgap' := mul_le_mul_of_nonneg_right hgap hn.le
  have he : Real.exp (-(dimensionExponent h * n / 2)) ≤
      Real.exp (-(gamma h * n) - n) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hr := hR.trans he
  have hm := mul_le_mul_of_nonneg_left hr hn.le
  apply (div_le_iff₀ (tolerance_pos hn)).2
  calc
    n * remainderLog ≤ n * Real.exp (-(gamma h * n) - n) := hm
    _ = (n ^ 2 * Real.exp (-n)) * tolerance h n := by
      rw [sub_eq_add_neg, Real.exp_add]
      dsimp [tolerance]
      field_simp

/-- Scalar validation of the complete logarithmic Haar multiplier.  The
premises are the separately stated coefficient-size, moment-size and
dimension estimates derived in the paper. -/
theorem haar_error_bound {h n L logN logp invp remainderLog : ℝ}
    (hh : (2 : ℝ) / 3 ≤ h) (hn : 64 ≤ n)
    (hL0 : 0 ≤ L) (hN0 : 0 ≤ logN) (hp0 : 0 ≤ logp) (hip0 : 0 ≤ invp)
    (hL : L ≤ 2 * Real.exp (2 * h * n) * Real.log (1 + 2 * n))
    (hN : logN ≤ 2 * dimensionExponent h * n)
    (hp : logp ≤ logN / 80)
    (hip : invp ≤ 4 * Real.exp (-(dimensionExponent h * n / 80)))
    (hR : remainderLog ≤ Real.exp (-(dimensionExponent h * n / 2))) :
    (n + 1) * L * invp + (n * (n + 1) / 2) * (logN + 3 * logp) * invp +
        n * remainderLog ≤ tolerance h n / 16 := by
  have hn0 : 0 < n := by linarith
  have hh0 : 0 ≤ h := by linarith
  exact final_error_from_contributions hn hh (tolerance_pos hn0)
    (coefficient_error_contribution hn0 hL0 hip0 hL hip)
    (dimension_error_contribution hh0 hn0 hN0 hp0 hip0 hN hp hip)
    (remainder_error_contribution hh0 hn0 hR)

/-- The logarithm of the multiplicative factor in equation `haar`, with the
paper's explicit choices of `N` and the even moment order `p`. -/
def haarLogMultiplier (h n L : ℝ) : ℝ :=
  (n + 1) * L / (momentParameter h n : ℝ) +
    n * (n + 1) * Real.log (dimensionChoice h n : ℝ) /
      (2 * (momentParameter h n : ℝ)) +
    3 * n * (n + 1) * Real.log (momentParameter h n : ℝ) /
      (2 * (momentParameter h n : ℝ)) +
    n * Real.log (1 + Real.exp (-(Real.log (dimensionChoice h n : ℝ) / 2)))

/-- With explicit ceiling/floor parameters, only the separately proved
coefficient-size estimate remains a premise of the scalar Haar error bound. -/
theorem explicit_haar_error_bound {h n L : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 64 ≤ n) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * Real.exp (2 * h * n) * Real.log (1 + 2 * n)) :
    haarLogMultiplier h n L ≤ tolerance h n / 16 := by
  have hn2 : 2 ≤ n := by linarith
  obtain ⟨_, hp, _, _⟩ := moment_parameter_bounds hh hn2
  have hp1 : (1 : ℝ) ≤ momentParameter h n := by exact_mod_cast (by omega : 1 ≤ momentParameter h n)
  have hp0 : (0 : ℝ) ≤ momentParameter h n := hp1.trans' (by norm_num)
  obtain ⟨hNlo, hNhi⟩ := dimension_choice_log_bounds hh hn2
  have hh0 : 0 ≤ h := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hbn0 : 0 ≤ dimensionExponent h * n := by dsimp [dimensionExponent]; positivity
  have hN0 : 0 ≤ Real.log (dimensionChoice h n : ℝ) := hbn0.trans hNlo
  have hpLog0 : 0 ≤ Real.log (momentParameter h n : ℝ) := Real.log_nonneg hp1
  have hb := haar_error_bound hh hn hL0 hN0 hpLog0 (by positivity :
    (0 : ℝ) ≤ 1 / (momentParameter h n : ℝ)) hL hNhi
    (moment_parameter_log_bound hh hn2)
    (moment_parameter_inverse_bound hh hn2)
    (remainder_log_bound hh hn2)
  convert hb using 1
  dsimp [haarLogMultiplier]
  ring

/-- The final conversion from an additive logarithmic error to the target
multiplicative norm tolerance. -/
theorem final_log_comparison {ε E : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hE : E ≤ ε / 16) : E < Real.log (1 + ε / 2) := by
  have hp : 0 < 1 + ε / 2 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have hrewrite : 1 - (1 + ε / 2)⁻¹ = ε / (2 + ε) := by
    field_simp
    ring
  rw [hrewrite] at hlog
  have hdiv : ε / 3 < ε / (2 + ε) := by
    apply (div_lt_div_iff_of_pos_left hε (by norm_num) (by linarith)).2
    linarith
  linarith

theorem explicit_haar_log_comparison {h n L : ℝ} (hh : (2 : ℝ) / 3 ≤ h)
    (hn : 64 ≤ n) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * Real.exp (2 * h * n) * Real.log (1 + 2 * n)) :
    haarLogMultiplier h n L < Real.log (1 + tolerance h n / 2) := by
  have hn0 : 0 < n := by linarith
  have hn2 : 2 ≤ n := by linarith
  have hh0 : 0 ≤ h := by linarith
  exact final_log_comparison (tolerance_pos hn0) (tolerance_lt_one hh0 hn2)
    (explicit_haar_error_bound hh hn hL0 hL)

/-- The numerical appendix at the paper's stated integer threshold.  Here
`L` denotes `log (2*m_n)`; its displayed bound is the coefficient-size
certificate obtained from the separately formalized reduction arithmetic. -/
theorem quantitative_certificate {K n : ℕ} {L : ℝ} (hK : 2 ≤ K)
    (hn : n₀ K ≤ n) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * (K : ℝ) ^ (2 * n) * Real.log (1 + 2 * (n : ℝ))) :
    Even (momentParameter (Real.log (K : ℝ)) n) ∧
    2 ≤ momentParameter (Real.log (K : ℝ)) n ∧
    haarLogMultiplier (Real.log (K : ℝ)) n L ≤
      tolerance (Real.log (K : ℝ)) n / 16 ∧
    haarLogMultiplier (Real.log (K : ℝ)) n L <
      Real.log (1 + tolerance (Real.log (K : ℝ)) n / 2) := by
  obtain ⟨_, hn64, _, _⟩ := threshold_consequences hK hn
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hKreal
  have hh : (2 : ℝ) / 3 ≤ Real.log (K : ℝ) := by linarith [Real.log_two_gt_d9]
  have hK0 : (0 : ℝ) < K := by linarith
  have hexp : Real.exp (2 * Real.log (K : ℝ) * (n : ℝ)) = (K : ℝ) ^ (2 * n) := by
    have he : 2 * Real.log (K : ℝ) * (n : ℝ) = (2 * n : ℕ) * Real.log (K : ℝ) := by
      push_cast
      ring
    rw [he, Real.exp_nat_mul, Real.exp_log hK0]
  have hL' : L ≤ 2 * Real.exp (2 * Real.log (K : ℝ) * (n : ℝ)) *
      Real.log (1 + 2 * (n : ℝ)) := by simpa only [hexp] using hL
  have hn2 : (2 : ℝ) ≤ n := by linarith
  obtain ⟨heven, hp, _, _⟩ := moment_parameter_bounds hh hn2
  exact ⟨heven, hp, explicit_haar_error_bound hh hn64 hL0 hL',
    explicit_haar_log_comparison hh hn64 hL0 hL'⟩

end

end Nonadditivity.Quantitative
