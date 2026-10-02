/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMomentSlack
import Nonadditivity.HaarTensorConstants

/-! # Explicit slack for corrected two-generator path encoding

The actual prescribed moment order satisfies the stronger dimension condition
`2^80*p^80 ≤ N`. It absorbs a factor `128` per important event and the extra
three powers of path length from the corrected event count. The combinatorial
encoding itself remains a separate theorem.
-/
noncomputable section
namespace Nonadditivity.HaarMomentConstants
open scoped BigOperators

theorem prescribed_dimension_strong {h n : ℝ}
    (hh : (2:ℝ)/3 ≤ h) (hn : 2 ≤ n) :
    2^80 * (Quantitative.momentParameter h n:ℝ)^80 ≤
      (Quantitative.dimensionChoice h n:ℝ) := by
  obtain ⟨_,_,_,hp⟩ := Quantitative.moment_parameter_bounds hh hn
  have hD : 0 < (Quantitative.dimensionChoice h n:ℝ) :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have htwop : 2*(Quantitative.momentParameter h n:ℝ) ≤
      Real.exp (Real.log (Quantitative.dimensionChoice h n:ℝ)/80) := by linarith
  have he : (Real.exp (Real.log (Quantitative.dimensionChoice h n:ℝ)/80))^80 =
      (Quantitative.dimensionChoice h n:ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (80:ℝ)*(Real.log (Quantitative.dimensionChoice h n:ℝ)/80) =
      Real.log (Quantitative.dimensionChoice h n:ℝ) by ring, Real.exp_log hD]
  rw [← mul_pow]
  exact he ▸ pow_le_pow_left₀ (by positivity) htwop 80

theorem strong_implies_dimension {p N : ℝ} (hN : 2^80*p^80 ≤ N) :
    2^32*p^80 ≤ N := by
  exact (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)^32 ≤ 2^80)
    (by positivity)).trans hN

theorem strong_fourth_root_lower {p N : ℝ} (hp : 2 ≤ p) (hN : 2^80*p^80 ≤ N) :
    2^20*p^20 ≤ N^(1/4:ℝ) := by
  have hN0 := (dimension_pos hp (strong_implies_dimension hN)).le
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (Real.rpow_nonneg hN0 _)
  have he : (N^(1/4:ℝ))^4=N := by
    simpa using Real.rpow_inv_natCast_pow hN0 (by norm_num : (4:ℕ) ≠ 0)
  rw [he]
  convert hN using 1; ring

theorem strong_square_root_lower {p N : ℝ} (hp : 2 ≤ p) (hN : 2^80*p^80 ≤ N) :
    2^40*p^40 ≤ N^(1/2:ℝ) := by
  have hN0 := (dimension_pos hp (strong_implies_dimension hN)).le
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.rpow_nonneg hN0 _)
  have he : (N^(1/2:ℝ))^2=N := by
    simpa using Real.rpow_inv_natCast_pow hN0 (by norm_num : (2:ℕ) ≠ 0)
  rw [he]
  convert hN using 1; ring

theorem encoding_alpha_le {p N : ℝ} (hp : 2 ≤ p) (hN : 2^80*p^80 ≤ N) :
    128*alpha p N ≤ 1/2 := by
  have hN0 := dimension_pos hp (strong_implies_dimension hN)
  have hr := strong_fourth_root_lower hp hN
  unfold alpha
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)).mpr
  norm_num at hr
  nlinarith [show 0 ≤ p^20 by positivity]

theorem encoding_beta_le {p N : ℝ} (hp : 2 ≤ p) (hN : 2^80*p^80 ≤ N) :
    16384*beta p N ≤ 1/2 := by
  have hN0 := dimension_pos hp (strong_implies_dimension hN)
  have hpow : p^38 ≤ p^80 := pow_le_pow_right₀ (by linarith) (by norm_num)
  unfold beta
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hN0).mpr
  norm_num at hN
  nlinarith [show 0 ≤ p^80 by positivity]

def encodingMajorant (p N t : ℝ) (a b : ℕ) : ℝ :=
  16384*t^3 * ((25/4)*(4*t^3)^4*p^11/N * Real.exp (t^2/N^(1/4:ℝ)) *
    (∑ i ∈ Finset.range a, (128*alpha p N)^i) *
    (∑ i ∈ Finset.range b, (16384*beta p N)^i))

theorem encodingMajorant_le {p N t : ℝ} (hp : 2 ≤ p) (hN : 2^80*p^80 ≤ N)
    (ht0 : 0 ≤ t) (ht : t ≤ p) (a b : ℕ) :
    encodingMajorant p N t a b ≤ 16384*6400*Real.exp 1*p^11/N*t^15 := by
  have hNc := strong_implies_dimension hN
  have hN0 := dimension_pos hp hNc
  have ha0 := (alpha_bounds hp hNc).1
  have hb0 := (beta_bounds hp hNc).1
  have ha := geometric_sum_bound (show 0 ≤ 128*alpha p N by positivity)
    (encoding_alpha_le hp hN) a
  have hb := geometric_sum_bound (show 0 ≤ 16384*beta p N by positivity)
    (encoding_beta_le hp hN) b
  have he := exponential_bound hp hNc ht0 ht
  unfold encodingMajorant
  calc
    _ ≤ 16384*t^3 * ((25/4)*(4*t^3)^4*p^11/N * Real.exp 1 * 2 * 2) := by gcongr
    _ = _ := by ring

theorem encoding_final_error_le {p N : ℝ} (hp : 2 ≤ p) (hN : 2^80*p^80 ≤ N) :
    16384*6400*Real.exp 1*p^27/N ≤ N^(-(1/2:ℝ)) := by
  have hN0 := dimension_pos hp (strong_implies_dimension hN)
  have hs := strong_square_root_lower hp hN
  have hpow : p^27 ≤ p^40 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have he := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
    (show 0 ≤ p^27 by positivity)
  have hsmall : 16384*6400*Real.exp 1*p^27 ≤ N^(1/2:ℝ) := by
    norm_num at hs
    nlinarith [show 0 ≤ p^27 by positivity]
  have hroot : N^(1/2:ℝ)*N^(1/2:ℝ)=N := by rw [← Real.rpow_add hN0]; norm_num
  rw [Real.rpow_neg hN0.le, ← one_div]
  apply (div_le_div_iff₀ hN0 (Real.rpow_pos_of_pos hN0 _)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hN0.le (1/2:ℝ))]


/-- Finite summation of corrected encoding contributions preserves the exact
one-pair target error. The path-length estimates remain explicit premises. -/
theorem sum_encoding_errors_le {p : ℕ} {N ρ : ℝ}
    (hp : 2 ≤ p) (hN : 2^80*(p:ℝ)^80 ≤ N) (hρ : 0 ≤ ρ)
    (D : ℕ → ℝ) (a b : ℕ → ℕ)
    (hD : ∀ t ∈ Finset.Icc 1 p,
      |D t| ≤ encodingMajorant p N t (a t) (b t) * ρ^p) :
    |∑ t ∈ Finset.Icc 1 p, D t| ≤ N^(-(1/2:ℝ))*ρ^p := by
  have hpr : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hN0 := dimension_pos hpr (strong_implies_dimension hN)
  have hpoint : ∀ t ∈ Finset.Icc 1 p,
      |D t| ≤ (16384*6400*Real.exp 1*(p:ℝ)^11/N*(t:ℝ)^15)*ρ^p := by
    intro t ht
    exact (hD t ht).trans (mul_le_mul_of_nonneg_right
      (encodingMajorant_le hpr hN (by positivity)
        (by exact_mod_cast (Finset.mem_Icc.mp ht).2) (a t) (b t)) (pow_nonneg hρ p))
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 p, |D t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 p,
        (16384*6400*Real.exp 1*(p:ℝ)^11/N*(t:ℝ)^15)*ρ^p := Finset.sum_le_sum hpoint
    _ = (16384*6400*Real.exp 1*(p:ℝ)^11/N*
        (∑ t ∈ Finset.Icc 1 p, (t:ℝ)^15))*ρ^p := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (16384*6400*Real.exp 1*(p:ℝ)^11/N*(p:ℝ)^16)*ρ^p := by
      gcongr
      exact length_sum_bound_with_overhead p 3
    _ = (16384*6400*Real.exp 1*(p:ℝ)^27/N)*ρ^p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (encoding_final_error_le hpr hN) (pow_nonneg hρ p)

end Nonadditivity.HaarMomentConstants
