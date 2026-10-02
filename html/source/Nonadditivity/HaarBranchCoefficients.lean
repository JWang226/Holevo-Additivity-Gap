/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarStationaryCoefficients

/-! # First-letter branches and their actual coefficient bounds

The initial operator is one literal coefficient and its regular shift. Thus
its norm budget is derived from the original operator, not supplied as an
extra estimate. All results allow arbitrary complete Hilbert coefficients.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarNonbacktracking
open scoped BigOperators ENNReal InnerProduct
open RegularCoefficientEnergy NoncommutativeCS
variable {G E J : Type*} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype J]

omit [CompleteSpace E] in
theorem wordCoefficient_regularPolynomial (w : J → G) (hw : Function.Injective w)
    (a : J → E →L[ℂ] E) (j : J) :
    wordCoefficient (MatrixRegularRestriction.coefficientPolynomial w a) (w j) = a j := by
  classical
  ext x
  simp only [wordCoefficient_apply, MatrixRegularRestriction.coefficientPolynomial_apply,
    vacuum_apply, lp.single_apply, Pi.single_apply, inv_mul_eq_one, hw.eq_iff]
  simp only [apply_ite, map_zero]
  simp

/-- The first-letter term of a stationary operator. -/
def firstLetter (A : H G E →L[ℂ] H G E) (g : G) : H G E →L[ℂ] H G E :=
  liftOperator (wordCoefficient A g) ∘L MatrixRegularRestriction.leftRegular g

theorem firstLetter_norm_le (A : H G E →L[ℂ] H G E) (g : G) :
    ‖firstLetter A g‖ ≤ ‖A‖ := by
  have hc : ‖wordCoefficient A g‖ ≤ ‖A‖ := by
    simpa only [killed, pow_zero, one_mul] using killed_wordCoefficient_norm_le A A 0 g
  have hs : ‖MatrixRegularRestriction.leftRegular (E := E) g‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  calc
    _ ≤ ‖liftOperator (G := G) (wordCoefficient A g)‖ *
        ‖MatrixRegularRestriction.leftRegular (E := E) g‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * 1 := mul_le_mul ((lift_norm_le _).trans hc) hs (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

omit [CompleteSpace E] in
theorem stationary_firstLetter (A : H G E →L[ℂ] H G E) (g : G) :
    IsStationary (firstLetter A g) := by
  have hs : IsStationary (MatrixRegularRestriction.leftRegular (E := E) g) := by
    intro h
    ext x z
    simp only [ContinuousLinearMap.comp_apply, MatrixRegularRestriction.leftRegular_apply,
      rightShift_apply, mul_assoc]
  exact (stationary_lift _).mul hs

/-- The non-returning branch of total time `r+1`, starting with letter `g`. -/
def branch (A : H G E →L[ℂ] H G E) (g : G) (r : ℕ) :=
  killed A (firstLetter A g) r

theorem branch_word_norm_le (A : H G E →L[ℂ] H G E) (g : G) (r : ℕ) (v : G) :
    ‖wordCoefficient (branch A g r) v‖ ≤ ‖A‖^(r+1) := by
  apply (killed_wordCoefficient_norm_le A (firstLetter A g) r v).trans
  simpa only [pow_succ] using
    mul_le_mul_of_nonneg_left (firstLetter_norm_le A g) (pow_nonneg (norm_nonneg A) r)

theorem branch_column_norm_le (A : H G E →L[ℂ] H G E) (g : G) (r : ℕ)
    (w : J → G) (hw : Function.Injective w) :
    ‖column (fun j => wordCoefficient (branch A g r) (w j))‖ ≤ ‖A‖^(r+1) := by
  apply (killed_coefficient_column_norm_le A (firstLetter A g) r w hw).trans
  simpa only [pow_succ] using
    mul_le_mul_of_nonneg_left (firstLetter_norm_le A g) (pow_nonneg (norm_nonneg A) r)

theorem branch_row_norm_le {A : H G E →L[ℂ] H G E} (hA : IsStationary A)
    (g : G) (r : ℕ) (w : J → G) (hw : Function.Injective w) :
    ‖row (fun j => wordCoefficient (branch A g r) (w j))‖ ≤
      (r+1:ℕ) * ‖A‖^(r+1) := by
  apply (killed_coefficient_row_norm_le hA (stationary_firstLetter A g) r w hw).trans
  have h := mul_le_mul_of_nonneg_left (firstLetter_norm_le A g)
    (by positivity : 0 ≤ (r+1:ℕ) * ‖A‖^r)
  simpa only [pow_succ, mul_assoc] using h

/-- A chain visited only once incurs exactly a square root of its number of
allowed words; no coefficient-space dimension enters the bound. -/
theorem branch_singleton_norm_le (A : H G E →L[ℂ] H G E) (g : G) (r : ℕ)
    (w : J → G) (hw : Function.Injective w) :
    ‖∑ j, wordCoefficient (branch A g r) (w j)‖ ≤
      Real.sqrt (Fintype.card J : ℝ) * ‖A‖^(r+1) := by
  have hb := HaarCoefficientBounds.singleton_sum_norm_le
    (fun j => wordCoefficient (branch A g r) (w j))
  rw [← HaarCoefficientBounds.column_norm_sq, Real.sqrt_sq (norm_nonneg (column (fun j => wordCoefficient (branch A g r) (w j))))] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (branch_column_norm_le A g r w hw)
    (Real.sqrt_nonneg _))

end Nonadditivity.HaarNonbacktracking
