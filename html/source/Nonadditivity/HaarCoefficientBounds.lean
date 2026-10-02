/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCS
import Nonadditivity.MatrixRegularRestriction

/-! # Coefficient bounds for the high-moment path method

All coefficients here act on an arbitrary complete Hilbert space. Evaluation
at the group identity proves the regular-polynomial energy bound directly,
so already-free tensor factors are permitted in the coefficient algebra.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarCoefficientBounds

open scoped BigOperators ENNReal InnerProduct
open Nonadditivity.NoncommutativeCS

variable {E G I : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Group G] [DecidableEq G] [Fintype I]

theorem column_adjoint_comp_column (A : I → E →L[ℂ] E) :
    (column A).adjoint ∘L column A = columnGram A := by
  have hadj : (column A).adjoint = row (fun i => (A i).adjoint) := by
    simp only [row, ContinuousLinearMap.adjoint_adjoint]
  rw [hadj]
  ext x
  simp [columnGram]

theorem column_norm_sq (A : I → E →L[ℂ] E) : ‖column A‖ ^ 2 = ‖columnGram A‖ := by
  rw [← column_adjoint_comp_column, ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- A singleton path factor uses only a square root of its number of colors. -/
theorem singleton_sum_norm_le (A : I → E →L[ℂ] E) :
    ‖∑ i, A i‖ ≤ Real.sqrt (Fintype.card I : ℝ) * Real.sqrt ‖columnGram A‖ := by
  exact Linearization.operator_sum_norm_le_of_gram_norm Finset.univ A
    (Real.sqrt ‖columnGram A‖) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (norm_nonneg _)]; exact le_rfl)

omit [CompleteSpace E] in
private theorem polynomial_single (w : I → G) (A : I → E →L[ℂ] E) (x : E) :
    MatrixRegularRestriction.coefficientPolynomial w A (lp.single 2 (1 : G) x) =
      ∑ i, lp.single 2 (w i) (A i x) := by
  ext g
  simp only [MatrixRegularRestriction.coefficientPolynomial_apply, lp.coeFn_sum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : (w i)⁻¹ * g = 1 ↔ g = w i := by
    rw [inv_mul_eq_one]
    exact eq_comm
  simp only [lp.single_apply, Pi.single_apply, heq]
  split_ifs <;> simp

omit [CompleteSpace E] in
/-- Distinct regular words isolate the coefficient energies in orthogonal
coordinates, for arbitrary bounded operator coefficients. -/
theorem regular_coefficient_energy_le (w : I → G) (hw : Function.Injective w)
    (A : I → E →L[ℂ] E) (x : E) :
    ∑ i, ‖A i x‖ ^ 2 ≤
      ‖MatrixRegularRestriction.coefficientPolynomial w A‖ ^ 2 * ‖x‖ ^ 2 := by
  classical
  have h := (MatrixRegularRestriction.coefficientPolynomial w A).le_opNorm
    (lp.single 2 (1 : G) x)
  rw [polynomial_single, lp.norm_single (by norm_num)] at h
  have hs : ‖(∑ i, lp.single 2 (w i) (A i x) : RegularCoefficientEnergy.VectorHilbert G E)‖ ^ 2 =
      ∑ i, ‖A i x‖ ^ 2 := by
    have hh := lp.norm_sum_single (p := 2) (by norm_num)
      (Function.extend w (fun i => A i x) 0) (Finset.univ.image w)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_image hw.injOn,
      hw.extend_apply] using hh
  simpa only [hs, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The column amplification is bounded by the genuine regular polynomial. -/
theorem regular_column_norm_le (w : I → G) (hw : Function.Injective w)
    (A : I → E →L[ℂ] E) :
    ‖column A‖ ≤ ‖MatrixRegularRestriction.coefficientPolynomial w A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (column A)
    (norm_nonneg (MatrixRegularRestriction.coefficientPolynomial w A))
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow]
  exact regular_coefficient_energy_le w hw A x

/-- The Gram bound is unconditional and remains valid with already-free
operator coefficients. -/
theorem regular_columnGram_norm_le (w : I → G) (hw : Function.Injective w)
    (A : I → E →L[ℂ] E) :
    ‖columnGram A‖ ≤ ‖MatrixRegularRestriction.coefficientPolynomial w A‖ ^ 2 := by
  rw [← column_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg (column A)) (regular_column_norm_le w hw A) 2

end Nonadditivity.HaarCoefficientBounds
