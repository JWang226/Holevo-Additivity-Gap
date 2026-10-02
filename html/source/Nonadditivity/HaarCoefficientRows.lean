/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoefficientBounds

/-! # Row energy for actual regular operator coefficients

The adjoint polynomial at the vacuum has coefficients `Aᵢ*` at words `wᵢ⁻¹`.
Consequently both row and column Gram factors in the path contraction theorem
are bounded by the same genuine regular norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarCoefficientBounds

open scoped BigOperators ENNReal InnerProduct
open Nonadditivity.NoncommutativeCS

variable {E G I : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Group G] [DecidableEq G] [Fintype I]

/-- The adjoint-vacuum identity holds for arbitrary bounded operator coefficients. -/
theorem polynomial_adjoint_single (w : I → G) (A : I → E →L[ℂ] E) (x : E) :
    (MatrixRegularRestriction.coefficientPolynomial w A).adjoint (lp.single 2 (1 : G) x) =
      ∑ i, lp.single 2 ((w i)⁻¹) ((A i).adjoint x) := by
  apply ext_inner_right ℂ
  intro f
  simp only [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left,
    MatrixRegularRestriction.coefficientPolynomial_apply, mul_one, inner_sum,
    sum_inner]

theorem regular_adjoint_coefficient_energy_le (w : I → G) (hw : Function.Injective w)
    (A : I → E →L[ℂ] E) (x : E) :
    ∑ i, ‖(A i).adjoint x‖ ^ 2 ≤
      ‖MatrixRegularRestriction.coefficientPolynomial w A‖ ^ 2 * ‖x‖ ^ 2 := by
  classical
  have hinv : Function.Injective (fun i => (w i)⁻¹) := fun i j h => hw (inv_injective h)
  have h := (MatrixRegularRestriction.coefficientPolynomial w A).adjoint.le_opNorm
    (lp.single 2 (1 : G) x)
  rw [polynomial_adjoint_single, lp.norm_single (by norm_num), LinearIsometryEquiv.norm_map] at h
  have hs : ‖(∑ i, lp.single 2 ((w i)⁻¹) ((A i).adjoint x) :
      RegularCoefficientEnergy.VectorHilbert G E)‖ ^ 2 = ∑ i, ‖(A i).adjoint x‖ ^ 2 := by
    have hh := lp.norm_sum_single (p := 2) (by norm_num)
      (Function.extend (fun i => (w i)⁻¹) (fun i => (A i).adjoint x) 0)
      (Finset.univ.image (fun i => (w i)⁻¹))
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_image hinv.injOn,
      hinv.extend_apply] using hh
  simpa only [hs, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

theorem regular_row_norm_le (w : I → G) (hw : Function.Injective w)
    (A : I → E →L[ℂ] E) :
    ‖row A‖ ≤ ‖MatrixRegularRestriction.coefficientPolynomial w A‖ := by
  rw [row, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound (column (fun i => (A i).adjoint))
    (norm_nonneg (MatrixRegularRestriction.coefficientPolynomial w A))
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow]
  exact regular_adjoint_coefficient_energy_le w hw A x

theorem row_norm_sq (A : I → E →L[ℂ] E) : ‖row A‖ ^ 2 = ‖rowGram A‖ := by
  simpa only [row, LinearIsometryEquiv.norm_map, columnGram, rowGram,
    ContinuousLinearMap.adjoint_adjoint] using column_norm_sq (fun i => (A i).adjoint)

theorem regular_rowGram_norm_le (w : I → G) (hw : Function.Injective w)
    (A : I → E →L[ℂ] E) :
    ‖rowGram A‖ ≤ ‖MatrixRegularRestriction.coefficientPolynomial w A‖ ^ 2 := by
  rw [← row_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg (row A)) (regular_row_norm_le w hw A) 2

end Nonadditivity.HaarCoefficientBounds
