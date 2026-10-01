/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarOperatorPolynomial

/-! # Sharp row and column factors for actual operator-word coefficients

Restricting to any finite injective family of group words costs no coefficient
space dimension. Applied to first-step non-returning polynomials, these are
the marked endpoint factors in the high-moment path argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarOperatorPolynomial

open scoped BigOperators ENNReal InnerProduct
open HaarNonbacktracking RegularCoefficientEnergy NoncommutativeCS

variable {G E I : Type*} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype I]

omit [DecidableEq G] [CompleteSpace E] in
/-- The regular evaluation is the literal finite-support coefficient polynomial. -/
theorem regular_eq_supportPolynomial (f : Polynomial G E) :
    regular f = MatrixRegularRestriction.coefficientPolynomial
      (fun g : f.support => (g : G)) (fun g => f g) := by
  rw [regular_eq_sum, MatrixRegularRestriction.coefficientPolynomial]
  exact (Finset.sum_attach f.support
    (fun g => liftOperator (f g) * MatrixRegularRestriction.leftRegular g)).symm

/-- The adjoint vacuum coefficient is the adjoint of the inverse-word coefficient. -/
theorem regular_adjoint_vacuum (f : Polynomial G E) (x : E) (g : G) :
    (regular f).adjoint (vacuum x) g = (f g⁻¹).adjoint x := by
  rw [regular_eq_supportPolynomial, vacuum_apply,
    HaarCoefficientBounds.polynomial_adjoint_single]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  rw [show (∑ a : f.support, if g = (a : G)⁻¹ then (f a).adjoint x else 0) =
      ∑ a ∈ f.support, if g = a⁻¹ then (f a).adjoint x else 0 from
    Finset.sum_coe_sort f.support (fun a : G => if g = a⁻¹ then (f a).adjoint x else 0)]
  have he (a : G) : g = a⁻¹ ↔ g⁻¹ = a := by
    constructor
    · intro h; rw [h, inv_inv]
    · intro h; rw [← h, inv_inv]
  simp only [he]
  by_cases hg : g⁻¹ ∈ f.support
  · exact Finset.sum_ite_eq_of_mem _ _ _ hg
  · have hz : f g⁻¹ = 0 := Finsupp.notMem_support_iff.mp hg
    rw [hz, map_zero, ContinuousLinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : g⁻¹ ≠ a := by intro h; exact hg (h.symm ▸ ha)
    simp [hne]

/-- Arbitrary finite coefficient columns are bounded by the genuine regular norm. -/
theorem coefficient_energy_le (f : Polynomial G E) (w : I → G)
    (hw : Function.Injective w) (x : E) :
    ∑ i, ‖f (w i) x‖ ^ 2 ≤ ‖regular f‖ ^ 2 * ‖x‖ ^ 2 := by
  classical
  have h := lp.sum_rpow_le_norm_rpow (by norm_num)
    (regular f (vacuum x)) (Finset.univ.image w)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_image hw.injOn,
    regular_vacuum] at h
  have hnorm := (regular f).le_opNorm (vacuum (G := G) x)
  rw [vacuum_apply, lp.norm_single (by norm_num)] at hnorm
  exact h.trans (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2)

/-- The same bound holds for coefficient rows, via the actual adjoint evaluation. -/
theorem adjoint_coefficient_energy_le (f : Polynomial G E) (w : I → G)
    (hw : Function.Injective w) (x : E) :
    ∑ i, ‖(f (w i)).adjoint x‖ ^ 2 ≤ ‖regular f‖ ^ 2 * ‖x‖ ^ 2 := by
  classical
  have hinv : Function.Injective (fun i => (w i)⁻¹) := fun i j h => hw (inv_injective h)
  have h := lp.sum_rpow_le_norm_rpow (by norm_num)
    ((regular f).adjoint (vacuum x)) (Finset.univ.image (fun i => (w i)⁻¹))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_image hinv.injOn,
    regular_adjoint_vacuum, inv_inv] at h
  have hnorm := (regular f).adjoint.le_opNorm (vacuum (G := G) x)
  rw [vacuum_apply, lp.norm_single (by norm_num), LinearIsometryEquiv.norm_map] at hnorm
  exact h.trans (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2)

theorem coefficient_column_norm_le (f : Polynomial G E) (w : I → G)
    (hw : Function.Injective w) : ‖column (fun i => f (w i))‖ ≤ ‖regular f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow]
  exact coefficient_energy_le f w hw x

theorem coefficient_row_norm_le (f : Polynomial G E) (w : I → G)
    (hw : Function.Injective w) : ‖row (fun i => f (w i))‖ ≤ ‖regular f‖ := by
  rw [row, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow]
  exact adjoint_coefficient_energy_le f w hw x

theorem coefficient_columnGram_le (f : Polynomial G E) (w : I → G)
    (hw : Function.Injective w) : ‖columnGram (fun i => f (w i))‖ ≤ ‖regular f‖ ^ 2 := by
  rw [← HaarCoefficientBounds.column_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg (column (fun i => f (w i)))) (coefficient_column_norm_le f w hw) 2

theorem coefficient_rowGram_le (f : Polynomial G E) (w : I → G)
    (hw : Function.Injective w) : ‖rowGram (fun i => f (w i))‖ ≤ ‖regular f‖ ^ 2 := by
  rw [← HaarCoefficientBounds.row_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg (row (fun i => f (w i)))) (coefficient_row_norm_le f w hw) 2

/-- Both marked endpoint Gram factors are bounded by the linear first-step loss. -/
theorem firstStep_endpoint_bounds (A : Polynomial G E) (a : G) (n : ℕ)
    (w : I → G) (hw : Function.Injective w) :
    Real.sqrt ‖columnGram (fun i => firstStep A a n (w i))‖ ≤
        (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) ∧
    Real.sqrt ‖rowGram (fun i => firstStep A a n (w i))‖ ≤
        (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) := by
  constructor
  · exact (Real.sqrt_le_sqrt (coefficient_columnGram_le (firstStep A a n) w hw)).trans
      (by rw [Real.sqrt_sq (norm_nonneg _)]; exact firstStep_norm_le _ _ _)
  · exact (Real.sqrt_le_sqrt (coefficient_rowGram_le (firstStep A a n) w hw)).trans
      (by rw [Real.sqrt_sq (norm_nonneg _)]; exact firstStep_norm_le _ _ _)

/-- A singly occurring profile family costs only the square root of its size. -/
theorem firstStep_singleton_bound (A : Polynomial G E) (a : G) (n : ℕ)
    (w : I → G) (hw : Function.Injective w) :
    ‖∑ i, firstStep A a n (w i)‖ ≤ Real.sqrt (Fintype.card I : ℝ) *
      ((n + 1 : ℕ) * ‖regular A‖ ^ (n + 1)) := by
  exact (HaarCoefficientBounds.singleton_sum_norm_le _).trans
    (mul_le_mul_of_nonneg_left (firstStep_endpoint_bounds A a n w hw).1 (Real.sqrt_nonneg _))

end Nonadditivity.HaarOperatorPolynomial
