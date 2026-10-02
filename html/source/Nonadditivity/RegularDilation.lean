/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularCoefficientEnergy
import Nonadditivity.MatrixRegularRestriction

/-! # Hermitian dilation of literal matrix-valued regular polynomials

The inverse-transpose coefficients implement the actual Hilbert adjoint.
Orthogonal coordinate slices then give the norm of the doubled polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularDilation

open RegularCoefficientEnergy
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

omit [DecidableEq G] in
theorem regularPolynomial_apply (S : Finset G) (a : G → Matrix ι ι ℂ)
    (f : Hilbert G ι) (h : G) :
    regularPolynomial S a f h = ∑ w ∈ S, coefficientOperator (a w) (f (w⁻¹ * h)) := by
  rw [MatrixRegularRestriction.matrixPolynomial_eq]
  rw [MatrixRegularRestriction.coefficientPolynomial_apply]
  exact Finset.sum_coe_sort S (fun w => coefficientOperator (a w) (f (w⁻¹ * h)))

theorem regularPolynomial_single (S : Finset G) (a : G → Matrix ι ι ℂ)
    (h : G) (x : CoefficientSpace ι) :
    regularPolynomial S a (lp.single 2 h x) =
      ∑ w ∈ S, lp.single 2 (w * h) (coefficientOperator (a w) x) := by
  simp only [regularPolynomial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    leftRegular_single, liftOperator_single]

theorem coefficientOperator_conjTranspose (A : Matrix ι ι ℂ) :
    coefficientOperator A.conjTranspose = (coefficientOperator A).adjoint := by
  unfold coefficientOperator
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]

/-- Testing the actual adjoint against one group coordinate identifies all
its inverse-transpose coefficients. -/
theorem adjoint_regularPolynomial_single (S : Finset G) (a : G → Matrix ι ι ℂ)
    (h : G) (x : CoefficientSpace ι) :
    (regularPolynomial S a).adjoint (lp.single 2 h x) =
      ∑ w ∈ S, lp.single 2 (w⁻¹ * h) (coefficientOperator (a w).conjTranspose x) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left,
    regularPolynomial_apply]
  simp only [inner_sum, sum_inner, lp.inner_single_left,
    coefficientOperator_conjTranspose, ContinuousLinearMap.adjoint_inner_left]

theorem image_inv_eq (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S) :
    S.image Inv.inv = S := by
  ext w
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hS v hv
  · intro hw
    exact ⟨w⁻¹, hS w hw, inv_inv w⟩

/-- On an inversion-closed support, inverse-transpose coefficients give
precisely the Hilbert adjoint of the original regular polynomial. -/
theorem inverse_transpose_polynomial (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S)
    (a : G → Matrix ι ι ℂ) :
    regularPolynomial S (fun w => (a w⁻¹).conjTranspose) =
      (regularPolynomial S a).adjoint := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro h
  apply ContinuousLinearMap.ext
  intro x
  change regularPolynomial S (fun w => (a w⁻¹).conjTranspose) (lp.single 2 h x) =
    (regularPolynomial S a).adjoint (lp.single 2 h x)
  rw [regularPolynomial_single, adjoint_regularPolynomial_single]
  conv_lhs => rw [← image_inv_eq S hS]
  rw [Finset.sum_image inv_injective.injOn]
  simp only [inv_inv]

def fiberLeft (x : CoefficientSpace (Sum ι ι)) : CoefficientSpace ι :=
  WithLp.toLp 2 (fun i => x (Sum.inl i))

def fiberRight (x : CoefficientSpace (Sum ι ι)) : CoefficientSpace ι :=
  WithLp.toLp 2 (fun i => x (Sum.inr i))

omit [DecidableEq ι] in
@[simp] theorem fiberLeft_apply (x : CoefficientSpace (Sum ι ι)) (i : ι) :
    fiberLeft x i = x (Sum.inl i) := rfl

omit [DecidableEq ι] in
@[simp] theorem fiberRight_apply (x : CoefficientSpace (Sum ι ι)) (i : ι) :
    fiberRight x i = x (Sum.inr i) := rfl

omit [DecidableEq ι] in
theorem fiber_energy (x : CoefficientSpace (Sum ι ι)) :
    ‖x‖ ^ 2 = ‖fiberLeft x‖ ^ 2 + ‖fiberRight x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, fiberLeft_apply, fiberRight_apply]
  exact Fintype.sum_sum_type (fun i => ‖x i‖ ^ 2)

def leftSlice (f : Hilbert G (Sum ι ι)) : Hilbert G ι :=
  ⟨fun g => fiberLeft (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => ?_)
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        f.property.summable (by norm_num))
    nlinarith [fiber_energy (f g), sq_nonneg ‖fiberRight (f g)‖]⟩

def rightSlice (f : Hilbert G (Sum ι ι)) : Hilbert G ι :=
  ⟨fun g => fiberRight (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => ?_)
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        f.property.summable (by norm_num))
    nlinarith [fiber_energy (f g), sq_nonneg ‖fiberLeft (f g)‖]⟩

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem leftSlice_apply (f : Hilbert G (Sum ι ι)) (g : G) (i : ι) :
    leftSlice f g i = f g (Sum.inl i) := rfl

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem rightSlice_apply (f : Hilbert G (Sum ι ι)) (g : G) (i : ι) :
    rightSlice f g i = f g (Sum.inr i) := rfl

omit [Group G] [DecidableEq G] [DecidableEq ι] in
/-- The original regular Hilbert norm splits into the two orthogonal blocks. -/
theorem slice_energy (f : Hilbert G (Sum ι ι)) :
    ‖f‖ ^ 2 = ‖leftSlice f‖ ^ 2 + ‖rightSlice f‖ ^ 2 := by
  rw [MatrixRegularRestriction.norm_sq, MatrixRegularRestriction.norm_sq,
    MatrixRegularRestriction.norm_sq]
  change (∑' g, ‖f g‖ ^ 2) =
    (∑' g, ‖fiberLeft (f g)‖ ^ 2) + (∑' g, ‖fiberRight (f g)‖ ^ 2)
  simp_rw [fiber_energy]
  apply Summable.tsum_add
  · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (leftSlice f).property.summable (by norm_num)
  · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (rightSlice f).property.summable (by norm_num)

def fiberEmbedRight (x : CoefficientSpace ι) : CoefficientSpace (Sum ι ι) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => x i))

omit [DecidableEq ι] in
@[simp] theorem fiberLeft_embedRight (x : CoefficientSpace ι) :
    fiberLeft (fiberEmbedRight x) = 0 := by ext i; rfl

omit [DecidableEq ι] in
@[simp] theorem fiberRight_embedRight (x : CoefficientSpace ι) :
    fiberRight (fiberEmbedRight x) = x := by ext i; rfl

omit [DecidableEq ι] in
theorem fiberEmbedRight_norm (x : CoefficientSpace ι) : ‖fiberEmbedRight x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [fiber_energy]
  simp

def embedRight (f : Hilbert G ι) : Hilbert G (Sum ι ι) :=
  ⟨fun g => fiberEmbedRight (f g), by
    apply memℓp_gen
    simp only [fiberEmbedRight_norm]
    exact f.property.summable (by norm_num)⟩

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem leftSlice_embedRight (f : Hilbert G ι) : leftSlice (embedRight f) = 0 := by
  ext g i
  rfl

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem rightSlice_embedRight (f : Hilbert G ι) : rightSlice (embedRight f) = f := by
  ext g i
  rfl

omit [Group G] [DecidableEq G] [DecidableEq ι] in
theorem embedRight_norm (f : Hilbert G ι) : ‖embedRight f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [slice_energy]
  simp

/-- The literal inverse-transpose coefficient dilation. -/
def dilationCoefficient (a : G → Matrix ι ι ℂ) (w : G) : Matrix (Sum ι ι) (Sum ι ι) ℂ :=
  Matrix.fromBlocks 0 (a w) (a w⁻¹).conjTranspose 0

omit [DecidableEq G] in
theorem fiberLeft_dilationCoefficient (a : G → Matrix ι ι ℂ) (w : G)
    (x : CoefficientSpace (Sum ι ι)) :
    fiberLeft (coefficientOperator (dilationCoefficient a w) x) =
      coefficientOperator (a w) (fiberRight x) := by
  ext i
  change ((dilationCoefficient a w) *ᵥ x.ofLp) (Sum.inl i) =
    ((a w) *ᵥ (fiberRight x).ofLp) i
  simp only [dilationCoefficient, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, fiberRight_apply]

omit [DecidableEq G] in
theorem fiberRight_dilationCoefficient (a : G → Matrix ι ι ℂ) (w : G)
    (x : CoefficientSpace (Sum ι ι)) :
    fiberRight (coefficientOperator (dilationCoefficient a w) x) =
      coefficientOperator (a w⁻¹).conjTranspose (fiberLeft x) := by
  ext i
  change ((dilationCoefficient a w) *ᵥ x.ofLp) (Sum.inr i) =
    ((a w⁻¹).conjTranspose *ᵥ (fiberLeft x).ofLp) i
  simp only [dilationCoefficient, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, fiberLeft_apply]

omit [DecidableEq G] in
theorem leftSlice_dilationPolynomial (S : Finset G) (a : G → Matrix ι ι ℂ)
    (f : Hilbert G (Sum ι ι)) :
    leftSlice (regularPolynomial S (dilationCoefficient a) f) =
      regularPolynomial S a (rightSlice f) := by
  ext g i
  change regularPolynomial S (dilationCoefficient a) f g (Sum.inl i) =
    regularPolynomial S a (rightSlice f) g i
  rw [regularPolynomial_apply, regularPolynomial_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro w hw
  exact congrArg (fun v : CoefficientSpace ι => v i)
    (fiberLeft_dilationCoefficient a w (f (w⁻¹ * g)))

theorem rightSlice_dilationPolynomial (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S)
    (a : G → Matrix ι ι ℂ) (f : Hilbert G (Sum ι ι)) :
    rightSlice (regularPolynomial S (dilationCoefficient a) f) =
      (regularPolynomial S a).adjoint (leftSlice f) := by
  rw [← inverse_transpose_polynomial S hS a]
  ext g i
  change regularPolynomial S (dilationCoefficient a) f g (Sum.inr i) =
    regularPolynomial S (fun w => (a w⁻¹).conjTranspose) (leftSlice f) g i
  rw [regularPolynomial_apply, regularPolynomial_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro w hw
  exact congrArg (fun v : CoefficientSpace ι => v i)
    (fiberRight_dilationCoefficient a w (f (w⁻¹ * g)))

/-- The doubled regular polynomial has at most the original operator norm,
by orthogonal squared norms and equality of the adjoint norm. -/
theorem dilation_polynomial_norm_le (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S)
    (a : G → Matrix ι ι ℂ) :
    ‖regularPolynomial S (dilationCoefficient a)‖ ≤ ‖regularPolynomial S a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [slice_energy, leftSlice_dilationPolynomial, rightSlice_dilationPolynomial S hS,
    mul_pow, slice_energy]
  have hL := pow_le_pow_left₀ (norm_nonneg _)
    ((regularPolynomial S a).le_opNorm (rightSlice f)) 2
  have hR := pow_le_pow_left₀ (norm_nonneg _)
    ((regularPolynomial S a).adjoint.le_opNorm (leftSlice f)) 2
  have hnorm : ‖(regularPolynomial S a).adjoint‖ = ‖regularPolynomial S a‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  rw [hnorm] at hR
  simp only [mul_pow] at hL hR
  nlinarith

/-- Embedding only the right block supplies the reverse norm inequality. -/
theorem norm_le_dilation_polynomial (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S)
    (a : G → Matrix ι ι ℂ) :
    ‖regularPolynomial S a‖ ≤ ‖regularPolynomial S (dilationCoefficient a)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have h := (regularPolynomial S (dilationCoefficient a)).le_opNorm (embedRight f)
  rw [embedRight_norm] at h
  have heq : ‖regularPolynomial S (dilationCoefficient a) (embedRight f)‖ =
      ‖regularPolynomial S a f‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [slice_energy, leftSlice_dilationPolynomial, rightSlice_dilationPolynomial S hS]
    simp
  rw [heq] at h
  exact h

/-- Hermitian dilation preserves the literal infinite regular-polynomial norm.
The identity is proved on the actual vector-valued square-summable spaces. -/
theorem dilation_polynomial_norm (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S)
    (a : G → Matrix ι ι ℂ) :
    ‖regularPolynomial S (dilationCoefficient a)‖ = ‖regularPolynomial S a‖ :=
  le_antisymm (dilation_polynomial_norm_le S hS a) (norm_le_dilation_polynomial S hS a)

end Nonadditivity.RegularDilation
