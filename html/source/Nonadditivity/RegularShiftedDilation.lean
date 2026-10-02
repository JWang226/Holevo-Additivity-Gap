/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularDilation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! # The exact shifted norm of an infinite regular dilation

The grading unitary makes the spectrum symmetric, so its positive endpoint
is the original polynomial norm. No finite-dimensional spectral assumption
is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularShiftedDilation

open RegularCoefficientEnergy RegularDilation
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

section Lift

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Applying the same bounded operator at each coordinate is a star-algebra map. -/
def liftStarAlgHom : (E →L[ℂ] E) →⋆ₐ[ℂ] (VectorHilbert G E →L[ℂ] VectorHilbert G E) where
  toFun := liftOperator
  map_zero' := by ext f g; simp
  map_one' := by ext f g; simp
  map_add' T R := by ext f g; simp
  map_mul' T R := by ext f g; simp
  commutes' z := by ext f g; simp
  map_star' T := by
    apply ContinuousLinearMap.ext
    intro f
    apply ext_inner_right ℂ
    intro h
    simp only [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.adjoint_inner_left]
    change (∑' g, inner ℂ ((star T) (f g)) (h g)) =
      ∑' g, inner ℂ (f g) (T (h g))
    simp_rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

end Lift

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

def grading : unitary (Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) :=
  let F : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ →⋆ₐ[ℂ]
      (Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) :=
    (liftStarAlgHom (G := G) (E := CoefficientSpace (ι ⊕ ι))).comp
      (StarAlgHomClass.toStarAlgHom (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℂ)))
  ⟨F Linearization.dilationSign.val, Unitary.map_mem F Linearization.dilationSign.property⟩

omit [Group G] [DecidableEq G] in
theorem grading_apply (f : Hilbert G (ι ⊕ ι)) (g : G) (i : ι ⊕ ι) :
    (grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) f g i =
      Sum.elim (fun j => f g (Sum.inl j)) (fun j => -f g (Sum.inr j)) i := by
  change (Linearization.dilationSign.val *ᵥ (f g).ofLp) i = _
  cases i <;>
    simp [Linearization.dilationSign, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

omit [Group G] [DecidableEq G] in
theorem grading_star :
    star (grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) =
      (grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) := by
  have hs : star (Linearization.dilationSign (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) =
      (Linearization.dilationSign (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := by
    simp [Linearization.dilationSign, Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose]
  change star ((liftStarAlgHom (G := G) (E := CoefficientSpace (ι ⊕ ι)))
    (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℂ) Linearization.dilationSign.val)) =
      (liftStarAlgHom (G := G) (E := CoefficientSpace (ι ⊕ ι)))
        (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℂ) Linearization.dilationSign.val)
  rw [← map_star, ← map_star, hs]

theorem dilation_selfAdjoint (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S)
    (a : G → Matrix ι ι ℂ) :
    IsSelfAdjoint (regularPolynomial S (dilationCoefficient a)) := by
  change (regularPolynomial S (dilationCoefficient a)).adjoint = _
  rw [← inverse_transpose_polynomial S hS]
  congr 1
  funext w
  simp [dilationCoefficient, Matrix.fromBlocks_conjTranspose]

omit [DecidableEq G] in
theorem grading_conjugate (S : Finset G) (a : G → Matrix ι ι ℂ) :
    (grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) *
      regularPolynomial S (dilationCoefficient a) *
      (star (grading (G := G) (ι := ι)) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) =
        -regularPolynomial S (dilationCoefficient a) := by
  rw [grading_star]
  ext f g i
  simp only [ContinuousLinearMap.mul_apply, grading_apply,
    ContinuousLinearMap.neg_apply, lp.coeFn_neg, Pi.neg_apply, WithLp.ofLp_neg]
  cases i with
  | inl i =>
    change (leftSlice (regularPolynomial S (dilationCoefficient a) ((grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) f))) g i = _
    rw [leftSlice_dilationPolynomial]
    have hr : rightSlice ((grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) f) = -rightSlice f := by
      ext h j
      exact grading_apply f h (Sum.inr j)
    rw [hr, map_neg]
    exact congrArg Neg.neg (congrArg (fun v : Hilbert G ι => v g i)
      (leftSlice_dilationPolynomial S a f)).symm
  | inr i =>
    simp only [Sum.elim_inr, regularPolynomial_apply,
      WithLp.ofLp_sum, Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    change fiberRight (coefficientOperator (dilationCoefficient a w)
      ((grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) f (w⁻¹ * g))) i =
      fiberRight (coefficientOperator (dilationCoefficient a w) (f (w⁻¹ * g))) i
    rw [fiberRight_dilationCoefficient, fiberRight_dilationCoefficient]
    have hl : fiberLeft ((grading (G := G) (ι := ι) : Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι))
        f (w⁻¹ * g)) = fiberLeft (f (w⁻¹ * g)) := by
      ext j
      exact grading_apply f (w⁻¹ * g) (Sum.inl j)
    rw [hl]

instance hilbertNontrivial [Nonempty ι] : Nontrivial (Hilbert G ι) := by
  classical
  let i : ι := Classical.choice inferInstance
  let x : CoefficientSpace ι := WithLp.toLp 2 (fun _ => (1 : ℂ))
  refine ⟨⟨lp.single 2 (1 : G) x, 0, ?_⟩⟩
  intro h
  have he := congrArg (fun f : Hilbert G ι => f 1 i) h
  simp [x] at he

theorem norm_mem_dilation_spectrum [Nonempty ι]
    (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S) (a : G → Matrix ι ι ℂ) :
    ‖regularPolynomial S a‖ ∈ spectrum ℝ (regularPolynomial S (dilationCoefficient a)) := by
  have hsym : spectrum ℝ (-regularPolynomial S (dilationCoefficient a)) =
      spectrum ℝ (regularPolynomial S (dilationCoefficient a)) := by
    rw [← grading_conjugate S a]
    exact Unitary.spectrum_star_right_conjugate
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (dilation_selfAdjoint S hS a) with h | h
  · simpa only [dilation_polynomial_norm S hS a] using h
  · rw [dilation_polynomial_norm S hS a] at h
    have hneg : ‖regularPolynomial S a‖ ∈
        spectrum ℝ (-regularPolynomial S (dilationCoefficient a)) := by
      rw [← spectrum.neg_eq]
      exact h
    rwa [hsym] at hneg

/-- The exact infinite-dimensional norm identity needed by Gram factorization. -/
theorem shifted_dilation_polynomial_norm [Nonempty ι]
    (S : Finset G) (hS : ∀ w ∈ S, w⁻¹ ∈ S) (a : G → Matrix ι ι ℂ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ‖regularPolynomial S (dilationCoefficient a) +
      algebraMap ℝ (Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) θ‖ =
        ‖regularPolynomial S a‖ + θ := by
  apply le_antisymm
  · calc
      _ ≤ ‖regularPolynomial S (dilationCoefficient a)‖ +
          ‖algebraMap ℝ (Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) θ‖ := norm_add_le _ _
      _ = ‖regularPolynomial S a‖ + θ := by
        rw [dilation_polynomial_norm S hS a, norm_algebraMap', Real.norm_eq_abs,
          abs_of_nonneg hθ]
  · have hmem : ‖regularPolynomial S a‖ + θ ∈ spectrum ℝ
        (regularPolynomial S (dilationCoefficient a) +
          algebraMap ℝ (Hilbert G (ι ⊕ ι) →L[ℂ] Hilbert G (ι ⊕ ι)) θ) := by
      rw [← spectrum.add_singleton_eq]
      exact Set.add_mem_add (norm_mem_dilation_spectrum S hS a) (Set.mem_singleton θ)
    have h := spectrum.norm_le_norm_of_mem hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) hθ)] at h

end Nonadditivity.RegularShiftedDilation
