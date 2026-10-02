/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Hermitian dilation on an arbitrary complex Hilbert space

The two blocks carry the Hilbert product norm. The grading symmetry puts the
positive norm endpoint in the spectrum, without a finite-dimensional premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.UniversalShiftedDilation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Double (E : Type*) := WithLp 2 (E × E)

/-- The Hermitian block matrix with upper-right block `A`. -/
def dilation (A : E →L[ℂ] E) : Double E →L[ℂ] Double E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    ((A.comp (WithLp.sndL 2 ℂ E E)).prod
      (A.adjoint.comp (WithLp.fstL 2 ℂ E E)))

@[simp] theorem dilation_apply_fst (A : E →L[ℂ] E) (x : Double E) :
    (dilation A x).fst = A x.snd := rfl

@[simp] theorem dilation_apply_snd (A : E →L[ℂ] E) (x : Double E) :
    (dilation A x).snd = A.adjoint x.fst := rfl

theorem dilation_norm_le (A : E →L[ℂ] E) : ‖dilation A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, dilation_apply_fst, dilation_apply_snd,
    mul_pow, WithLp.prod_norm_sq_eq_of_L2]
  have hL := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm x.snd) 2
  have hR := pow_le_pow_left₀ (norm_nonneg _) (A.adjoint.le_opNorm x.fst) 2
  have hnorm : ‖A.adjoint‖ = ‖A‖ := ContinuousLinearMap.adjoint.norm_map _
  rw [hnorm] at hR
  simp only [mul_pow] at hL hR
  nlinarith

theorem norm_le_dilation (A : E →L[ℂ] E) : ‖A‖ ≤ ‖dilation A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : Double E := WithLp.toLp 2 (0, x)
  have hy : ‖y‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [y]
  have hAy : ‖dilation A y‖ = ‖A x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [WithLp.prod_norm_sq_eq_of_L2, y]
  simpa only [hy, hAy] using (dilation A).le_opNorm y

theorem dilation_norm (A : E →L[ℂ] E) : ‖dilation A‖ = ‖A‖ :=
  le_antisymm (dilation_norm_le A) (norm_le_dilation A)

theorem dilation_selfAdjoint (A : E →L[ℂ] E) : IsSelfAdjoint (dilation A) := by
  change (dilation A).adjoint = dilation A
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    dilation_apply_fst, dilation_apply_snd, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact add_comm _ _

def gradingOperator : Double E →L[ℂ] Double E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 ℂ E E).prod (-(WithLp.sndL 2 ℂ E E)))

omit [CompleteSpace E] in
@[simp] theorem grading_apply_fst (x : Double E) :
    (gradingOperator x).fst = x.fst := rfl

omit [CompleteSpace E] in
@[simp] theorem grading_apply_snd (x : Double E) :
    (gradingOperator x).snd = -x.snd := rfl

theorem grading_star : star (gradingOperator (E := E)) = gradingOperator := by
  change gradingOperator.adjoint = gradingOperator (E := E)
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

omit [CompleteSpace E] in
theorem grading_sq : gradingOperator (E := E) * gradingOperator = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext <;> simp [ContinuousLinearMap.mul_apply]

def grading : unitary (Double E →L[ℂ] Double E) :=
  ⟨gradingOperator, by
    rw [Unitary.mem_iff, grading_star]
    exact ⟨grading_sq, grading_sq⟩⟩

theorem grading_conjugate (A : E →L[ℂ] E) :
    (grading (E := E) : Double E →L[ℂ] Double E) * dilation A *
      (star (grading (E := E)) : Double E →L[ℂ] Double E) = -dilation A := by
  change gradingOperator * dilation A * star gradingOperator = _
  rw [grading_star]
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext <;> simp [ContinuousLinearMap.mul_apply]

theorem norm_mem_dilation_spectrum [Nontrivial E] (A : E →L[ℂ] E) :
    ‖A‖ ∈ spectrum ℝ (dilation A) := by
  have hsym : spectrum ℝ (-dilation A) = spectrum ℝ (dilation A) := by
    rw [← grading_conjugate A]
    exact Unitary.spectrum_star_right_conjugate
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (dilation_selfAdjoint A) with h | h
  · simpa only [dilation_norm] using h
  · rw [dilation_norm] at h
    have hneg : ‖A‖ ∈ spectrum ℝ (-dilation A) := by
      rw [← spectrum.neg_eq]
      exact h
    rwa [hsym] at hneg

/-- The exact shifted dilation identity, valid on every nonzero complex Hilbert space. -/
theorem shifted_dilation_norm [Nontrivial E] (A : E →L[ℂ] E) (θ : ℝ) (hθ : 0 ≤ θ) :
    ‖dilation A + algebraMap ℝ (Double E →L[ℂ] Double E) θ‖ = ‖A‖ + θ := by
  apply le_antisymm
  · calc
      _ ≤ ‖dilation A‖ + ‖algebraMap ℝ (Double E →L[ℂ] Double E) θ‖ := norm_add_le _ _
      _ = ‖A‖ + θ := by
        rw [dilation_norm, norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg hθ]
  · have hmem : ‖A‖ + θ ∈ spectrum ℝ
        (dilation A + algebraMap ℝ (Double E →L[ℂ] Double E) θ) := by
      rw [← spectrum.add_singleton_eq]
      exact Set.add_mem_add (norm_mem_dilation_spectrum A) (Set.mem_singleton θ)
    have h := spectrum.norm_le_norm_of_mem hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) hθ)] at h

end Nonadditivity.UniversalShiftedDilation
