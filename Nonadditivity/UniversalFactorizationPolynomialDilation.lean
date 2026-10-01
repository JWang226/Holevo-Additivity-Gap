/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.UniversalFactorizationGram
import Nonadditivity.UniversalShiftedDilation
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! # Hermitian dilation in every Hilbert-space unitary representation

The same inverse-transpose matrix coefficients give the actual Hilbert adjoint.
Splitting the two coefficient blocks is an explicit linear isometry; hence the
shifted-dilation identity applies to the literal represented polynomial.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace Nonadditivity.UniversalFactorization
open scoped BigOperators InnerProductSpace Matrix
open FiniteSetFactorization

variable {G ι E : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (π : G →* unitary (E →L[ℂ] E))

omit [DecidableEq G] in
/-- Inverting an inverse-closed support preserves every finite sum. -/
theorem inverse_closed_sum {A : Type*} [AddCommMonoid A]
    (S : Finset G) (hS : ∀w∈S, w⁻¹∈S) (f : G → A) :
    (∑w∈S, f w⁻¹)=∑w∈S, f w := by
  apply Finset.sum_bij (fun w _ => w⁻¹)
  · intro w hw; exact hS w hw
  · intro w hw v hv heq; exact inv_injective heq
  · intro w hw; exact ⟨w⁻¹,hS w hw,by simp⟩
  · intro w hw; rfl

/-- The inverse-transpose coefficient polynomial is the actual Hilbert adjoint. -/
theorem polynomial_adjoint (S : Finset G) (hS : ∀w∈S, w⁻¹∈S)
    (a : G → Matrix ι ι ℂ) :
    (polynomial π S a).adjoint = polynomial π S (fun w => (a w⁻¹).conjTranspose) := by
  simp only [polynomial,map_sum,term_adjoint]
  have h := inverse_closed_sum S hS (fun w => term π (a w⁻¹).conjTranspose w)
  simpa only [inv_inv] using h

/-- Split the two coefficient blocks into a Hilbert direct sum. -/
def dilationSplit : Space (ι ⊕ ι) E ≃ₗᵢ[ℂ]
    UniversalShiftedDilation.Double (Space ι E) :=
  PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : ι ⊕ ι => E)

omit [DecidableEq ι] [CompleteSpace E] in
@[simp] theorem dilationSplit_fst (x : Space (ι ⊕ ι) E) (i : ι) :
    (dilationSplit x).ofLp.1 i=x (Sum.inl i) := rfl

omit [DecidableEq ι] [CompleteSpace E] in
@[simp] theorem dilationSplit_snd (x : Space (ι ⊕ ι) E) (i : ι) :
    (dilationSplit x).ofLp.2 i=x (Sum.inr i) := rfl

omit [DecidableEq ι] [CompleteSpace E] in
@[simp] theorem dilationSplit_symm_inl
    (x : UniversalShiftedDilation.Double (Space ι E)) (i : ι) :
    (dilationSplit.symm x) (Sum.inl i)=x.ofLp.1 i := rfl

omit [DecidableEq ι] [CompleteSpace E] in
@[simp] theorem dilationSplit_symm_inr
    (x : UniversalShiftedDilation.Double (Space ι E)) (i : ι) :
    (dilationSplit.symm x) (Sum.inr i)=x.ofLp.2 i := rfl

/-- The upper-right block has exactly the original polynomial coefficients. -/
theorem polynomial_dilation_inl (S : Finset G) (a : G → Matrix ι ι ℂ)
    (x : Space (ι ⊕ ι) E) (i : ι) :
    polynomial π S (dilationCoefficient a) x (Sum.inl i) =
      polynomial π S a (dilationSplit x).ofLp.2 i := by
  simp only [polynomial,ContinuousLinearMap.sum_apply,WithLp.ofLp_sum,Finset.sum_apply,
    term,ContinuousLinearMap.comp_apply,rectLift_apply,shift_apply,dilationCoefficient,
    Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_smul,
    Finset.sum_const_zero,zero_add,add_zero]
  rfl

/-- The lower-left block is exactly the adjoint, including the inverse words. -/
theorem polynomial_dilation_inr (S : Finset G) (hS : ∀w∈S, w⁻¹∈S)
    (a : G → Matrix ι ι ℂ) (x : Space (ι ⊕ ι) E) (i : ι) :
    polynomial π S (dilationCoefficient a) x (Sum.inr i) =
      (polynomial π S a).adjoint (dilationSplit x).ofLp.1 i := by
  rw [polynomial_adjoint π S hS]
  simp only [polynomial,ContinuousLinearMap.sum_apply,WithLp.ofLp_sum,Finset.sum_apply,
    term,ContinuousLinearMap.comp_apply,rectLift_apply,shift_apply,dilationCoefficient,
    Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_smul,
    Finset.sum_const_zero,zero_add,add_zero]
  rfl

/-- The represented coefficient polynomial is precisely the Hermitian dilation
under the explicit coefficient-block splitting isometry. -/
theorem polynomial_dilation (S : Finset G) (hS : ∀w∈S, w⁻¹∈S)
    (a : G → Matrix ι ι ℂ) :
    dilationSplit.conjStarAlgEquiv (polynomial π S (dilationCoefficient a)) =
      UniversalShiftedDilation.dilation (polynomial π S a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.equiv 2 (Space ι E × Space ι E)).injective
  apply Prod.ext
  · ext i
    change polynomial π S (dilationCoefficient a) (dilationSplit.symm x) (Sum.inl i) = _
    rw [polynomial_dilation_inl π]
    simp
  · ext i
    change polynomial π S (dilationCoefficient a) (dilationSplit.symm x) (Sum.inr i) = _
    rw [polynomial_dilation_inr π S hS]
    simp

/-- Exact shifted polynomial norm for every nonzero Hilbert representation. -/
theorem shifted_dilation_polynomial_norm [Nonempty ι] [Nontrivial E]
    (S : Finset G) (hS : ∀w∈S, w⁻¹∈S) (a : G → Matrix ι ι ℂ)
    (θ : ℝ) (hθ : 0≤θ) :
    ‖polynomial π S (dilationCoefficient a)+
      algebraMap ℝ (Space (ι ⊕ ι) E →L[ℂ] Space (ι ⊕ ι) E) θ‖ =
        ‖polynomial π S a‖+θ := by
  rw [←StarAlgEquiv.norm_map (dilationSplit (ι := ι) (E := E)).conjStarAlgEquiv]
  rw [map_add, polynomial_dilation π S hS]
  have hshift : (dilationSplit (ι := ι) (E := E)).conjStarAlgEquiv
      (algebraMap ℝ (Space (ι ⊕ ι) E →L[ℂ] Space (ι ⊕ ι) E) θ) =
      algebraMap ℝ (UniversalShiftedDilation.Double (Space ι E) →L[ℂ]
        UniversalShiftedDilation.Double (Space ι E)) θ := by
    ext x
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
    exact (dilationSplit (ι := ι) (E := E)).map_smul_of_tower θ _ |>.trans
      (congrArg (fun z => θ • z) ((dilationSplit (ι := ι) (E := E)).apply_symm_apply x))
  rw [hshift]
  exact UniversalShiftedDilation.shifted_dilation_norm _ θ hθ

end Nonadditivity.UniversalFactorization
