/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductPolynomialReduction

/-! # Final self-adjoint linear polynomial with unchanged comparison error -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.PolynomialReduction.Polynomial
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open FiniteSetFactorization
variable {G : Type} [Group G] [DecidableEq G]

def symmetricSupport (P : Polynomial G) : Finset G :=
  P.support ∪ P.support.image (fun w => w⁻¹)

theorem symmetricSupport_inverse (P : Polynomial G) {w : G}
    (hw : w ∈ P.symmetricSupport) : w⁻¹ ∈ P.symmetricSupport := by
  simp only [symmetricSupport, Finset.mem_union, Finset.mem_image] at hw ⊢
  rcases hw with hw | ⟨v,hv,rfl⟩
  · exact Or.inr ⟨w,hw,rfl⟩
  · exact Or.inl (by simpa using hv)

def dilate (P : Polynomial G) : Polynomial G where
  Index := P.Index ⊕ P.Index
  fintype := inferInstance
  decEq := inferInstance
  nonempty := inferInstance
  support := P.symmetricSupport
  coefficient := dilationCoefficient P.normalizedCoefficient

@[simp] theorem dilate_dimension (P : Polynomial G) :
    Fintype.card P.dilate.Index = 2*Fintype.card P.Index := by
  simp [dilate, two_mul]

theorem dilate_normalizedCoefficient (P : Polynomial G) :
    P.dilate.normalizedCoefficient = dilationCoefficient P.normalizedCoefficient := by
  funext w
  by_cases hw : w ∈ P.symmetricSupport
  · simp [normalizedCoefficient, dilate, hw]
  · have hw0 : w ∉ P.support := fun h => hw (Finset.mem_union_left _ h)
    have hwi0 : w⁻¹ ∉ P.support := by
      intro h
      apply hw
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨w⁻¹, h, inv_inv w⟩
    simp [normalizedCoefficient, dilate, hw, dilationCoefficient, hw0, hwi0]

theorem subset_cover (P : Polynomial G) :
    P.support ⊆ Linearization.differenceSupport (insert 1 P.support) := by
  intro w hw
  exact Linearization.mem_differenceSupport.mpr
    ⟨1, by simp, w, by simp [hw], by simp⟩

theorem dilate_subset_cover (P : Polynomial G) :
    P.dilate.support ⊆ Linearization.differenceSupport (insert 1 P.support) := by
  intro w hw
  change w ∈ P.support ∪ P.support.image (fun w => w⁻¹) at hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact P.subset_cover hw
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact Linearization.inv_mem_differenceSupport (P.subset_cover hv)

theorem dilate_finite_norm (P : Polynomial G) {ν : Type*}
    [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G →* unitary (Matrix ν ν ℂ)) : ‖P.dilate.finiteEval π‖ = ‖P.finiteEval π‖ := by
  rw [← P.dilate.finiteEval_enlarge π (insert 1 P.support) P.dilate_subset_cover,
    dilate_normalizedCoefficient]
  have h := shifted_dilation_polynomial_norm (insert 1 P.support)
    P.normalizedCoefficient π 0 (by norm_num)
  simpa only [map_zero, add_zero, P.finiteEval_enlarge π _ P.subset_cover] using h

theorem dilate_regular_norm (P : Polynomial G) : ‖P.dilate.regularEval‖ = ‖P.regularEval‖ := by
  rw [← P.dilate.regularEval_enlarge (insert 1 P.support) P.dilate_subset_cover,
    dilate_normalizedCoefficient]
  have h := RegularDilation.dilation_polynomial_norm
    (Linearization.differenceSupport (insert 1 P.support))
    (fun _ hw => Linearization.inv_mem_differenceSupport hw) P.normalizedCoefficient
  simpa only [P.regularEval_enlarge _ P.subset_cover] using h

theorem dilate_finite_isHermitian (P : Polynomial G) {ν : Type*}
    [Fintype ν] [DecidableEq ν]
    (π : G →* unitary (Matrix ν ν ℂ)) : (P.dilate.finiteEval π).IsHermitian := by
  have hinv (w : G) : (π w : Matrix ν ν ℂ).conjTranspose =
      (π w⁻¹ : Matrix ν ν ℂ) := by rw [map_inv]; rfl
  unfold Matrix.IsHermitian finiteEval
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_kronecker, hinv]
  apply Finset.sum_bij (fun w _ => w⁻¹)
  · intro w hw
    exact P.symmetricSupport_inverse hw
  · intro w hw v hv h
    exact inv_injective h
  · intro w hw
    exact ⟨w⁻¹,P.symmetricSupport_inverse hw, by simp⟩
  · intro w hw
    congr 1
    exact (dilationCoefficient_inverse P.normalizedCoefficient w).symm

end Nonadditivity.PolynomialReduction.Polynomial

namespace Nonadditivity.ProductPolynomialReduction
open PolynomialReduction
open scoped Matrix Matrix.Norms.L2Operator
variable {α : Type} [DecidableEq α] {n : ℕ}

theorem dilate_degree (P : Polynomial (GroupWord α n)) (r : ℕ)
    (hP : ∀ w ∈ P.support, degree w ≤ r) :
    ∀ w ∈ P.dilate.support, degree w ≤ r := by
  intro w hw
  change w ∈ P.support ∪ P.support.image (fun w => w⁻¹) at hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact hP w hw
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    simpa only [degree_inv] using hP v hv

/-- A concrete self-adjoint linear polynomial on the original product group,
with actual finite/regular error transfer and exact coefficient dimension. -/
theorem constructed_selfAdjoint_linear_reduction (P : Polynomial (GroupWord α n)) (k : ℕ)
    (hP : ∀ w ∈ P.support, degree w ≤ 2^k) :
    ∃ H : Polynomial (GroupWord α n),
      (∀ w ∈ H.support, w=1 ∨ ∃ x : Fin n × α, w=generator x ∨ w=(generator x)⁻¹) ∧
      Fintype.card H.Index = 2*Fintype.card P.Index*dimensionCost P k ∧
      ∀ {ν : Type} [Fintype ν] [DecidableEq ν] [Nonempty ν]
        (π : GroupWord α n →* unitary (Matrix ν ν ℂ)),
        (H.finiteEval π).IsHermitian ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        ‖H.finiteEval π‖ ≤ (1+ε/(errorCost P k:ℝ))*‖H.regularEval‖ →
        ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  refine ⟨(reduce P k).dilate, ?_, ?_, ?_⟩
  · intro w hw
    exact degree_le_one_letters w (dilate_degree _ 1 (reduce_degree P k hP) w hw)
  · rw [Polynomial.dilate_dimension, reduce_dimension]
    ring
  · intro ν _ _ _ π
    refine ⟨Polynomial.dilate_finite_isHermitian _ π, ?_⟩
    intro ε hε hε1 hfinal
    apply reduce_error_transfer P k π ε hε hε1
    simpa only [Polynomial.dilate_finite_norm, Polynomial.dilate_regular_norm] using hfinal

end Nonadditivity.ProductPolynomialReduction
