/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.UniversalFactorizationOperators
import Nonadditivity.RegularFactorization

/-! Representation-independent Gram factorization on arbitrary complex Hilbert spaces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Nonadditivity.UniversalFactorization
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
section Assembly
open FiniteSetFactorization
variable {G ι E : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (π : G →* unitary (E →L[ℂ] E))

def polynomial (S : Finset G) (c : G → Matrix ι ι ℂ) : Space ι E →L[ℂ] Space ι E :=
  ∑ w ∈ S, term π (c w) w


/-- The actual column of represented unitaries on the given finite support. -/
def column (S : Finset G) : Space ι E →L[ℂ] Space (Support S × ι) E :=
  ∑ g : Support S, term π (selector g).conjTranspose g.val

def evaluate (S : Finset G) (A : Matrix (Support S × ι) (Support S × ι) ℂ) :
    Space ι E →L[ℂ] Space ι E :=
  (column π S).adjoint.comp ((rectLift A).comp (column π S))

theorem select_column (S : Finset G) (g : Support S) :
    (rectLift (selector (ι := ι) g)).comp (column π S) = shift π g.val := by
  rw [column, ContinuousLinearMap.comp_finset_sum]
  conv_lhs => arg 2; ext h; rw [← term_identity π, term_mul π, one_mul,
    selector_mul_adjoint]
  rw [Finset.sum_eq_single g]
  · simp
  · intro h hh hne
    simp [Ne.symm hne]
  · simp

@[simp] theorem evaluate_add (S : Finset G)
    (A B : Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate π S (A+B) = evaluate π S A + evaluate π S B := by
  simp [evaluate, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

@[simp] theorem evaluate_smul (S : Finset G) (r : ℝ)
    (A : Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate π S (r • A) = r • evaluate π S A := by
  simp [evaluate, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem evaluate_sum {α : Type*} (S : Finset G) (s : Finset α)
    (A : α → Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate π S (∑ a ∈ s, A a) = ∑ a ∈ s, evaluate π S (A a) := by
  simp [evaluate, ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum]

theorem evaluate_place (S : Finset G) (g h : Support S) (A : Matrix ι ι ℂ) :
    evaluate π S (place g h A) = term π A (g.val⁻¹*h.val) := by
  have heq : evaluate π S (place g h A) =
      ((rectLift (selector g)).comp (column π S)).adjoint.comp
        ((rectLift A).comp ((rectLift (selector h)).comp (column π S))) := by
    simp only [evaluate, place, rectLift_mul, rectLift_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
  rw [heq, select_column π, select_column π, shift_adjoint π, ← ContinuousLinearMap.comp_assoc, ← rectLift_shift π,
    ContinuousLinearMap.comp_assoc, shift_mul π]
  rfl

theorem evaluate_polarInsertion (S : Finset G) (g h : Support S) (c : Matrix ι ι ℂ) :
    evaluate π S (polarInsertion g h c) =
      rectLift (CFC.abs c.conjTranspose) + term π c (g.val⁻¹*h.val) +
      term π c.conjTranspose (h.val⁻¹*g.val) + rectLift (CFC.abs c) := by
  rw [polarInsertion_eq]
  simp only [evaluate_add π, evaluate_place π, inv_mul_cancel, term_identity]

theorem evaluate_representative (S : Finset G) (c : G → Matrix ι ι ℂ)
    (w : NonidentityWords S) :
    evaluate π S (polarInsertion (representative S w).1 (representative S w).2 (c w.val)) =
      rectLift (CFC.abs (c w.val).conjTranspose) + term π (c w.val) w.val +
      term π (c w.val).conjTranspose w.val⁻¹ + rectLift (CFC.abs (c w.val)) := by
  rw [evaluate_polarInsertion π, representative_spec]
  have hinv : (representative S w).2.val⁻¹ * (representative S w).1.val = w.val⁻¹ := by
    rw [← representative_spec S w]
    simp
  rw [hinv]

theorem evaluate_nonconstantGram (S : Finset G) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    evaluate π S (nonconstantGram S c) =
      (∑ w : NonidentityWords S, term π (c w.val) w.val) + rectLift (diagonalCorrection S c) := by
  have hmod : (∑ w : NonidentityWords S, CFC.abs (c w.val).conjTranspose) =
      diagonalCorrection S c := by
    unfold diagonalCorrection
    apply Fintype.sum_equiv (inverseWords S)
    intro w
    rw [← hstar w.val (Finset.mem_erase.mp w.property).2]
    rfl
  have hinv : (∑ w : NonidentityWords S, term π (c w.val).conjTranspose w.val⁻¹) =
      ∑ w : NonidentityWords S, term π (c w.val) w.val := by
    apply Fintype.sum_equiv (inverseWords S)
    intro w
    rw [← hstar w.val (Finset.mem_erase.mp w.property).2]
    rfl
  unfold nonconstantGram
  rw [evaluate_sum π]
  simp only [evaluate_smul π, evaluate_representative π]
  rw [← Finset.smul_sum (M := ℝ) (N := Space ι E →L[ℂ] Space ι E)
    (r := (1 / 2 : ℝ)) (s := Finset.univ)
    (f := fun w : NonidentityWords S => rectLift (CFC.abs (c w.val).conjTranspose) +
      term π (c w.val) w.val + term π (c w.val).conjTranspose w.val⁻¹ +
      rectLift (CFC.abs (c w.val)))]
  simp only [Finset.sum_add_distrib]
  rw [← rectLift_sum, hmod, hinv, ← rectLift_sum]
  change (1 / 2 : ℝ) •
    (rectLift (diagonalCorrection S c) +
      (∑ w : NonidentityWords S, term π (c w.val) w.val) +
      (∑ w : NonidentityWords S, term π (c w.val) w.val) +
      rectLift (diagonalCorrection S c)) = _
  module

theorem polynomial_eq (S : Finset G) (c : G → Matrix ι ι ℂ) :
    polynomial π S c = ∑ w ∈ S, term π (c w) w := rfl

theorem polynomial_decompose (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    polynomial π (Linearization.differenceSupport S) c =
      (∑ w : NonidentityWords S, term π (c w.val) w.val) + rectLift (c 1) := by
  have h1 : (1:G) ∈ Linearization.differenceSupport S :=
    Linearization.mem_differenceSupport.mpr ⟨1,hS,1,hS,by simp⟩
  rw [polynomial_eq π]
  have hs : (∑ w : NonidentityWords S, term π (c w.val) w.val) =
      ∑ w ∈ (Linearization.differenceSupport S).erase 1, term π (c w) w :=
    (Finset.sum_subtype (p := fun w => w ∈ (Linearization.differenceSupport S).erase 1)
      ((Linearization.differenceSupport S).erase 1) (fun _ => Iff.rfl) (fun w => term π (c w) w)).symm
  rw [hs, ← term_identity π (c 1)]
  exact (Finset.sum_erase_add _ _ h1).symm

/-- Evaluation of the same finite positive Gram matrix in any unitary representation. -/
theorem evaluate_gramMatrix (S : Finset G) (hS : (1:G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    evaluate π S (gramMatrix S hS c) =
      polynomial π (Linearization.differenceSupport S) c +
        algebraMap ℝ (Space ι E →L[ℂ] Space ι E) (theta S c) := by
  rw [gramMatrix, evaluate_add π, evaluate_nonconstantGram π S c hstar, evaluate_place π]
  simp only [inv_one, one_mul, term_identity]
  rw [add_assoc, ← rectLift_add]
  have hc : diagonalCorrection S c + constantCorrection S c =
      c 1 + algebraMap ℝ (Matrix ι ι ℂ) (theta S c) := by
    unfold constantCorrection
    abel
  rw [hc, rectLift_add, rectLift_algebraMap, polynomial_decompose π S hS c]
  abel

/-- Rectangular square-root factor evaluated in the given representation. -/
def factor (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Space ι E →L[ℂ] Space (Support S × ι) E :=
  ∑ g : Support S, term π (factorCoefficient S hS c g) g.val

theorem factor_eq (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    factor π S hS c = (rectLift (CFC.sqrt (gramMatrix S hS c))).comp (column π S) := by
  unfold factor factorCoefficient column term
  rw [ContinuousLinearMap.comp_finset_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [rectLift_mul, ContinuousLinearMap.comp_assoc]

/-- The Gram identity on an arbitrary complete complex Hilbert space. -/
theorem factor_gram (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    (factor π S hS c).adjoint.comp (factor π S hS c) =
      polynomial π (Linearization.differenceSupport S) c +
        algebraMap ℝ (Space ι E →L[ℂ] Space ι E) (theta S c) := by
  have hG := gramMatrix_posSemidef S hS c hstar
  have hR := Linearization.positive_sqrt_gram (gramMatrix S hS c) hG
  rw [factor_eq π, ContinuousLinearMap.adjoint_comp, ← rectLift_adjoint]
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (rectLift _),
    ← rectLift_mul, hR]
  exact evaluate_gramMatrix π S hS c hstar

/-- The same padded coefficient matrices evaluated in the given representation. -/
def padded (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Space (Support S × ι) E →L[ℂ] Space (Support S × ι) E :=
  ∑ g : Support S, term π (paddedCoefficient S hS c g) g.val

/-- Extend the constructed supported coefficients by zero to the whole group. -/
def paddedCoefficients (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : G) : Matrix (Support S × ι) (Support S × ι) ℂ :=
  if hg : g ∈ S then paddedCoefficient S hS c ⟨g,hg⟩ else 0

/-- The padded factor is the actual polynomial with the constructed supported coefficients. -/
theorem padded_eq_polynomial (S : Finset G) (hS : (1:G) ∈ S)
    (c : G → Matrix ι ι ℂ) :
    padded π S hS c = polynomial π S (paddedCoefficients S hS c) := by
  rw [polynomial_eq π]
  unfold padded
  rw [← Finset.sum_coe_sort S (fun g => term π (paddedCoefficients S hS c g) g)]
  apply Finset.sum_congr rfl
  intro g hg
  simp [paddedCoefficients, g.property]

theorem padded_eq (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    padded π S hS c = (factor π S hS c).comp (rectLift (selector (⟨1,hS⟩ : Support S))) := by
  unfold padded factor paddedCoefficient
  rw [ContinuousLinearMap.finset_sum_comp]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← term_identity π (selector (⟨1,hS⟩ : Support S)), term_mul π, mul_one]

theorem padded_norm (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    ‖padded π S hS c‖ = ‖factor π S hS c‖ := by
  rw [padded_eq π]
  apply RegularFactorization.norm_comp_coisometry
  rw [← rectLift_adjoint, ← rectLift_mul, selector_mul_adjoint]
  simp

/-- Squared norm of the factor from its proved Gram identity. -/
theorem padded_norm_sq (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    ‖padded π S hS c‖ ^ 2 =
      ‖polynomial π (Linearization.differenceSupport S) c +
        algebraMap ℝ (Space ι E →L[ℂ] Space ι E) (theta S c)‖ := by
  rw [padded_norm π, pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self,
    factor_gram π S hS c hstar]


end Assembly
end Nonadditivity.UniversalFactorization
