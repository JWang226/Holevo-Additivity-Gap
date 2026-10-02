/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCS

/-! # Coefficient amplification in an arbitrary Hilbert representation

Rectangular scalar matrices act on finite Hilbert direct sums. An arbitrary
unitary representation acts coordinatewise and commutes with every such
coefficient matrix. Products and adjoints are proved on the actual operators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.UniversalFactorization

open scoped BigOperators InnerProductSpace Matrix

abbrev Space (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] :=
  NoncommutativeCS.DirectSum ι E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

def rectLift (A : Matrix ι κ ℂ) : Space κ E →L[ℂ] Space ι E :=
  NoncommutativeCS.column (fun i => NoncommutativeCS.row
    (fun j => A i j • ContinuousLinearMap.id ℂ E))

@[simp] theorem rectLift_apply (A : Matrix ι κ ℂ) (x : Space κ E) (i : ι) :
    rectLift A x i = ∑ j, A i j • x j := by
  simp [rectLift]

@[simp] theorem rectLift_zero : rectLift (E := E) (0 : Matrix ι κ ℂ) = 0 := by
  ext x i
  simp

@[simp] theorem rectLift_add (A B : Matrix ι κ ℂ) :
    rectLift (E := E) (A + B) = rectLift A + rectLift B := by
  ext x i
  simp [add_smul, Finset.sum_add_distrib]

@[simp] theorem rectLift_smul (r : ℝ) (A : Matrix ι κ ℂ) :
    rectLift (E := E) (r • A) = r • rectLift A := by
  ext x i
  simp only [rectLift_apply, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    Matrix.smul_apply]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => smul_assoc r (A i j) (x j))

@[simp] theorem rectLift_one [DecidableEq ι] :
    rectLift (E := E) (1 : Matrix ι ι ℂ) = 1 := by
  ext x i
  simp [Matrix.one_apply, ite_smul]

@[simp] theorem rectLift_mul (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) :
    rectLift (E := E) (A * B) = (rectLift A).comp (rectLift B) := by
  ext x i
  simp only [rectLift_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

@[simp] theorem rectLift_adjoint (A : Matrix ι κ ℂ) :
    rectLift (E := E) A.conjTranspose = (rectLift A).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, rectLift_apply, Matrix.conjTranspose_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]
  rw [Finset.sum_comm]

@[simp] theorem rectLift_sum {α : Type*} (s : Finset α) (A : α → Matrix ι κ ℂ) :
    rectLift (E := E) (∑ a ∈ s, A a) = ∑ a ∈ s, rectLift (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

@[simp] theorem rectLift_algebraMap [DecidableEq ι] (r : ℝ) :
    rectLift (E := E) (algebraMap ℝ (Matrix ι ι ℂ) r) =
      algebraMap ℝ (Space ι E →L[ℂ] Space ι E) r := by
  simp only [Algebra.algebraMap_eq_smul_one, rectLift_smul, rectLift_one]

variable {G : Type*} [Group G]

/-- Coordinatewise action of the given arbitrary unitary representation. -/
def shift (π : G →* unitary (E →L[ℂ] E)) (g : G) : Space ι E →L[ℂ] Space ι E :=
  NoncommutativeCS.amplify (π g : E →L[ℂ] E)

@[simp] theorem shift_apply (π : G →* unitary (E →L[ℂ] E)) (g : G)
    (x : Space ι E) (i : ι) : shift π g x i = (π g : E →L[ℂ] E) (x i) := rfl

@[simp] theorem shift_mul (π : G →* unitary (E →L[ℂ] E)) (g h : G) :
    (shift (ι := ι) π g).comp (shift π h) = shift π (g * h) := by
  ext x i
  simp [map_mul]

@[simp] theorem shift_one (π : G →* unitary (E →L[ℂ] E)) :
    shift (ι := ι) π 1 = 1 := by
  ext x i
  simp

@[simp] theorem shift_adjoint (π : G →* unitary (E →L[ℂ] E)) (g : G) :
    (shift (ι := ι) π g).adjoint = shift π g⁻¹ := by
  have hi : (π g⁻¹ : E →L[ℂ] E) = (π g : E →L[ℂ] E).adjoint := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
      ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, shift_apply, hi, ContinuousLinearMap.adjoint_inner_left]

theorem rectLift_shift (π : G →* unitary (E →L[ℂ] E)) (A : Matrix ι κ ℂ) (g : G) :
    (rectLift A).comp (shift π g) = (shift π g).comp (rectLift A) := by
  ext x i
  simp

/-- A scalar matrix coefficient times the arbitrary unitary representation. -/
def term (π : G →* unitary (E →L[ℂ] E)) (A : Matrix ι κ ℂ) (g : G) :
    Space κ E →L[ℂ] Space ι E := (rectLift A).comp (shift π g)

@[simp] theorem term_add (π : G →* unitary (E →L[ℂ] E))
    (A B : Matrix ι κ ℂ) (g : G) :
    term π (A + B) g = term π A g + term π B g := by
  simp [term, ContinuousLinearMap.add_comp]

@[simp] theorem term_smul (π : G →* unitary (E →L[ℂ] E))
    (r : ℝ) (A : Matrix ι κ ℂ) (g : G) :
    term π (r • A) g = r • term π A g := by
  simp [term, ContinuousLinearMap.smul_comp]

@[simp] theorem term_zero (π : G →* unitary (E →L[ℂ] E)) (g : G) :
    term π (0 : Matrix ι κ ℂ) g = 0 := by simp [term]

@[simp] theorem term_one [DecidableEq ι] (π : G →* unitary (E →L[ℂ] E)) (g : G) :
    term π (1 : Matrix ι ι ℂ) g = shift π g := by
  ext x i
  simp [term]

@[simp] theorem term_identity (π : G →* unitary (E →L[ℂ] E)) (A : Matrix ι κ ℂ) :
    term π A 1 = rectLift A := by
  ext x i
  simp [term]

theorem term_mul (π : G →* unitary (E →L[ℂ] E))
    (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) (g h : G) :
    (term π A g).comp (term π B h) = term π (A * B) (g * h) := by
  simp only [term, rectLift_mul, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (shift π g), ← rectLift_shift,
    ContinuousLinearMap.comp_assoc, shift_mul]

theorem term_adjoint (π : G →* unitary (E →L[ℂ] E)) (A : Matrix ι κ ℂ) (g : G) :
    (term π A g).adjoint = term π A.conjTranspose g⁻¹ := by
  simp only [term, ContinuousLinearMap.adjoint_comp, shift_adjoint, ← rectLift_adjoint]
  exact (rectLift_shift π _ _).symm

end Nonadditivity.UniversalFactorization
