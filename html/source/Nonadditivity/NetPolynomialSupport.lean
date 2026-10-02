/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NetPolynomial
import Nonadditivity.PolynomialDilation

/-! # Collected-word polynomial for the observable test net

Repeated branch words are summed into actual matrix coefficients on a finite
support, so the constructed shortening theorem applies to the test polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Nonadditivity.NetPolynomialSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open NetPolynomial

section Collection
variable {G J I : Type} [Group G] [DecidableEq G]
  [Fintype J] [DecidableEq J] [Fintype I]

def wordSupport (w : I → G) : Finset G := Finset.univ.image w

def collectedScalar (w : I → G) (a : I → J → ℂ) (g : G) (j : J) : ℂ :=
  ∑ i, if w i = g then a i j else 0

def collectedCoefficient (w : I → G) (a : I → J → ℂ) (g : G) : Matrix J J ℂ :=
  Matrix.diagonal (collectedScalar w a g)

omit [Group G] [Fintype J] [DecidableEq J] in
/-- Summing repeated words preserves every scalar finite evaluation. -/
theorem collected_sum {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (w : I → G) (a : I → J → ℂ) (j : J) (f : G → V) :
    ∑ g ∈ wordSupport w, collectedScalar w a g j • f g = ∑ i, a i j • f (w i) := by
  classical
  simp only [collectedScalar, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp [wordSupport]

/-- The grouped coefficient polynomial is exactly the original direct sum,
on the same actual vector-valued Hilbert space. -/
theorem collected_regular_eq (w : I → G) (a : I → J → ℂ) :
    RegularCoefficientEnergy.regularPolynomial (wordSupport w) (collectedCoefficient w a) =
      NetPolynomial.regularPolynomial w a := by
  ext f g j
  simp only [RegularDilation.regularPolynomial_apply, WithLp.ofLp_sum, Finset.sum_apply,
    NetPolynomial.regularPolynomial, MatrixRegularRestriction.coefficientPolynomial_apply]
  have he (v : G) : RegularCoefficientEnergy.coefficientOperator (collectedCoefficient w a v)
      (f (v⁻¹*g)) j = collectedScalar w a v j * f (v⁻¹*g) j := by
    change (Matrix.diagonal (collectedScalar w a v) *ᵥ (f (v⁻¹*g)).ofLp) j = _
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  simp only [he, diagonalCoefficient_apply]
  exact collected_sum w a j (fun v => f (v⁻¹*g) j)

/-- A finite polynomial record with exactly the original coefficient dimension. -/
def polynomial [Nonempty J] (w : I → G) (a : I → J → ℂ) :
    PolynomialReduction.Polynomial G where
  Index := J
  fintype := inferInstance
  decEq := inferInstance
  nonempty := inferInstance
  support := wordSupport w
  coefficient := collectedCoefficient w a

@[simp] theorem polynomial_regularEval [Nonempty J] (w : I → G) (a : I → J → ℂ) :
    (polynomial w a).regularEval = NetPolynomial.regularPolynomial w a :=
  collected_regular_eq w a

omit [Fintype J] in
/-- Collection followed by swapping tensor coordinates gives exactly the
finite direct sum, with no norm comparison premise. -/
theorem collected_finite_eq {V : Type*} [Fintype V] [DecidableEq V]
    (w : I → G) (a : I → J → ℂ) (π : G →* unitary (Matrix V V ℂ)) :
    (∑ g ∈ wordSupport w, collectedCoefficient w a g ⊗ₖ (π g : Matrix V V ℂ)).submatrix
      (Equiv.prodComm V J) (Equiv.prodComm V J) =
      finitePolynomial (fun i => (π (w i) : Matrix V V ℂ)) a := by
  ext ⟨x,j⟩ ⟨y,k⟩
  rw [finitePolynomial_eq_blockDiagonal]
  simp only [Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.sum_apply,
    Matrix.kronecker_apply, collectedCoefficient, Matrix.diagonal_apply,
    Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : j = k
  · subst k
    simp only [ite_true]
    exact collected_sum w a j (fun g => (π g : Matrix V V ℂ) x y)
  · simp [h]

/-- The finite polynomial record has the exact maximum test norm. -/
theorem polynomial_finiteEval_norm [Nonempty J]
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : I → G) (a : I → J → ℂ) (π : G →* unitary (Matrix V V ℂ)) :
    ‖(polynomial w a).finiteEval π‖ = ‖fun j => ∑ i, a i j • (π (w i) : Matrix V V ℂ)‖ := by
  rw [← MatrixNormReindex.submatrix_equiv_norm (Equiv.prodComm V J)
    ((polynomial w a).finiteEval π)]
  rw [show (polynomial w a).finiteEval π =
    ∑ g ∈ wordSupport w, collectedCoefficient w a g ⊗ₖ (π g : Matrix V V ℂ) from rfl]
  rw [collected_finite_eq, finitePolynomial_norm]
end Collection

end Nonadditivity.NetPolynomialSupport
