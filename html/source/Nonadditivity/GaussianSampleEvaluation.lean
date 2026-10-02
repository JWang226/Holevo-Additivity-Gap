/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianRectangularAlgebra
import Nonadditivity.GaussianNetRealization
namespace Nonadditivity.GaussianRectangular
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {B Env D : Type*} [Fintype B] [Fintype Env] [Fintype D]
  [DecidableEq B] [DecidableEq Env] [DecidableEq D]

theorem sampleMatrix_mulVec (z : Sample B Env D) (x : EuclideanSpace ℂ D) :
    sampleMatrix B Env D z *ᵥ (x : D → ℂ) =
      (samplingScale B Env : ℂ) • (inputMap x *ᵥ (z : ((B × Env) × D) → ℂ)) := by
  funext r
  change (∑d, (samplingScale B Env:ℂ)*z (r,d)*x d) =
    (samplingScale B Env:ℂ) * ∑p : (B×Env)×D, (if r=p.1 then x p.2 else 0)*z p
  rw [Fintype.sum_prod_type]
  simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem dot_pullback {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix κ ι ℂ) (A : Matrix κ κ ℂ) (z : ι → ℂ) :
    star z ⬝ᵥ ((L.conjTranspose * A * L) *ᵥ z) =
      star (L *ᵥ z) ⬝ᵥ (A *ᵥ (L *ᵥ z)) := by
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.vecMul_vecMul]

theorem real_inner_complex_euclidean {ι : Type*} [Fintype ι]
    (z w : EuclideanSpace ℂ ι) : inner ℝ z w = (inner ℂ z w).re := by
  simp only [PiLp.inner_apply, Complex.re_sum, RCLike.inner_apply]
  rfl

theorem quadraticOperator_sample_identity (A : Matrix B B ℂ)
    (x : EuclideanSpace ℂ D) (z : Sample B Env D) :
    inner ℝ (quadraticOperator (Env := Env) A x z) z =
      (star (x : D → ℂ) ⬝ᵥ ((sampleMatrix B Env D z).conjTranspose *
        environmentExtension (Env := Env) A * sampleMatrix B Env D z) *ᵥ (x : D → ℂ)).re := by
  rw [real_inner_comm, real_inner_complex_euclidean, EuclideanSpace.inner_eq_star_dotProduct]
  change ((quadraticMatrix (Env := Env) A x *ᵥ (z : ((B × Env) × D) → ℂ)) ⬝ᵥ star (z : ((B × Env) × D) → ℂ)).re = _
  rw [dotProduct_comm]
  congr 1
  rw [quadraticMatrix, Matrix.smul_mulVec, dotProduct_smul, pullback_factorization,
    dot_pullback, dot_pullback, sampleMatrix_mulVec]
  simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_pow]
  ring

open scoped Kronecker

theorem environmentExtension_eq_kronecker (A : Matrix B B ℂ) :
    environmentExtension (Env := Env) A = A ⊗ₖ (1:Matrix Env Env ℂ) := by
  ext ⟨b,e⟩ ⟨c,f⟩
  simp [environmentExtension,Matrix.blockDiagonal_apply,
    Matrix.one_apply,mul_ite]

theorem quadratic_eq_dot (A : Matrix D D ℂ) (x : EuclideanSpace ℂ D) :
    GaussianNetRealization.quadratic A x =
      (star (x:D→ℂ) ⬝ᵥ (A *ᵥ (x:D→ℂ))).re := by
  unfold GaussianNetRealization.quadratic
  rw [←real_inner_complex_euclidean,real_inner_comm,real_inner_complex_euclidean,
    EuclideanSpace.inner_eq_star_dotProduct]
  change ((A *ᵥ (x:D→ℂ)) ⬝ᵥ star (x:D→ℂ)).re = _
  rw [dotProduct_comm]

/-- The actual Gaussian real quadratic form is exactly the channel compression test. -/
theorem quadraticOperator_quadratic (A : Matrix B B ℂ)
    (x : EuclideanSpace ℂ D) (z : Sample B Env D) :
    inner ℝ (quadraticOperator (Env := Env) A x z) z =
      GaussianNetRealization.quadratic
        (GaussianNormalization.rawAdjoint (sampleMatrix B Env D z) A) x := by
  rw [quadraticOperator_sample_identity,quadratic_eq_dot,environmentExtension_eq_kronecker]
  rfl

/-- The identity-observable Gaussian test controls the literal Gram matrix. -/
theorem quadraticOperator_one_quadratic (x : EuclideanSpace ℂ D) (z : Sample B Env D) :
    inner ℝ (quadraticOperator (Env := Env) (1:Matrix B B ℂ) x z) z =
      GaussianNetRealization.quadratic
        (GaussianNormalization.gram (sampleMatrix B Env D z)) x := by
  rw [quadraticOperator_quadratic]
  simp only [GaussianNormalization.rawAdjoint,Matrix.one_kronecker_one,Matrix.mul_one,
    GaussianNormalization.gram]

end
end Nonadditivity.GaussianRectangular
