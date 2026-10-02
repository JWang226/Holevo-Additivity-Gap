/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarTensorReplacement
import Nonadditivity.MatrixNormReindex

/-! # Partial substitution agrees with literal tensor evaluation

Only a finite basis permutation separates consecutive matrix substitutions
from a single tensor representation. The operator norm is exactly preserved.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarTensorReplacement
open HaarWordExpansion RegularCoefficientEnergy
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker ENNReal

variable {G H ι ν κ : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

def productRepresentation (ρ : G →* Matrix ν ν ℂ) (σ : H →* Matrix κ κ ℂ) :
    G × H →* Matrix (ν × κ) (ν × κ) ℂ where
  toFun w := ρ w.1 ⊗ₖ σ w.2
  map_one' := by simp
  map_mul' g h := by simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Matrix.mul_kronecker_mul]

theorem finiteEval_partial_eq (ρ : G →* Matrix ν ν ℂ) (σ : H →* Matrix κ κ ℂ)
    (f : MatrixPolynomial (G × H) ι) :
    finiteEval σ (partialEval ρ f) =
      (finiteEval (productRepresentation ρ σ) f).submatrix
        (Equiv.prodAssoc ι ν κ) (Equiv.prodAssoc ι ν κ) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk =>
    change finiteEval σ (partialEval ρ ((f : MatrixPolynomial (G × H) ι) + k)) = _
    rw [map_add, map_add, map_add, Matrix.submatrix_add, hf, hk]
    rfl
  | single g A =>
    simp only [partialEval_single, finiteEval_single]
    ext a b
    change (A a.1.1 b.1.1 * ρ g.1 a.1.2 b.1.2) * σ g.2 a.2 b.2 =
      A a.1.1 b.1.1 * (ρ g.1 a.1.2 b.1.2 * σ g.2 a.2 b.2)
    ring

theorem finiteEval_partial_norm (ρ : G →* Matrix ν ν ℂ) (σ : H →* Matrix κ κ ℂ)
    (f : MatrixPolynomial (G × H) ι) :
    ‖finiteEval σ (partialEval ρ f)‖ = ‖finiteEval (productRepresentation ρ σ) f‖ := by
  rw [finiteEval_partial_eq, MatrixNormReindex.submatrix_equiv_norm]

theorem rectLift_norm (A : Matrix ι ι ℂ) : ‖RegularFactorization.rectLift (G := G) A‖ = ‖A‖ := by
  have hc : ‖coefficientOperator A‖ = ‖A‖ := rfl
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro f
    have hb := RegularFactorization.liftFunction_norm_le
      (G := G) (coefficientOperator A) f
    rw [hc] at hb
    exact hb
  · rw [← hc]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have he : RegularFactorization.rectLift (G := G) A (lp.single 2 (1:G) x) =
        lp.single 2 (1:G) (coefficientOperator A x) := by
      ext g i
      simp only [RegularFactorization.rectLift_apply, lp.single_apply, Pi.single_apply]
      split_ifs <;> simp_all [coefficientOperator]
    have hb := (RegularFactorization.rectLift (G := G) A).le_opNorm (lp.single 2 (1:G) x)
    rw [he, lp.norm_single (by norm_num), lp.norm_single (by norm_num)] at hb
    exact hb

theorem polynomial_eq_single_of_unique [Unique G] (f : MatrixPolynomial G ι) :
    f = MonoidAlgebra.single 1 (f 1) := by
  ext g i j
  have hg : g = 1 := Subsingleton.elim _ _
  simp [hg]

/-- After every free coordinate has been replaced, the remaining regular
norm is exactly the norm of the finite coefficient matrix. -/
theorem regularEval_unique_norm [Unique G] (f : MatrixPolynomial G ι) :
    ‖regularEval f‖ = ‖f 1‖ := by
  rw [polynomial_eq_single_of_unique f, regularEval_single,
    RegularFactorization.term_identity, rectLift_norm]
  simp

theorem kronecker_punit_one_norm (A : Matrix ι ι ℂ) :
    ‖A ⊗ₖ (1 : Matrix PUnit PUnit ℂ)‖ = ‖A‖ := by
  have he : A ⊗ₖ (1 : Matrix PUnit PUnit ℂ) =
      A.submatrix (Equiv.prodPUnit ι) (Equiv.prodPUnit ι) := by
    ext a b
    simp [Matrix.kronecker_apply]
  rw [he, MatrixNormReindex.submatrix_equiv_norm]

theorem finiteEval_trivial_norm [Unique G] (f : MatrixPolynomial G ι) :
    ‖finiteEval (1 : G →* Matrix PUnit PUnit ℂ) f‖ = ‖regularEval f‖ := by
  rw [regularEval_unique_norm, polynomial_eq_single_of_unique f, finiteEval_single]
  simpa using kronecker_punit_one_norm (f 1)

end Nonadditivity.HaarTensorReplacement
