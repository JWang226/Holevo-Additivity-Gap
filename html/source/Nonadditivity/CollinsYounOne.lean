/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularRestriction
import Nonadditivity.FreeBridge
import Nonadditivity.CollinsYoun

/-! # The proved one-factor Collins--Youn bound in the actual free model

Evaluation of the sole product coordinate is a genuine group isomorphism.
The regular-polynomial norm and the matrix trace/HS norm are preserved by
the corresponding concrete reindexings.
-/

noncomputable section

namespace Nonadditivity.CollinsYounOne

open FreeModel RegularRestriction
open scoped BigOperators

def oneBranchEquiv (K : ℕ) : Branch K 1 ≃ Fin K :=
  Equiv.funUnique (Fin 1) (Fin K)

def oneGroupEquiv (K : ℕ) : ProductFreeGroup K 1 ≃* FreeGroup (Fin K) :=
  MulEquiv.funUnique (Fin 1) (FreeGroup (Fin K))

def oneMatrix {K : ℕ} (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  A.submatrix (oneBranchEquiv K).symm (oneBranchEquiv K).symm

theorem oneMatrix_trace {K : ℕ} (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    (oneMatrix A).trace = A.trace :=
  FreeBridge.trace_submatrix_equiv (oneBranchEquiv K).symm A

theorem oneMatrix_hsLength {K : ℕ} (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    AdjointPurity.hsLength (oneMatrix A) = AdjointPurity.hsLength A :=
  FreeBridge.hsLength_submatrix_equiv (oneBranchEquiv K).symm A

def collapsedPolynomial {K : ℕ} (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    Hilbert (FreeGroup (Fin K)) →L[ℂ] Hilbert (FreeGroup (Fin K)) :=
  ∑ i, ∑ j, oneMatrix A i j • leftRegular ((FreeGroup.of i)⁻¹ * FreeGroup.of j)

/-- The exact unnormalized one-factor polynomial has the same regular norm
after collapsing the singleton product-group coordinate. -/
theorem one_polynomial_norm_eq {K : ℕ}
    (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    ‖∑ a : Branch K 1, ∑ b : Branch K 1,
      A a b • leftRegular ((branchWord a)⁻¹ * branchWord b)‖ =
        ‖collapsedPolynomial A‖ := by
  have h := regularPolynomial_equiv_norm_eq (oneGroupEquiv K)
    (fun p : Branch K 1 × Branch K 1 => (branchWord p.1)⁻¹ * branchWord p.2)
    (fun p => A p.1 p.2)
  simp only [regularPolynomial, Fintype.sum_prod_type] at h
  have hsum : (∑ a : Branch K 1, ∑ b : Branch K 1,
      A a b • leftRegular (oneGroupEquiv K ((branchWord a)⁻¹ * branchWord b))) =
      collapsedPolynomial A := by
    rw [← (oneBranchEquiv K).symm.sum_comp]
    unfold collapsedPolynomial
    apply Finset.sum_congr rfl
    intro i _
    rw [← (oneBranchEquiv K).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [hsum] at h
  exact h.symm

/-- Normalization of the actual `gamma` operator is exactly division by K. -/
theorem freeNorm_one_eq {K : ℕ}
    (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    freeNorm A = (1 / (K : ℝ)) * ‖collapsedPolynomial A‖ := by
  simp only [freeNorm, gamma, pow_one, norm_smul, norm_div, norm_one,
    Complex.norm_natCast]
  rw [one_polynomial_norm_eq]

/-- The manuscript's exact one-factor constant is 3/K. -/
theorem freeConstant_one {K : ℕ} (hK : 2 ≤ K) : c K 1 = 3 / (K : ℝ) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hc := c_sq hK (by norm_num : 1 ≤ (1 : ℕ))
  simp only [pow_one, add_sub_cancel_left] at hc
  have hs : (3 / (K : ℝ)) ^ 2 = (9 / (K : ℝ)) / (K : ℝ) := by ring
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ 3 / (K : ℝ))).mp
  exact hc.trans hs.symm

theorem collapsedPolynomial_eq_localPolynomial {K : ℕ}
    (A : Matrix (Branch K 1) (Branch K 1) ℂ) :
    collapsedPolynomial A = CollinsYoun.localPolynomial (oneMatrix A) := rfl

/-- The one-factor Collins--Youn assertion in the project's actual normalized
free model. All regular-operator and HS estimates are proved internally. -/
theorem collinsYounBound_one {K : ℕ} (hK : 2 ≤ K) : CollinsYounBound K 1 := by
  intro A htrace
  have ht : (oneMatrix A).trace = 0 := (oneMatrix_trace A).trans htrace
  have hb := CollinsYoun.local_polynomial_norm_le_three_hs (oneMatrix A) ht
  rw [oneMatrix_hsLength] at hb
  rw [freeNorm_one_eq, collapsedPolynomial_eq_localPolynomial, freeConstant_one hK]
  calc
    _ ≤ (1 / (K : ℝ)) * (3 * AdjointPurity.hsLength A) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Nonadditivity.CollinsYounOne
