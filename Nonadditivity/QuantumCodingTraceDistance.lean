/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingContinuity
import Nonadditivity.AdjointPurity

/-! Convexity and disturbance estimates for the actual spectral trace distance. -/
noncomputable section
namespace Nonadditivity.QuantumCodingContinuity
open Entropy EntropyMixtures
open scoped BigOperators ComplexOrder Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Absolute diagonal sum in every orthonormal basis is at most spectral trace norm. -/
theorem sum_abs_diagonal_unitary_le (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (U : unitary (Matrix ι ι ℂ)) :
    (∑ i, |(((U : Matrix ι ι ℂ) * A * (star U : Matrix ι ι ℂ)) i i).re|) ≤
      ∑ i, |hA.eigenvalues i| := by
  let V := U * hA.eigenvectorUnitary
  have hmat : (U : Matrix ι ι ℂ) * A * (star U : Matrix ι ι ℂ) =
      (V : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
        (star V : Matrix ι ι ℂ) := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [V, Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
    rfl
  simp_rw [hmat, diagonal_unitary_conjugate]
  calc
    _ ≤ ∑ i, ∑ j, unitaryWeights V i j * |hA.eigenvalues j| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j, |unitaryWeights V i j * hA.eigenvalues j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (unitaryWeights_nonneg V _ _)]
    _ = ∑ j, |hA.eigenvalues j| := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, unitaryWeights_col_sum, one_mul]

/-- Convexity of the spectral trace norm, including singular matrices and zero coefficients. -/
theorem eigenvalue_abs_sum_le_of_mixture {κ : Type*} [Fintype κ]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (B : κ → Matrix ι ι ℂ)
    (hB : ∀ j, (B j).IsHermitian) (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hmix : A = ∑ j, (p j : ℂ) • B j) :
    (∑ i, |hA.eigenvalues i|) ≤ ∑ j, p j * ∑ i, |(hB j).eigenvalues i| := by
  let U := star hA.eigenvectorUnitary
  have hd : (U : Matrix ι ι ℂ) * A * (star U : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have he (i : ι) : hA.eigenvalues i =
      ∑ j, p j * (((U : Matrix ι ι ℂ) * B j * (star U : Matrix ι ι ℂ)) i i).re := by
    have hc : (U : Matrix ι ι ℂ) * A * (star U : Matrix ι ι ℂ) =
        ∑ j, (p j : ℂ) • ((U : Matrix ι ι ℂ) * B j * (star U : Matrix ι ι ℂ)) := by
      calc
        _ = (U : Matrix ι ι ℂ) * (∑ j, (p j : ℂ) • B j) * (star U : Matrix ι ι ℂ) :=
          congrArg (fun X : Matrix ι ι ℂ => (U : Matrix ι ι ℂ) * X * (star U : Matrix ι ι ℂ)) hmix
        _ = _ := by simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hh := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) (hd.symm.trans hc)
    simpa only [Matrix.diagonal_apply_eq, Complex.ofReal_re, Matrix.sum_apply,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hh
  simp_rw [he]
  calc
    _ ≤ ∑ i, ∑ j, p j *
        |(((U : Matrix ι ι ℂ) * B j * (star U : Matrix ι ι ℂ)) i i).re| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j, |p j * (((U : Matrix ι ι ℂ) * B j * (star U : Matrix ι ι ℂ)) i i).re| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (hp _)]
    _ = ∑ j, p j * ∑ i,
        |(((U : Matrix ι ι ℂ) * B j * (star U : Matrix ι ι ℂ)) i i).re| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (sum_abs_diagonal_unitary_le (B j) (hB j) U) (hp j)

/-- Convexity of the actual half trace distance under normalized finite mixtures. -/
theorem traceDistance_mixture_le {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1)
    (ρ σ : κ → DensityMatrix ι) :
    traceDistance (DensityMatrix.mixture p hp hs ρ) (DensityMatrix.mixture p hp hs σ) ≤
      ∑ j, p j * traceDistance (ρ j) (σ j) := by
  have h := eigenvalue_abs_sum_le_of_mixture
    ((DensityMatrix.mixture p hp hs ρ).matrix - (DensityMatrix.mixture p hp hs σ).matrix)
    (differenceHermitian _ _) (fun j => (ρ j).matrix - (σ j).matrix)
    (fun j => differenceHermitian (ρ j) (σ j)) p hp (by
      simp only [DensityMatrix.mixture_matrix, smul_sub, Finset.sum_sub_distrib])
  have hh := div_le_div_of_nonneg_right h (show (0 : ℝ) ≤ 2 by norm_num)
  simpa only [traceDistance, Finset.sum_div, mul_div_assoc] using hh


/-- Symmetry follows from the basis-independent spectral trace norm. -/
theorem traceDistance_comm (ρ σ : DensityMatrix ι) : traceDistance ρ σ = traceDistance σ ρ := by
  have hone (ρ σ : DensityMatrix ι) : traceDistance ρ σ ≤ traceDistance σ ρ := by
    let U := star (differenceHermitian ρ σ).eigenvectorUnitary
    have hd : (U : Matrix ι ι ℂ) * (ρ.matrix - σ.matrix) * (star U : Matrix ι ι ℂ) =
        Matrix.diagonal (fun i => ((differenceHermitian ρ σ).eigenvalues i : ℂ)) :=
      (differenceHermitian ρ σ).conjStarAlgAut_star_eigenvectorUnitary
    have hn : (U : Matrix ι ι ℂ) * (σ.matrix - ρ.matrix) * (star U : Matrix ι ι ℂ) =
        -Matrix.diagonal (fun i => ((differenceHermitian ρ σ).eigenvalues i : ℂ)) := by
      calc
        _ = -((U : Matrix ι ι ℂ) * (ρ.matrix - σ.matrix) * (star U : Matrix ι ι ℂ)) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, neg_sub]
        _ = _ := congrArg Neg.neg hd
    have h := sum_abs_diagonal_unitary_le (σ.matrix - ρ.matrix) (differenceHermitian σ ρ) U
    rw [hn] at h
    simp only [Matrix.neg_apply, Matrix.diagonal_apply_eq, Complex.neg_re, Complex.ofReal_re,
      abs_neg] at h
    exact div_le_div_of_nonneg_right h (by norm_num)
  exact le_antisymm (hone ρ σ) (hone σ ρ)

end Nonadditivity.QuantumCodingContinuity
