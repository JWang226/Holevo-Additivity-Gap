/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingTraceDistance

/-! Actual purification and gentle-projection bounds for spectral trace distance. -/
noncomputable section
namespace Nonadditivity.QuantumCodingContinuity
open Entropy EntropyMixtures
open scoped BigOperators ComplexOrder Matrix ComplexConjugate MatrixOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Rectangular Hilbert--Schmidt norm, independent of matrix operator-norm instances. -/
def hsNorm (X : Matrix ι κ ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

omit [DecidableEq ι] in
theorem hsNorm_nonneg (X : Matrix ι κ ℂ) : 0 ≤ hsNorm X := Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem hsNorm_sq (X : Matrix ι κ ℂ) : hsNorm X ^ 2 = (X * Xᴴ).trace.re := by
  rw [hsNorm, Real.sq_sqrt (by positivity)]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

theorem hsNorm_unitary (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι κ ℂ) :
    hsNorm ((U : Matrix ι ι ℂ) * X) = hsNorm X := by
  have hsq : hsNorm ((U : Matrix ι ι ℂ) * X) ^ 2 = hsNorm X ^ 2 := by
    rw [hsNorm_sq, hsNorm_sq, Matrix.conjTranspose_mul]
    change (((U : Matrix ι ι ℂ) * X) * (Xᴴ * (star U : Matrix ι ι ℂ))).trace.re = _
    have hm : ((U : Matrix ι ι ℂ) * X) * (Xᴴ * (star U : Matrix ι ι ℂ)) =
        (U : Matrix ι ι ℂ) * (X * Xᴴ) * (star U : Matrix ι ι ℂ) := by
      simp only [Matrix.mul_assoc]
    rw [hm, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  nlinarith [hsNorm_nonneg ((U : Matrix ι ι ℂ) * X), hsNorm_nonneg X]

omit [DecidableEq ι] in
theorem entry_norm_product_sum_le (X Y : Matrix ι κ ℂ) :
    (∑ i, ∑ j, ‖X i j‖ * ‖Y i j‖) ≤ hsNorm X * hsNorm Y := by
  simpa only [hsNorm, Fintype.sum_prod_type] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun ij : ι × κ => ‖X ij.1 ij.2‖) (fun ij : ι × κ => ‖Y ij.1 ij.2‖)

private theorem abs_normSq_sub_le (x y : ℂ) :
    |Complex.normSq x - Complex.normSq y| ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hfact : ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := by ring
  rw [hfact, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x y) (by positivity)

omit [DecidableEq ι] in
/-- A dimension-free bound for the diagonal of a difference of Gram matrices. -/
theorem sum_abs_diagonal_gram_sub_le (X Y : Matrix ι κ ℂ) :
    (∑ i, |((X * Xᴴ - Y * Yᴴ) i i).re|) ≤
      hsNorm (X - Y) * (hsNorm X + hsNorm Y) := by
  have he (i : ι) : ((X * Xᴴ - Y * Yᴴ) i i).re =
      ∑ j, (Complex.normSq (X i j) - Complex.normSq (Y i j)) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
      Finset.sum_sub_distrib]
  simp_rw [he]
  calc
    _ ≤ ∑ i, ∑ j, |Complex.normSq (X i j) - Complex.normSq (Y i j)| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, ‖X i j - Y i j‖ * (‖X i j‖ + ‖Y i j‖) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_normSq_sub_le _ _
    _ = (∑ i, ∑ j, ‖(X - Y) i j‖ * ‖X i j‖) +
        (∑ i, ∑ j, ‖(X - Y) i j‖ * ‖Y i j‖) := by
      simp only [Matrix.sub_apply, mul_add, Finset.sum_add_distrib]
    _ ≤ hsNorm (X - Y) * hsNorm X + hsNorm (X - Y) * hsNorm Y :=
      add_le_add (entry_norm_product_sum_le (X - Y) X) (entry_norm_product_sum_le (X - Y) Y)
    _ = _ := by ring

/-- Purification bound for arbitrary rectangular amplitudes of normalized states. -/
theorem traceDistance_le_hsNorm_of_gram (ρ σ : DensityMatrix ι)
    (X Y : Matrix ι κ ℂ) (hX : ρ.matrix = X * Xᴴ) (hY : σ.matrix = Y * Yᴴ) :
    traceDistance ρ σ ≤ hsNorm (X - Y) := by
  let U := star (differenceHermitian ρ σ).eigenvectorUnitary
  have hd : (U : Matrix ι ι ℂ) * (ρ.matrix - σ.matrix) * (star U : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => ((differenceHermitian ρ σ).eigenvalues i : ℂ)) :=
    (differenceHermitian ρ σ).conjStarAlgAut_star_eigenvectorUnitary
  have hg : ((U : Matrix ι ι ℂ) * X) * ((U : Matrix ι ι ℂ) * X)ᴴ -
      ((U : Matrix ι ι ℂ) * Y) * ((U : Matrix ι ι ℂ) * Y)ᴴ =
      Matrix.diagonal (fun i => ((differenceHermitian ρ σ).eigenvalues i : ℂ)) := by
    calc
      _ = (U : Matrix ι ι ℂ) * (ρ.matrix - σ.matrix) * (star U : Matrix ι ι ℂ) := by
        simp only [hX, hY, Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul,
          ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = _ := hd
  have h := sum_abs_diagonal_gram_sub_le ((U : Matrix ι ι ℂ) * X) ((U : Matrix ι ι ℂ) * Y)
  rw [hg] at h
  simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re, ← Matrix.mul_sub, hsNorm_unitary] at h
  have hx : hsNorm X = 1 := by
    have hh := hsNorm_sq X
    rw [← hX, ρ.normalized, Complex.one_re] at hh
    nlinarith [hsNorm_nonneg X]
  have hy : hsNorm Y = 1 := by
    have hh := hsNorm_sq Y
    rw [← hY, σ.normalized, Complex.one_re] at hh
    nlinarith [hsNorm_nonneg Y]
  rw [hx, hy] at h
  unfold traceDistance
  linarith


omit [DecidableEq ι] in
theorem hsNorm_sub_sq (X Y : Matrix ι κ ℂ) :
    hsNorm (X - Y) ^ 2 = hsNorm X ^ 2 + hsNorm Y ^ 2 - 2 * (X * Yᴴ).trace.re := by
  have hc : (Y * Xᴴ).trace.re = (X * Yᴴ).trace.re := by
    have h := congrArg Complex.re (Matrix.trace_conjTranspose (X * Yᴴ))
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_re] using h
  rw [hsNorm_sq, hsNorm_sq, hsNorm_sq, Matrix.conjTranspose_sub,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
  simp only [Matrix.trace_sub, Complex.sub_re, hc]
  ring

/-- Gentle projection with a dimension-free square-root disturbance estimate.
The success probability is the literal matrix trace; the comparison state
is the normalized projected density matrix. -/
theorem traceDistance_gentle_projection (ρ τ : DensityMatrix ι)
    (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (hprob : (P * ρ.matrix * P).trace.re = s)
    (hτ : τ.matrix = ((s⁻¹ : ℝ) : ℂ) • (P * ρ.matrix * P)) :
    traceDistance ρ τ ≤ Real.sqrt (2 * (1 - s)) := by
  let X := CFC.sqrt ρ.matrix
  have hXh : X.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ.matrix)).isHermitian
  have hX : X * Xᴴ = ρ.matrix := by
    rw [hXh.eq]
    exact CFC.sqrt_mul_sqrt_self ρ.matrix ρ.positive.nonneg
  let c : ℂ := ((Real.sqrt s)⁻¹ : ℝ)
  let Y := c • (P * X)
  have hcstar : star c = c := by simp [c]
  have hcsq : c * c = ((s⁻¹ : ℝ) : ℂ) := by
    dsimp [c]
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← mul_inv, Real.mul_self_sqrt hs.le]
  have hY : Y * Yᴴ = τ.matrix := by
    rw [hτ]
    change (c • (P * X)) * (c • (P * X))ᴴ = _
    rw [Matrix.conjTranspose_smul, hcstar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcsq, Matrix.conjTranspose_mul, hP.eq]
    congr 1
    calc
      (P * X) * (Xᴴ * P) = P * (X * Xᴴ) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hX]
  have hx : hsNorm X = 1 := by
    have h := hsNorm_sq X
    rw [hX, ρ.normalized, Complex.one_re] at h
    nlinarith [hsNorm_nonneg X]
  have hy : hsNorm Y = 1 := by
    have h := hsNorm_sq Y
    rw [hY, τ.normalized, Complex.one_re] at h
    nlinarith [hsNorm_nonneg Y]
  have htr : (ρ.matrix * P).trace.re = s := by
    rw [Matrix.trace_mul_cycle, hPP, Matrix.trace_mul_comm] at hprob
    exact hprob
  have hcross : (X * Yᴴ).trace.re = Real.sqrt s := by
    have hm : X * Yᴴ = c • (ρ.matrix * P) := by
      change X * (c • (P * X))ᴴ = _
      rw [Matrix.conjTranspose_smul, hcstar, Matrix.mul_smul, Matrix.conjTranspose_mul, hP.eq]
      congr 1
      rw [← Matrix.mul_assoc, hX]
    rw [hm, Matrix.trace_smul]
    change (c * (ρ.matrix * P).trace).re = _
    simp only [c, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, htr]
    have hr := Real.sq_sqrt hs.le
    have hn := Real.sqrt_pos.mpr hs
    apply (inv_mul_eq_iff_eq_mul₀ hn.ne').2
    nlinarith
  have hnorm : hsNorm (X - Y) ^ 2 = 2 - 2 * Real.sqrt s := by
    rw [hsNorm_sub_sq, hx, hy, hcross]
    ring
  have hroot : s ≤ Real.sqrt s := by
    have hsqrt := Real.sq_sqrt hs.le
    have hnon := Real.sqrt_nonneg s
    nlinarith
  have hbound : hsNorm (X - Y) ≤ Real.sqrt (2 * (1 - s)) := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * (1 - s) by linarith)
    nlinarith [hsNorm_nonneg (X - Y), Real.sqrt_nonneg (2 * (1 - s))]
  exact (traceDistance_le_hsNorm_of_gram ρ τ X Y hX.symm hY.symm).trans hbound


/-- Mean square-root disturbance is controlled by the mean failure probability. -/
theorem weighted_mean_gentle_bound {μ : Type*} [Fintype μ]
    (p t e : μ → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1)
    (ht : ∀ j, 0 ≤ t j) (he : ∀ j, 0 ≤ e j)
    (hb : ∀ j, t j ≤ Real.sqrt (2 * e j)) :
    (∑ j, p j * t j) ≤ Real.sqrt (2 * ∑ j, p j * e j) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => Real.sqrt (p j)) (fun j => Real.sqrt (p j) * t j)
  have hprod (j : μ) : Real.sqrt (p j) * (Real.sqrt (p j) * t j) = p j * t j := by
    rw [← mul_assoc, Real.mul_self_sqrt (hp j)]
  simp only [hprod, mul_pow, Real.sq_sqrt (hp _), hs, one_mul] at hc
  have hsq (j : μ) : t j ^ 2 ≤ 2 * e j := by
    have hr := Real.sq_sqrt (show 0 ≤ 2 * e j from mul_nonneg (by norm_num) (he j))
    nlinarith [hb j, ht j, Real.sqrt_nonneg (2 * e j)]
  have hemean : 0 ≤ ∑ j, p j * e j := Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (he j)
  have hsum : (∑ j, p j * t j ^ 2) ≤ 2 * ∑ j, p j * e j := by
    calc
      _ ≤ ∑ j, p j * (2 * e j) := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hsq j) (hp j)
      _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hr := Real.sq_sqrt (show 0 ≤ 2 * ∑ j, p j * e j by positivity)
  nlinarith [Real.sqrt_nonneg (2 * ∑ j, p j * e j)]

end Nonadditivity.QuantumCodingContinuity
