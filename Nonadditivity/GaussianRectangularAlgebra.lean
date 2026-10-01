/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianRectangular
import Nonadditivity.NetPolynomial
import Nonadditivity.ComplexRealTrace

namespace Nonadditivity.GaussianRectangular

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

variable {B Env D : Type*} [Fintype B] [Fintype Env] [Fintype D]
  [DecidableEq B] [DecidableEq Env] [DecidableEq D]

def inputMap (x : EuclideanSpace ℂ D) : Matrix (B × Env) ((B × Env) × D) ℂ :=
  fun r p => if r = p.1 then x p.2 else 0

def environmentExtension (A : Matrix B B ℂ) : Matrix (B × Env) (B × Env) ℂ :=
  Matrix.blockDiagonal fun _ : Env => A

theorem inputMap_mul_adjoint (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    inputMap (B := B) (Env := Env) x * (inputMap (B := B) (Env := Env) x).conjTranspose = 1 := by
  have hsum : ∑ d, x d * star (x d) = (1 : ℂ) := by
    calc
      _ = inner ℂ x x := rfl
      _ = (‖x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K x
      _ = 1 := by rw [hx]; norm_num
  change (∑ d, x d * (starRingEnd ℂ) (x d)) = (1 : ℂ) at hsum
  ext r s
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [inputMap, starRingEnd_apply]
  have he (t : B × Env) :
      (∑ d : D, (if r = t then x d else 0) * star (if s = t then x d else 0)) =
      if r = t then (if s = t then 1 else 0) else 0 := by
    by_cases hr : r = t <;> by_cases hs : s = t <;> simp [hr, hs, hsum]
  simp only [he]
  simp [Matrix.one_apply, eq_comm]

theorem pullback_factorization (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) :
    pullbackMatrix (Env := Env) A x =
      (inputMap x).conjTranspose * environmentExtension A * inputMap x := by
  have hleft (p : (B × Env) × D) (r : B × Env) :
      ((inputMap (B := B) (Env := Env) x).conjTranspose * environmentExtension (Env := Env) A) p r =
        star (x p.2) * environmentExtension A p.1 r := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inputMap]
    calc
      _ = ∑ t : B × Env, if t = p.1 then star (x p.2) * environmentExtension A t r else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : t = p.1 <;> simp [ht]
      _ = _ := by simp
  ext p q
  rw [Matrix.mul_apply]
  simp only [hleft, inputMap, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [pullbackMatrix, environmentExtension, Matrix.blockDiagonal_apply]
  split_ifs <;> simp_all

theorem environmentExtension_mul (A C : Matrix B B ℂ) :
    environmentExtension (Env := Env) (A * C) =
      environmentExtension A * environmentExtension C :=
  Matrix.blockDiagonal_mul _ _

theorem pullback_mul (A C : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    pullbackMatrix (Env := Env) A x * pullbackMatrix C x = pullbackMatrix (A * C) x := by
  rw [pullback_factorization, pullback_factorization, pullback_factorization,
    environmentExtension_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (inputMap x), inputMap_mul_adjoint x hx, Matrix.one_mul]

theorem trace_pullback (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    (pullbackMatrix (Env := Env) A x).trace = (Fintype.card Env : ℂ) * A.trace := by
  rw [pullback_factorization, Matrix.trace_mul_cycle, inputMap_mul_adjoint x hx,
    Matrix.one_mul, environmentExtension, Matrix.trace_blockDiagonal]
  simp

theorem pullback_isHermitian (A : Matrix B B ℂ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ D) : (pullbackMatrix (Env := Env) A x).IsHermitian := by
  change (pullbackMatrix A x).conjTranspose = _
  rw [pullback_factorization, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  have he : (environmentExtension (Env := Env) A).conjTranspose = environmentExtension A := by
    simp only [environmentExtension, Matrix.blockDiagonal_conjTranspose, hA.eq]
  rw [he]
  simp only [Matrix.mul_assoc]

theorem inputMap_norm [Nonempty B] [Nonempty Env]
    (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) : ‖inputMap (B := B) (Env := Env) x‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self ((inputMap (B := B) (Env := Env) x).conjTranspose)
  rw [Matrix.conjTranspose_conjTranspose, inputMap_mul_adjoint x hx,
    norm_one, Matrix.l2_opNorm_conjTranspose] at h
  nlinarith [norm_nonneg (inputMap (B := B) (Env := Env) x)]

theorem environmentExtension_norm [Nonempty Env] (A : Matrix B B ℂ) :
    ‖environmentExtension (Env := Env) A‖ = ‖A‖ := by
  rw [environmentExtension, NetPolynomial.blockDiagonal_norm]
  simp

theorem pullback_norm_le [Nonempty B] [Nonempty Env]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    ‖pullbackMatrix (Env := Env) A x‖ ≤ ‖A‖ := by
  rw [pullback_factorization]
  calc
    _ ≤ ‖(inputMap x).conjTranspose * environmentExtension (Env := Env) A‖ * ‖inputMap x‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(inputMap x).conjTranspose‖ * ‖environmentExtension (Env := Env) A‖) * ‖inputMap x‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose, inputMap_norm x hx,
      environmentExtension_norm, one_mul, mul_one]

theorem samplingScale_sq [Nonempty B] [Nonempty Env] :
    samplingScale B Env ^ 2 = 1 / (2 * (Fintype.card B : ℝ) * Fintype.card Env) := by
  dsimp [samplingScale]
  rw [inv_pow, Real.sq_sqrt (by positivity), one_div]

theorem quadraticMatrix_isHermitian (A : Matrix B B ℂ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ D) : (quadraticMatrix (Env := Env) A x).IsHermitian := by
  change (quadraticMatrix (Env := Env) A x).conjTranspose = _
  simp only [quadraticMatrix, Matrix.conjTranspose_smul, star_trivial, (pullback_isHermitian A hA x).eq]

theorem quadraticOperator_symmetric (A : Matrix B B ℂ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ D) : (quadraticOperator (Env := Env) A x).toLinearMap.IsSymmetric := by
  have hi (z w : Sample B Env D) :
      inner ℝ z w = (inner ℂ z w).re := by
    simp only [PiLp.inner_apply, Complex.re_sum, RCLike.inner_apply]
    rfl
  have h := Matrix.isHermitian_iff_isSymmetric.mp (quadraticMatrix_isHermitian (Env := Env) A hA x)
  intro z w
  change inner ℝ (quadraticOperator (Env := Env) A x z) w = inner ℝ z (quadraticOperator (Env := Env) A x w)
  rw [hi, hi]
  exact congrArg Complex.re (h z w)

theorem quadraticOperator_norm_le [Nonempty B] [Nonempty Env]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    ‖quadraticOperator (Env := Env) A x‖ ≤ ‖A‖ / (2 * (Fintype.card B : ℝ) * Fintype.card Env) := by
  unfold quadraticOperator
  rw [ContinuousLinearMap.norm_restrictScalars,
    Matrix.l2_opNorm_toEuclideanCLM, quadraticMatrix, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (pullback_norm_le (Env := Env) A x hx) (sq_nonneg (samplingScale B Env))
  rw [samplingScale_sq] at h ⊢
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

theorem trace_quadraticMatrix (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    (quadraticMatrix (Env := Env) A x).trace.re =
      samplingScale B Env ^ 2 * Fintype.card Env * A.trace.re := by
  rw [quadraticMatrix, Matrix.trace_smul, trace_pullback A x hx]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero, sub_zero]
  ring

theorem trace_quadraticMatrix_sq (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    (quadraticMatrix (Env := Env) A x * quadraticMatrix A x).trace.re =
      samplingScale B Env ^ 4 * Fintype.card Env * (A * A).trace.re := by
  rw [quadraticMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    pullback_mul A A x hx, Matrix.trace_smul, trace_pullback (A * A) x hx]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero, sub_zero]
  ring


theorem quadraticOperator_trace [Nonempty B] [Nonempty Env]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    (quadraticOperator (Env := Env) A x).toLinearMap.trace ℝ (Sample B Env D) =
      A.trace.re / Fintype.card B := by
  unfold quadraticOperator
  rw [ComplexRealTrace.trace_restrict, trace_quadraticMatrix A x hx, samplingScale_sq]
  have hB : (Fintype.card B : ℝ) ≠ 0 := by positivity
  have hN : (Fintype.card Env : ℝ) ≠ 0 := by positivity
  field_simp

theorem quadraticOperator_trace_square [Nonempty B] [Nonempty Env]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖ = 1) :
    ((quadraticOperator (Env := Env) A x).toLinearMap *
      (quadraticOperator (Env := Env) A x).toLinearMap).trace ℝ (Sample B Env D) =
      (A * A).trace.re / (2 * (Fintype.card B : ℝ)^2 * Fintype.card Env) := by
  unfold quadraticOperator
  rw [ComplexRealTrace.trace_square_restrict, trace_quadraticMatrix_sq A x hx]
  rw [show samplingScale B Env ^ 4 = (samplingScale B Env ^ 2)^2 by ring, samplingScale_sq]
  have hB : (Fintype.card B : ℝ) ≠ 0 := by positivity
  have hN : (Fintype.card Env : ℝ) ≠ 0 := by positivity
  field_simp

end
end Nonadditivity.GaussianRectangular
