/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingUnion
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order

/-! # Matrix trace form of the projective quantum union bound

The vector estimate is summed over the columns of an arbitrary amplitude.
Thus it applies to every positive matrix, without normalization or a rank
restriction, and to the literal ordered product of the selected projections.
-/

noncomputable section
namespace Nonadditivity.QuantumCoding
open scoped BigOperators InnerProductSpace Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A Hermitian idempotent matrix gives an actual orthogonal projection. -/
def Projection.ofMatrix (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hAA : A*A=A) : Projection (EuclideanSpace ℂ ι) where
  map := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  symmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  idempotent := by
    intro x
    have h := congrArg (fun B : Matrix ι ι ℂ => Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B x) hAA
    simpa only [map_mul, ContinuousLinearMap.mul_apply] using h

/-- The ordered product after `n` selected projective outcomes. -/
def actualProduct (A : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | n+1 => A n * actualProduct A n

/-- Matrix products describe exactly the vector projection trajectory. -/
theorem matrix_trajectory (A : ℕ → Matrix ι ι ℂ)
    (hA : ∀i, (A i).IsHermitian) (hAA : ∀i, A i*A i=A i)
    (x : EuclideanSpace ℂ ι) (n : ℕ) :
    Projection.trajectory (fun i => Projection.ofMatrix (A i) (hA i) (hAA i)) x n =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (actualProduct A n) x := by
  induction n with
  | zero => simp [Projection.trajectory, actualProduct]
  | succ n ih =>
    simp only [Projection.trajectory, actualProduct, map_mul,
      ContinuousLinearMap.mul_apply]
    change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A n)
      (Projection.trajectory (fun i => Projection.ofMatrix (A i) (hA i) (hAA i)) x n) = _
    rw [ih]

/-- One column of a rectangular amplitude, as a genuine Euclidean vector. -/
def amplitudeColumn (X : Matrix ι κ ℂ) (j : κ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => X i j)

omit [Fintype κ] in
theorem amplitudeColumn_mul (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) (j : κ) :
    amplitudeColumn (A*X) j = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (amplitudeColumn X j) := rfl

omit [Fintype κ] in
theorem amplitudeColumn_sub_mul (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) (j : κ) :
    amplitudeColumn (((1 : Matrix ι ι ℂ)-A)*X) j =
      amplitudeColumn X j - Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (amplitudeColumn X j) := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  rfl

omit [DecidableEq ι] in
/-- The squared column norms sum to the literal Gram-matrix trace. -/
theorem trace_gram_eq_sum_column_norm_sq (X : Matrix ι κ ℂ) :
    (X*X.conjTranspose).trace.re = ∑ j, ‖amplitudeColumn X j‖^2 := by
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, ←Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq, EuclideanSpace.norm_sq_eq,
    amplitudeColumn]

/-- For an orthogonal projection, squared rejected amplitude equals its
single failure probability on the original positive matrix. -/
theorem rejected_gram_trace (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hAA : A*A=A) (X : Matrix ι κ ℂ) :
    ((((1 : Matrix ι ι ℂ)-A)*X)*(((1 : Matrix ι ι ℂ)-A)*X).conjTranspose).trace =
      (((1 : Matrix ι ι ℂ)-A)*(X*X.conjTranspose)).trace := by
  have hQ : ((1 : Matrix ι ι ℂ)-A)*((1 : Matrix ι ι ℂ)-A)=1-A := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAA]
    abel
  have hstar : ((1 : Matrix ι ι ℂ)-A).conjTranspose=1-A := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hA.eq]
  rw [Matrix.conjTranspose_mul, hstar]
  calc
    ((((1 : Matrix ι ι ℂ)-A)*X)*(X.conjTranspose*((1 : Matrix ι ι ℂ)-A))).trace =
        ((((1 : Matrix ι ι ℂ)-A)*(X*X.conjTranspose))*((1 : Matrix ι ι ℂ)-A)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((((1 : Matrix ι ι ℂ)-A)*((1 : Matrix ι ι ℂ)-A))*(X*X.conjTranspose)).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = _ := by rw [hQ]

/-- Gao's bound for actual ordered matrix projections and any rectangular
amplitude, with no dimension or normalization factor. -/
theorem trace_union_bound_amplitude (A : ℕ → Matrix ι ι ℂ)
    (hA : ∀i, (A i).IsHermitian) (hAA : ∀i, A i*A i=A i)
    (X : Matrix ι κ ℂ) (n : ℕ) :
    (X*X.conjTranspose).trace.re -
        (actualProduct A n * (X*X.conjTranspose) * (actualProduct A n).conjTranspose).trace.re ≤
      4 * ∑ i ∈ Finset.range n, ((1-A i)*(X*X.conjTranspose)).trace.re := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Projection.union_bound
      (fun i => Projection.ofMatrix (A i) (hA i) (hAA i)) (amplitudeColumn X j) n)
  have hre (i : ℕ) (j : κ) :
      amplitudeColumn X j - (Projection.ofMatrix (A i) (hA i) (hAA i)).map
        (amplitudeColumn X j) = amplitudeColumn ((1-A i)*X) j :=
    (amplitudeColumn_sub_mul (A i) X j).symm
  simp_rw [hre, matrix_trajectory, ←amplitudeColumn_mul] at h
  rw [Finset.sum_sub_distrib, ←Finset.mul_sum, Finset.sum_comm] at h
  simp_rw [←trace_gram_eq_sum_column_norm_sq] at h
  simp_rw [rejected_gram_trace _ (hA _) (hAA _)] at h
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

/-- The trace union bound applies to every positive semidefinite input matrix.
The square root is constructed by continuous functional calculus. -/
theorem trace_union_bound (A : ℕ → Matrix ι ι ℂ)
    (hA : ∀i, (A i).IsHermitian) (hAA : ∀i, A i*A i=A i)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (n : ℕ) :
    ρ.trace.re -
        (actualProduct A n * ρ * (actualProduct A n).conjTranspose).trace.re ≤
      4 * ∑ i ∈ Finset.range n, ((1-A i)*ρ).trace.re := by
  have hroot : CFC.sqrt ρ * (CFC.sqrt ρ).conjTranspose = ρ := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  simpa only [hroot] using trace_union_bound_amplitude A hA hAA (CFC.sqrt ρ) n

end Nonadditivity.QuantumCoding
