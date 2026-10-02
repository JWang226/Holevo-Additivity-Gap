/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalConverse
import Nonadditivity.EntropyProducts

/-! # Concrete Naimark dilation of finite POVMs

The dilation matrix consists of the positive square roots of the actual
effects. Its Gram matrix is the identity, and its induced state map preserves
von Neumann entropy. Each diagonal label block has exactly the original Born
probability, without assuming a measurement representation theorem.
-/

noncomputable section

namespace Nonadditivity.Operational.POVM

open Entropy Channels
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

variable {ο μ : Type*} [Fintype ο] [DecidableEq ο] [Fintype μ] [DecidableEq μ]

def sqrtEffect (P : POVM ο μ) (m : μ) : Matrix ο ο ℂ := CFC.sqrt (P.effect m)

omit [DecidableEq μ] in
theorem sqrtEffect_hermitian (P : POVM ο μ) (m : μ) :
    (P.sqrtEffect m).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P.effect m))).isHermitian

omit [DecidableEq μ] in
@[simp] theorem sqrtEffect_square (P : POVM ο μ) (m : μ) :
    P.sqrtEffect m * P.sqrtEffect m = P.effect m :=
  CFC.sqrt_mul_sqrt_self _ (P.positive m).nonneg

omit [DecidableEq μ] in
@[simp] theorem sqrtEffect_gram (P : POVM ο μ) (m : μ) :
    (P.sqrtEffect m).conjTranspose * P.sqrtEffect m = P.effect m := by
  rw [(P.sqrtEffect_hermitian m).eq, P.sqrtEffect_square]

/-- The rectangular isometry `v ↦ (sqrt(E_m) v)_m`. -/
def dilationMatrix (P : POVM ο μ) : Matrix (μ × ο) ο ℂ :=
  fun p i => P.sqrtEffect p.1 p.2 i

omit [DecidableEq μ] in
@[simp] theorem dilationMatrix_gram (P : POVM ο μ) :
    P.dilationMatrix.conjTranspose * P.dilationMatrix = 1 := by
  have he : P.dilationMatrix.conjTranspose * P.dilationMatrix =
      ∑ m, (P.sqrtEffect m).conjTranspose * P.sqrtEffect m := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dilationMatrix,
      Fintype.sum_prod_type]
  rw [he]
  simp only [sqrtEffect_gram, P.complete]

/-- A single rectangular Kraus operator realizes the isometric embedding. -/
def dilationChannel (P : POVM ο μ) : KrausChannel ο (μ × ο) Unit where
  kraus := fun _ => P.dilationMatrix
  complete := by simp

/-- Actual density matrix after adjoining the coherent measurement label. -/
def dilate (P : POVM ο μ) (ρ : DensityMatrix ο) : DensityMatrix (μ × ο) :=
  P.dilationChannel.output ρ

@[simp] theorem dilate_matrix (P : POVM ο μ) (ρ : DensityMatrix ο) :
    (P.dilate ρ).matrix = P.dilationMatrix * ρ.matrix * P.dilationMatrix.conjTranspose := by
  simp [dilate, KrausChannel.output_matrix, dilationChannel, KrausChannel.map]

/-- Entropy is preserved by the literal rectangular dilation. -/
@[simp] theorem dilate_entropy (P : POVM ο μ) (ρ : DensityMatrix ο) :
    (P.dilate ρ).vonNeumann = ρ.vonNeumann := by
  apply DensityMatrix.entropy_eq_of_padded_charpoly _ _ (Fintype.card ο)
    (Fintype.card (μ × ο))
  have h := Matrix.charpoly_mul_comm' (P.dilationMatrix * ρ.matrix)
    P.dilationMatrix.conjTranspose
  simpa only [← Matrix.mul_assoc, dilationMatrix_gram, Matrix.one_mul,
    ← dilate_matrix] using h

/-- The diagonal block associated with outcome `m`. -/
def labelBlock (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) : Matrix ο ο ℂ :=
  (P.dilate ρ).matrix.submatrix (fun i => (m, i)) (fun i => (m, i))

theorem labelBlock_eq (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    P.labelBlock ρ m = P.sqrtEffect m * ρ.matrix * (P.sqrtEffect m).conjTranspose := by
  ext i j
  simp only [labelBlock, Matrix.submatrix_apply, dilate_matrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dilationMatrix]

theorem labelBlock_positive (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    (P.labelBlock ρ m).PosSemidef := by
  rw [labelBlock_eq]
  exact ρ.positive.mul_mul_conjTranspose_same _

/-- Measuring the new label reproduces exactly the original POVM statistics. -/
@[simp] theorem labelBlock_trace (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    (P.labelBlock ρ m).trace.re = P.probability ρ m := by
  rw [labelBlock_eq, Matrix.trace_mul_cycle, sqrtEffect_gram, Matrix.trace_mul_comm]
  rfl

/-- Dilation commutes with every actual finite ensemble average. -/
theorem dilate_mixture {ν : Type*} [Fintype ν] (P : POVM ο μ)
    (p : ν → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (ρ : ν → DensityMatrix ο) :
    P.dilate (DensityMatrix.mixture p hp hsum ρ) =
      DensityMatrix.mixture p hp hsum (fun i => P.dilate (ρ i)) := by
  apply Entropy.DensityMatrix.ext
  simp only [dilate_matrix, DensityMatrix.mixture_matrix, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Orthogonal projection onto a specified measurement label. -/
def labelProjection (m : μ) : Matrix (μ × ο) (μ × ο) ℂ :=
  Matrix.diagonal (fun p => if p.1 = m then 1 else 0)

omit [Fintype ο] [Fintype μ] in
theorem labelProjection_positive (m : μ) : (labelProjection (ο := ο) m).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro p
  change (0 : ℂ) ≤ if p.1 = m then 1 else 0
  split_ifs <;> norm_num

omit [Fintype ο] [Fintype μ] in
theorem labelProjection_hermitian (m : μ) :
    (labelProjection (ο := ο) m).IsHermitian := (labelProjection_positive m).isHermitian

@[simp] theorem labelProjection_idempotent (m : μ) :
    labelProjection (ο := ο) m * labelProjection m = labelProjection m := by
  unfold labelProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> norm_num

/-- Projecting on a label simply zeros every other row and column. -/
theorem labelProjection_compress_apply (A : Matrix (μ × ο) (μ × ο) ℂ)
    (m : μ) (p q : μ × ο) :
    (labelProjection (ο := ο) m * A * labelProjection (ο := ο) m :
      Matrix (μ × ο) (μ × ο) ℂ) p q =
      if p.1 = m ∧ q.1 = m then A p q else 0 := by
  simp only [labelProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hp : p.1 = m <;> by_cases hq : q.1 = m <;> simp [hp, hq]

/-- The probability of the label projection is exactly the original Born
probability of the POVM effect. -/
theorem labelProjection_probability (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    ((P.dilate ρ).matrix * labelProjection m).trace.re = P.probability ρ m := by
  rw [← labelBlock_trace P ρ m]
  congr 1
  unfold Matrix.trace
  simp only [Matrix.diag_apply, labelProjection, Matrix.mul_diagonal,
    Fintype.sum_prod_type, labelBlock, Matrix.submatrix_apply]
  simp

theorem labelProjection_compress_trace (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    (labelProjection m * (P.dilate ρ).matrix * labelProjection m).trace.re =
      P.probability ρ m := by
  rw [Matrix.trace_mul_cycle, labelProjection_idempotent, Matrix.trace_mul_comm]
  exact P.labelProjection_probability ρ m

theorem labelBlock_trace_complex (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    (P.labelBlock ρ m).trace = (P.probability ρ m : ℂ) := by
  apply Complex.ext
  · exact P.labelBlock_trace ρ m
  · have hreal := (RCLike.nonneg_iff.mp (P.labelBlock_positive ρ m).trace_nonneg).2
    simpa using hreal

/-- The normalized state inside the successful label block, with an explicit
state chosen when that label has zero probability. -/
def normalizedBlockState [Nonempty ο] (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    DensityMatrix ο :=
  if h : 0 < P.probability ρ m then {
    matrix := ((P.probability ρ m)⁻¹ : ℂ) • P.labelBlock ρ m
    positive := (P.labelBlock_positive ρ m).smul (by
      exact_mod_cast inv_nonneg.mpr h.le)
    normalized := by
      rw [Matrix.trace_smul, labelBlock_trace_complex]
      simp [h.ne'] }
  else maximallyMixed ο

theorem normalizedBlockState_matrix_of_pos [Nonempty ο] (P : POVM ο μ)
    (ρ : DensityMatrix ο) (m : μ) (h : 0 < P.probability ρ m) :
    (P.normalizedBlockState ρ m).matrix =
      ((P.probability ρ m)⁻¹ : ℂ) • P.labelBlock ρ m := by
  simp [normalizedBlockState, h]

theorem probability_smul_normalizedBlockState [Nonempty ο] (P : POVM ο μ)
    (ρ : DensityMatrix ο) (m : μ) :
    (P.probability ρ m : ℂ) • (P.normalizedBlockState ρ m).matrix = P.labelBlock ρ m := by
  by_cases h : 0 < P.probability ρ m
  · rw [normalizedBlockState_matrix_of_pos P ρ m h, smul_smul]
    simp [h.ne']
  · have hz : P.probability ρ m = 0 := le_antisymm (le_of_not_gt h) (P.probability_nonneg ρ m)
    have hB : P.labelBlock ρ m = 0 := (P.labelBlock_positive ρ m).trace_eq_zero_iff.mp
      (by rw [labelBlock_trace_complex, hz, Complex.ofReal_zero])
    simp [hz, hB]

end Nonadditivity.Operational.POVM
