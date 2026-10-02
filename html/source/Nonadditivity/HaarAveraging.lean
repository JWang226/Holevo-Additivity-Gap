/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Haar averaging in every finite-dimensional unitary representation

The averaged matrix is proved to be the orthogonal projection onto the
invariant vectors.  The entries of the mixed tensor-power specialization
are Haar moments of arbitrary degree.  This is the algebraic starting point
of Weingarten calculus; it does not assert a growing-degree trace estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarAveraging

open MeasureTheory HaarModel
open scoped Matrix Matrix.Norms.L2Operator Kronecker

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Normalization and Haar uniqueness give right invariance as well. -/
instance haarRightInvariant (N : ℕ) : (haar N).IsMulRightInvariant := by
  constructor
  intro V
  letI : IsProbabilityMeasure ((haar N).map (fun U => U * V)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const V).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The canonical normalized Haar law is invariant under inversion. -/
instance haarInvInvariant (N : ℕ) : (haar N).IsInvInvariant := by
  letI : IsProbabilityMeasure (haar N).inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  letI : (haar N).inv.IsHaarMeasure := { }
  constructor
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Entrywise Haar averaging of a continuous matrix-valued representation. -/
def average (R : LocalUnitary N → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ U, R U i j ∂haar N

omit [Fintype ι] [DecidableEq ι] in
lemma integrable_entry {R : LocalUnitary N → Matrix ι ι ℂ}
    (hR : Continuous R) (i j : ι) : Integrable (fun U => R U i j) (haar N) :=
  (hR.matrix_elem i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [DecidableEq ι] in
/-- The actual average is fixed by every represented group element. -/
theorem mul_average (R : LocalUnitary N → Matrix ι ι ℂ)
    (hR : Continuous R) (hmul : ∀ U V, R (U * V) = R U * R V)
    (V : LocalUnitary N) : R V * average R = average R := by
  ext i j
  simp only [Matrix.mul_apply, average]
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum _ (fun k _ => (integrable_entry hR k j).const_mul _)]
  simp_rw [← Matrix.mul_apply, ← hmul]
  exact integral_mul_left_eq_self (μ := haar N) (fun U => R U i j) V

omit [DecidableEq ι] in
/-- Averaging also absorbs multiplication on the right. -/
theorem average_mul (R : LocalUnitary N → Matrix ι ι ℂ)
    (hR : Continuous R) (hmul : ∀ U V, R (U * V) = R U * R V)
    (V : LocalUnitary N) : average R * R V = average R := by
  ext i j
  simp only [Matrix.mul_apply, average]
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum _ (fun k _ => (integrable_entry hR i k).mul_const _)]
  simp_rw [← Matrix.mul_apply, ← hmul]
  exact integral_mul_right_eq_self (μ := haar N) (fun U => R U i j) V

omit [DecidableEq ι] in
/-- Arbitrary-order Haar averaging is idempotent. -/
theorem average_sq (R : LocalUnitary N → Matrix ι ι ℂ)
    (hR : Continuous R) (hmul : ∀ U V, R (U * V) = R U * R V) :
    average R * average R = average R := by
  ext i j
  change (∑ k, (∫ U, R U i k ∂haar N) * average R k j) = average R i j
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum _ (fun k _ => (integrable_entry hR i k).mul_const _)]
  change (∫ U, (R U * average R) i j ∂haar N) = average R i j
  simp_rw [mul_average R hR hmul]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- Haar inversion makes the average of a unitary representation Hermitian. -/
theorem average_conjTranspose (R : LocalUnitary N → Matrix ι ι ℂ)
    (hinv : ∀ U, R U⁻¹ = (R U)ᴴ) : (average R)ᴴ = average R := by
  ext i j
  change starRingEnd ℂ (∫ U, R U j i ∂haar N) = ∫ U, R U i j ∂haar N
  rw [← integral_conj]
  change (∫ U, (R U)ᴴ i j ∂haar N) = _
  simp_rw [← hinv]
  exact integral_inv_eq_self (fun U => R U i j) (haar N)

omit [DecidableEq ι] in
/-- A vector is fixed by the average exactly when it is invariant. -/
theorem average_mulVec_eq_iff (R : LocalUnitary N → Matrix ι ι ℂ)
    (hR : Continuous R) (hmul : ∀ U V, R (U * V) = R U * R V)
    (v : ι → ℂ) :
    average R *ᵥ v = v ↔ ∀ U, R U *ᵥ v = v := by
  constructor
  · intro hv U
    calc
      R U *ᵥ v = R U *ᵥ (average R *ᵥ v) := by rw [hv]
      _ = (R U * average R) *ᵥ v := Matrix.mulVec_mulVec v (R U) (average R)
      _ = v := by rw [mul_average R hR hmul, hv]
  · intro hv
    funext i
    change (∑ j, (∫ U, R U i j ∂haar N) * v j) = v i
    simp_rw [← integral_mul_const]
    rw [← integral_finset_sum _ (fun j _ => (integrable_entry hR i j).mul_const _)]
    change (∫ U, (R U *ᵥ v) i ∂haar N) = v i
    simp_rw [hv]
    simp

section TensorPowers

open Entropy

abbrev PowerIndex (N p : ℕ) := TensorChainIndex (Fin (N+1)) p

/-- The literal tensor power, including its one-dimensional zeroth power. -/
def tensorPower (A : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) :
    (p : ℕ) → Matrix (PowerIndex N p) (PowerIndex N p) ℂ
  | 0 => 1
  | p+1 => tensorPower A p ⊗ₖ A

theorem tensorPower_mul (A B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (p : ℕ) :
    tensorPower (A*B) p = tensorPower A p * tensorPower B p := by
  induction p with
  | zero => simp [tensorPower]
  | succ p ih => simp only [tensorPower, ih, Matrix.mul_kronecker_mul]

theorem tensorPower_conjTranspose (A : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (p : ℕ) :
    tensorPower Aᴴ p = (tensorPower A p)ᴴ := by
  induction p with
  | zero => simp [tensorPower]
  | succ p ih =>
    simp only [tensorPower, ih]
    exact (Matrix.conjTranspose_kronecker _ _).symm

theorem continuous_tensorPower (p : ℕ) :
    Continuous (fun A : Matrix (Fin (N+1)) (Fin (N+1)) ℂ => tensorPower A p) := by
  induction p with
  | zero => exact continuous_const
  | succ p ih =>
    apply continuous_matrix
    intro i j
    change Continuous (fun A => tensorPower A p i.1 j.1 * A i.2 j.2)
    exact (ih.matrix_elem _ _).mul (continuous_id.matrix_elem _ _)

/-- The concrete representation whose entries are arbitrary mixed Haar moments. -/
def mixedTensor (p q : ℕ) (U : LocalUnitary N) :
    Matrix (PowerIndex N p × PowerIndex N q) (PowerIndex N p × PowerIndex N q) ℂ :=
  tensorPower (U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) p ⊗ₖ
    tensorPower ((U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ).map (starRingEnd ℂ)) q

theorem mixedTensor_mul (p q : ℕ) (U V : LocalUnitary N) :
    mixedTensor p q (U*V) = mixedTensor p q U * mixedTensor p q V := by
  unfold mixedTensor
  change tensorPower ((U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) * (V : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)) p ⊗ₖ
    tensorPower (((U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) * (V : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)).map (starRingEnd ℂ)) q = _
  rw [Matrix.map_mul, tensorPower_mul, tensorPower_mul, Matrix.mul_kronecker_mul]

theorem mixedTensor_inv (p q : ℕ) (U : LocalUnitary N) :
    mixedTensor p q U⁻¹ = (mixedTensor p q U)ᴴ := by
  have hu : ((U⁻¹ : LocalUnitary N) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) =
      (U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)ᴴ := rfl
  have hc : ((U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)ᴴ).map (starRingEnd ℂ) =
      ((U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ).map (starRingEnd ℂ))ᴴ := by
    ext i j
    simp
  simp only [mixedTensor, hu, hc, tensorPower_conjTranspose, Matrix.conjTranspose_kronecker]

theorem continuous_mixedTensor (p q : ℕ) : Continuous (mixedTensor (N := N) p q) := by
  have hc : Continuous (fun U : LocalUnitary N =>
      (U : Matrix (Fin (N+1)) (Fin (N+1)) ℂ).map (starRingEnd ℂ)) := by
    apply continuous_matrix
    intro i j
    exact (HaarMoments.continuous_entry i j).star
  apply continuous_matrix
  intro i j
  exact (((continuous_tensorPower p).comp continuous_subtype_val).matrix_elem i.1 j.1).mul
    (((continuous_tensorPower q).comp hc).matrix_elem i.2 j.2)

/-- Every mixed moment matrix, at arbitrary orders, is an idempotent. -/
theorem average_mixedTensor_sq (p q : ℕ) :
    average (mixedTensor (N := N) p q) * average (mixedTensor p q) =
      average (mixedTensor p q) :=
  average_sq _ (continuous_mixedTensor p q) (mixedTensor_mul p q)

/-- Every mixed moment matrix, at arbitrary orders, is Hermitian. -/
theorem average_mixedTensor_hermitian (p q : ℕ) :
    (average (mixedTensor (N := N) p q)).IsHermitian :=
  average_conjTranspose _ (mixedTensor_inv p q)

/-- The concrete arbitrary-degree Haar moment matrix projects onto invariant tensors. -/
theorem average_mixedTensor_mulVec_eq_iff (p q : ℕ)
    (v : PowerIndex N p × PowerIndex N q → ℂ) :
    average (mixedTensor p q) *ᵥ v = v ↔ ∀ U : LocalUnitary N, mixedTensor p q U *ᵥ v = v :=
  average_mulVec_eq_iff _ (continuous_mixedTensor p q) (mixedTensor_mul p q) v

end TensorPowers

end Nonadditivity.HaarAveraging

