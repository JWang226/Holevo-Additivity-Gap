/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FiniteRealization
import Nonadditivity.QuantitativeNet
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Exact real dimension of traceless Hermitian observables

The imaginary-part map and real trace give two rank-nullity identities.
No explicit choice of a Hermitian basis is required.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.ObservableDimension

open scoped BigOperators
open FiniteRealization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Hermitian matrices have exactly one real parameter per complex matrix entry. -/
theorem selfAdjoint_matrix_finrank :
    Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) = Fintype.card ι ^ 2 := by
  have h := (imaginaryPart (A := Matrix ι ι ℂ)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr imaginaryPart_surjective, finrank_top,
    ker_imaginaryPart] at h
  change Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) +
    Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) = _ at h
  rw [Module.finrank_matrix, Complex.finrank_real_complex] at h
  simp only [pow_two]
  omega

instance selfAdjoint_matrix_finiteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  FiniteDimensional.of_surjective (imaginaryPart (A := Matrix ι ι ℂ))
    imaginaryPart_surjective

/-- Real trace restricted to actual self-adjoint matrices. -/
def hermitianTrace : selfAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace (A : Matrix ι ι ℂ)).re
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' r A := by simp [Matrix.trace_smul]

omit [DecidableEq ι] in
@[simp] theorem hermitianTrace_apply (A : selfAdjoint (Matrix ι ι ℂ)) :
    hermitianTrace A = (Matrix.trace (A : Matrix ι ι ℂ)).re := rfl

omit [DecidableEq ι] in
theorem hermitian_trace_im (A : selfAdjoint (Matrix ι ι ℂ)) :
    (Matrix.trace (A : Matrix ι ι ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (Matrix.trace (A : Matrix ι ι ℂ)) = _
  rw [← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose]
  exact congrArg Matrix.trace A.property

/-- A single real diagonal entry realizes any prescribed trace. -/
theorem hermitianTrace_surjective [Nonempty ι] :
    Function.Surjective (hermitianTrace (ι := ι)) := by
  classical
  intro r
  let i : ι := Classical.arbitrary ι
  let A : Matrix ι ι ℂ := Matrix.diagonal (fun j => if j = i then (r : ℂ) else 0)
  have hA : IsSelfAdjoint A := by
    change (Matrix.diagonal (fun j => if j = i then (r : ℂ) else 0)).IsHermitian
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro j
    split_ifs <;> simp [IsSelfAdjoint]
  refine ⟨⟨A, hA⟩, ?_⟩
  simp [hermitianTrace, A, Matrix.trace, Matrix.diag, apply_ite]

/-- The Euclidean entry model of observables is exactly the kernel of real
trace on the Hermitian matrices. -/
def observableEquivTraceKernel : ObservableSpace ι ≃ₗ[ℝ]
    LinearMap.ker (hermitianTrace (ι := ι)) where
  toFun x := ⟨⟨entriesToMatrix x.val, x.property.1⟩, by
    change (Matrix.trace (entriesToMatrix x.val)).re = 0
    rw [x.property.2]
    rfl⟩
  invFun x := ⟨matrixToEntries (x.val : Matrix ι ι ℂ), by
    constructor
    · exact x.val.property
    · apply Complex.ext
      · exact x.property
      · exact hermitian_trace_im x.val⟩
  left_inv x := by ext i; rfl
  right_inv x := by ext i j; rfl
  map_add' x y := by ext i j; rfl
  map_smul' r x := by ext i j; rfl

/-- The manuscript's exact exponent: a nonempty `d×d` traceless Hermitian
observable space has real dimension `d²−1`. -/
theorem observableSpace_finrank [Nonempty ι] :
    Module.finrank ℝ (ObservableSpace ι) = Fintype.card ι ^ 2 - 1 := by
  rw [observableEquivTraceKernel.finrank_eq]
  have h := (hermitianTrace (ι := ι)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hermitianTrace_surjective, finrank_top,
    Module.finrank_self, selfAdjoint_matrix_finrank] at h
  omega

/-- The sharp inverse-natural-radius net in the actual Hilbert--Schmidt
observable sphere, including any prescribed test and its negative. -/
theorem exists_symmetric_observable_net [Nonempty ι]
    (a : ObservableSpace ι) (ha : ‖a‖ = 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ tests : Finset (ObservableSpace ι), a ∈ tests ∧ -a ∈ tests ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      (∀ x ∈ tests, ∀ y ∈ tests, x ≠ y → 1 / (n : ℝ) < dist x y) ∧
      UnitSphereNet tests (1 / (n : ℝ)) ∧
      (tests.card : ℝ) ≤ (1 + 2 * (n : ℝ)) ^ (Fintype.card ι ^ 2 - 1) := by
  simpa only [observableSpace_finrank] using
    QuantitativeNet.exists_symmetric_inverse_nat_net a ha n hn

/-- Matrix-form entry point: Hermiticity, zero trace and unit HS length
produce the exact-cardinality net with this matrix included. -/
theorem exists_symmetric_observable_net_for_matrix [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (htrace : A.trace = 0)
    (hhs : AdjointPurity.hsLength A = 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ tests : Finset (ObservableSpace ι), matrixObservable A hA htrace ∈ tests ∧
      -matrixObservable A hA htrace ∈ tests ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      (∀ x ∈ tests, ∀ y ∈ tests, x ≠ y → 1 / (n : ℝ) < dist x y) ∧
      UnitSphereNet tests (1 / (n : ℝ)) ∧
      (tests.card : ℝ) ≤ (1 + 2 * (n : ℝ)) ^ (Fintype.card ι ^ 2 - 1) := by
  apply exists_symmetric_observable_net _ _ n hn
  rw [observable_norm_eq_hsLength, observableMatrix_matrixObservable]
  exact hhs

end Nonadditivity.ObservableDimension
