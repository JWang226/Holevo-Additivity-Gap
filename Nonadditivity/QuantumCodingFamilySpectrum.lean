/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingSpectral
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The actual spectrum of a finite tensor power

Tensor powers here have the standard word basis `Fin n → ι`, and their matrix
entries are products of the original entries. Diagonalization is proved
entrywise, including the zero-fold tensor product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Nonadditivity.QuantumCoding

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorFamilyMatrix {n : ℕ} (A : Fin n → Matrix ι ι ℂ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ := fun x y => ∏ j, A j (x j) (y j)

omit [DecidableEq ι] in
theorem tensorFamilyMatrix_mul {n : ℕ} (A B : Fin n → Matrix ι ι ℂ) :
    tensorFamilyMatrix (fun j => A j * B j) = tensorFamilyMatrix A * tensorFamilyMatrix B := by
  ext x y
  simp only [tensorFamilyMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

omit [Fintype ι] [DecidableEq ι] in
theorem tensorFamilyMatrix_star {n : ℕ} (A : Fin n → Matrix ι ι ℂ) :
    tensorFamilyMatrix (fun j => star (A j)) = star (tensorFamilyMatrix A) := by
  ext x y
  simp [tensorFamilyMatrix, Matrix.star_apply]

omit [Fintype ι] in
theorem tensorFamilyMatrix_diagonal {n : ℕ} (p : Fin n → ι → ℂ) :
    tensorFamilyMatrix (fun j => Matrix.diagonal (p j)) = Matrix.diagonal (fun x => ∏ j, p j (x j)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorFamilyMatrix]
  · have hj : ∃ j, x j ≠ y j := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨j, hj⟩ := hj
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ hj

omit [Fintype ι] in
theorem tensorFamilyMatrix_one (n : ℕ) : tensorFamilyMatrix (n := n) (fun _ => (1 : Matrix ι ι ℂ)) = 1 := by
  rw [← Matrix.diagonal_one, tensorFamilyMatrix_diagonal]
  simp

def tensorFamilyUnitary {n : ℕ} (U : Fin n → unitary (Matrix ι ι ℂ)) :
    unitary (Matrix (Fin n → ι) (Fin n → ι) ℂ) :=
  ⟨tensorFamilyMatrix (fun j => (U j : Matrix ι ι ℂ)), by
    rw [Unitary.mem_iff]
    constructor
    · rw [← tensorFamilyMatrix_star, ← tensorFamilyMatrix_mul]
      simp only [Unitary.coe_star_mul_self]
      exact tensorFamilyMatrix_one n
    · rw [← tensorFamilyMatrix_star, ← tensorFamilyMatrix_mul]
      have h : (fun j => (U j : Matrix ι ι ℂ) * star (U j : Matrix ι ι ℂ)) =
          (fun _ => 1) := by
        funext j
        exact Unitary.coe_mul_star_self (U j)
      rw [h, tensorFamilyMatrix_one]⟩

def tensorFamilyWeights {n : ℕ} (p : Fin n → ι → ℝ) (x : Fin n → ι) : ℝ := ∏ j, p j (x j)

theorem tensorFamilyMatrix_diagonalization {n : ℕ} (ρ : Fin n → DensityMatrix ι) :
    tensorFamilyMatrix (fun j => (ρ j).matrix) =
      Unitary.conjStarAlgAut ℂ _
        (tensorFamilyUnitary (fun j => (ρ j).positive.isHermitian.eigenvectorUnitary))
        (Matrix.diagonal (fun x => (tensorFamilyWeights (fun j => (ρ j).weights) x : ℂ))) := by
  have hs : (fun j => (ρ j).matrix) = fun j =>
      Unitary.conjStarAlgAut ℂ _ (ρ j).positive.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (fun i => ((ρ j).weights i : ℂ))) := by
    funext j
    exact (ρ j).positive.isHermitian.spectral_theorem
  rw [hs]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [tensorFamilyMatrix_mul, tensorFamilyMatrix_mul, tensorFamilyMatrix_diagonal,
    tensorFamilyMatrix_star]
  simp only [tensorFamilyUnitary, tensorFamilyWeights, Complex.ofReal_prod]

omit [Fintype ι] [DecidableEq ι] in
theorem tensorFamilyWeights_nonneg {n : ℕ} (p : Fin n → ι → ℝ) (hp : ∀ j i, 0 ≤ p j i)
    (x : Fin n → ι) : 0 ≤ tensorFamilyWeights p x :=
  Finset.prod_nonneg fun i _ => hp i (x i)

omit [DecidableEq ι] in
theorem tensorFamilyWeights_sum {n : ℕ} (p : Fin n → ι → ℝ) (hp : ∀ j, ∑ i, p j i = 1) :
    ∑ x, tensorFamilyWeights p x = 1 := by
  unfold tensorFamilyWeights
  rw [← Fintype.prod_sum]
  simp [hp]

/-- Actual product matrix state, with positivity proved by diagonalization. -/
def tensorFamilyState {n : ℕ} (ρ : Fin n → DensityMatrix ι) : DensityMatrix (Fin n → ι) where
  matrix := tensorFamilyMatrix (fun j => (ρ j).matrix)
  positive := by
    rw [tensorFamilyMatrix_diagonalization]
    exact unitaryDiagonal_posSemidef _ _ (tensorFamilyWeights_nonneg _
      (fun j => (ρ j).weights_nonneg))
  normalized := by
    rw [tensorFamilyMatrix_diagonalization, unitaryDiagonal_trace,
      tensorFamilyWeights_sum _ (fun j => (ρ j).weights_sum)]
    simp


end Nonadditivity.QuantumCoding
