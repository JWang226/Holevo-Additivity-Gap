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

def tensorMatrix (A : Matrix ι ι ℂ) (n : ℕ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ := fun x y => ∏ j, A (x j) (y j)

omit [DecidableEq ι] in
theorem tensorMatrix_mul (A B : Matrix ι ι ℂ) (n : ℕ) :
    tensorMatrix (A * B) n = tensorMatrix A n * tensorMatrix B n := by
  ext x y
  simp only [tensorMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

omit [Fintype ι] [DecidableEq ι] in
theorem tensorMatrix_star (A : Matrix ι ι ℂ) (n : ℕ) :
    tensorMatrix (star A) n = star (tensorMatrix A n) := by
  ext x y
  simp [tensorMatrix, Matrix.star_apply]

omit [Fintype ι] in
theorem tensorMatrix_diagonal (p : ι → ℂ) (n : ℕ) :
    tensorMatrix (Matrix.diagonal p) n = Matrix.diagonal (fun x => ∏ j, p (x j)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorMatrix]
  · have hj : ∃ j, x j ≠ y j := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨j, hj⟩ := hj
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ hj

omit [Fintype ι] in
theorem tensorMatrix_one (n : ℕ) : tensorMatrix (1 : Matrix ι ι ℂ) n = 1 := by
  rw [← Matrix.diagonal_one, tensorMatrix_diagonal]
  simp

def tensorPowerUnitary (U : unitary (Matrix ι ι ℂ)) (n : ℕ) :
    unitary (Matrix (Fin n → ι) (Fin n → ι) ℂ) :=
  ⟨tensorMatrix U n, by
    rw [Unitary.mem_iff]
    constructor
    · rw [← tensorMatrix_star, ← tensorMatrix_mul, Unitary.coe_star_mul_self,
        tensorMatrix_one]
    · rw [← tensorMatrix_star, ← tensorMatrix_mul]
      have h : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 :=
        Unitary.coe_mul_star_self U
      rw [h, tensorMatrix_one]⟩

def tensorWeights (p : ι → ℝ) (n : ℕ) (x : Fin n → ι) : ℝ := ∏ j, p (x j)

theorem tensorMatrix_diagonalization (ρ : DensityMatrix ι) (n : ℕ) :
    tensorMatrix ρ.matrix n =
      Unitary.conjStarAlgAut ℂ _
        (tensorPowerUnitary ρ.positive.isHermitian.eigenvectorUnitary n)
        (Matrix.diagonal (fun x => (tensorWeights ρ.weights n x : ℂ))) := by
  conv_lhs => rw [ρ.positive.isHermitian.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply,
    tensorMatrix_mul, tensorMatrix_mul, tensorMatrix_diagonal, tensorMatrix_star,
    Unitary.conjStarAlgAut_apply]
  simp only [tensorPowerUnitary, tensorWeights, Complex.ofReal_prod]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem tensorWeights_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (n : ℕ)
    (x : Fin n → ι) : 0 ≤ tensorWeights p n x :=
  Finset.prod_nonneg fun i _ => hp (x i)

omit [DecidableEq ι] in
theorem tensorWeights_sum (p : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    ∑ x, tensorWeights p n x = 1 := by
  unfold tensorWeights
  rw [← Fintype.prod_sum]
  simp [hp]

/-- Actual product matrix state, with positivity proved by diagonalization. -/
def tensorState (ρ : DensityMatrix ι) (n : ℕ) : DensityMatrix (Fin n → ι) where
  matrix := tensorMatrix ρ.matrix n
  positive := by
    rw [tensorMatrix_diagonalization]
    exact unitaryDiagonal_posSemidef _ _ (tensorWeights_nonneg _ ρ.weights_nonneg n)
  normalized := by
    rw [tensorMatrix_diagonalization, unitaryDiagonal_trace, tensorWeights_sum _ ρ.weights_sum]
    simp

def tensorTypicalProjector (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  spectralProjector (tensorPowerUnitary ρ.positive.isHermitian.eigenvectorUnitary n)
    (spectralBand (tensorWeights ρ.weights n)
      (Real.exp (-(n : ℝ) * (ρ.vonNeumann + δ)))
      (Real.exp (-(n : ℝ) * (ρ.vonNeumann - δ))))

theorem tensorTypicalProjector_idempotent (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    tensorTypicalProjector ρ n δ * tensorTypicalProjector ρ n δ =
      tensorTypicalProjector ρ n δ := spectralProjector_idempotent _ _

theorem tensorTypicalProjector_posSemidef (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    (tensorTypicalProjector ρ n δ).PosSemidef := spectralProjector_posSemidef _ _

theorem tensorTypicalProjector_le_one (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    (1 - tensorTypicalProjector ρ n δ).PosSemidef := spectralProjector_le_one _ _

theorem tensorTypicalProjector_trace_bound (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    (tensorTypicalProjector ρ n δ).trace.re ≤ Real.exp ((n : ℝ) * (ρ.vonNeumann + δ)) := by
  rw [tensorTypicalProjector, spectralProjector_trace, Complex.natCast_re]
  have h := spectralBand_card (tensorWeights ρ.weights n)
    (tensorWeights_nonneg ρ.weights ρ.weights_nonneg n)
    (tensorWeights_sum ρ.weights ρ.weights_sum n)
    (hi := Real.exp (-(n : ℝ) * (ρ.vonNeumann - δ)))
    (Real.exp_pos (-(n : ℝ) * (ρ.vonNeumann + δ)))
  convert h using 1
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

theorem tensorTypicalProjector_compression_le (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    ((Real.exp (-(n : ℝ) * (ρ.vonNeumann - δ)) : ℂ) • tensorTypicalProjector ρ n δ -
      tensorTypicalProjector ρ n δ * (tensorState ρ n).matrix *
        tensorTypicalProjector ρ n δ).PosSemidef := by
  change (_ - _ * tensorMatrix ρ.matrix n * _).PosSemidef
  rw [tensorMatrix_diagonalization]
  exact spectralBand_compression_le _ _ _ _

theorem tensorTypicalProjector_acceptance (ρ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    ((tensorState ρ n).matrix * tensorTypicalProjector ρ n δ).trace.re =
      ∑ x ∈ spectralBand (tensorWeights ρ.weights n)
        (Real.exp (-(n : ℝ) * (ρ.vonNeumann + δ)))
        (Real.exp (-(n : ℝ) * (ρ.vonNeumann - δ))), tensorWeights ρ.weights n x := by
  change (tensorMatrix ρ.matrix n * _).trace.re = _
  rw [tensorMatrix_diagonalization]
  exact spectralProjector_acceptance _ _ _

end Nonadditivity.QuantumCoding
