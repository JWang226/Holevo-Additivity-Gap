/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.EntropyProducts
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Actual spectral projectors for finite quantum coding

These are matrix projectors, formed in an arbitrary diagonalizing unitary,
with proved trace and semidefinite estimates. Their cutoffs are numerical
spectral bounds; no coding or typicality conclusion is assumed.
-/

noncomputable section

namespace Nonadditivity.QuantumCoding

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitaryDiagonal_posSemidef (U : unitary (Matrix ι ι ℂ))
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (p i : ℂ)))).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same (B := (U : Matrix ι ι ℂ))
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (p i : ℂ)
  exact_mod_cast hp i

theorem unitaryDiagonal_trace (U : unitary (Matrix ι ι ℂ)) (p : ι → ℝ) :
    (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (p i : ℂ)))).trace =
      ((∑ i, p i : ℝ) : ℂ) := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.trace_diagonal]
  simp

/-- Select a set of columns of an actual orthonormal eigenbasis. -/
def spectralProjector (U : unitary (Matrix ι ι ℂ)) (s : Finset ι) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => if i ∈ s then 1 else 0))

theorem spectralProjector_posSemidef (U : unitary (Matrix ι ι ℂ)) (s : Finset ι) :
    (spectralProjector U s).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    (B := (U : Matrix ι ι ℂ))
  apply Matrix.PosSemidef.diagonal
  intro i
  change 0 ≤ (if i ∈ s then (1 : ℂ) else 0)
  split_ifs <;> simp

theorem spectralProjector_idempotent (U : unitary (Matrix ι ι ℂ)) (s : Finset ι) :
    spectralProjector U s * spectralProjector U s = spectralProjector U s := by
  unfold spectralProjector
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  split_ifs <;> simp

theorem spectralProjector_trace (U : unitary (Matrix ι ι ℂ)) (s : Finset ι) :
    (spectralProjector U s).trace = (s.card : ℂ) := by
  rw [spectralProjector, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.trace_diagonal]
  simp

theorem spectralProjector_complement (U : unitary (Matrix ι ι ℂ)) (s : Finset ι) :
    1 - spectralProjector U s = spectralProjector U (Finset.univ \ s) := by
  unfold spectralProjector
  rw [← map_one (Unitary.conjStarAlgAut ℂ _ U), ← map_sub]
  congr 1
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  split_ifs <;> simp_all

theorem spectralProjector_le_one (U : unitary (Matrix ι ι ℂ)) (s : Finset ι) :
    (1 - spectralProjector U s).PosSemidef := by
  rw [spectralProjector_complement]
  exact spectralProjector_posSemidef _ _

/-- Compression in the eigenbasis is literally restriction of eigenvalues. -/
theorem spectralProjector_compress (U : unitary (Matrix ι ι ℂ)) (s : Finset ι)
    (p : ι → ℝ) :
    spectralProjector U s *
        Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (p i : ℂ))) *
        spectralProjector U s =
      Unitary.conjStarAlgAut ℂ _ U
        (Matrix.diagonal (fun i => if i ∈ s then (p i : ℂ) else 0)) := by
  unfold spectralProjector
  rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  split_ifs <;> simp

theorem spectralProjector_acceptance (U : unitary (Matrix ι ι ℂ)) (s : Finset ι)
    (p : ι → ℝ) :
    ((Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (p i : ℂ)))) *
      spectralProjector U s).trace.re = ∑ i ∈ s, p i := by
  unfold spectralProjector
  rw [← map_mul, Matrix.diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.trace_diagonal]
  simp

/-- The spectral band of an arbitrary probability list. -/
def spectralBand (p : ι → ℝ) (lo hi : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => lo ≤ p i ∧ p i ≤ hi)

omit [DecidableEq ι] in
theorem spectralBand_card (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {lo hi : ℝ} (hlo : 0 < lo) :
    ((spectralBand p lo hi).card : ℝ) ≤ 1 / lo := by
  have hsumlo : ((spectralBand p lo hi).card : ℝ) * lo ≤
      ∑ i ∈ spectralBand p lo hi, p i := by
    calc
      _ = ∑ _i ∈ spectralBand p lo hi, lo := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.1
  have hle : (∑ i ∈ spectralBand p lo hi, p i) ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_univ_sum_of_nonneg fun i => hp i
  exact (le_div_iff₀ hlo).mpr (hsumlo.trans hle)

/-- A spectral upper cutoff gives the operator inequality used for packing. -/
theorem spectralBand_compression_le (U : unitary (Matrix ι ι ℂ))
    (p : ι → ℝ) (lo hi : ℝ) :
    ((hi : ℂ) • spectralProjector U (spectralBand p lo hi) -
      spectralProjector U (spectralBand p lo hi) *
        Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (p i : ℂ))) *
        spectralProjector U (spectralBand p lo hi)).PosSemidef := by
  rw [spectralProjector_compress]
  unfold spectralProjector
  rw [← map_smul, ← map_sub]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    (B := (U : Matrix ι ι ℂ))
  rw [← Matrix.diagonal_smul, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · simp only [mul_one]
    exact_mod_cast sub_nonneg.mpr (Finset.mem_filter.mp h).2.2
  · simp

/-- The projector is built from the density matrix's actual spectral data. -/
def typicalProjector (ρ : DensityMatrix ι) (s a : ℝ) : Matrix ι ι ℂ :=
  spectralProjector ρ.positive.isHermitian.eigenvectorUnitary
    (spectralBand ρ.weights (Real.exp (-s - a)) (Real.exp (-s + a)))

theorem typicalProjector_trace_bound (ρ : DensityMatrix ι) (s a : ℝ) :
    (typicalProjector ρ s a).trace.re ≤ Real.exp (s + a) := by
  rw [typicalProjector, spectralProjector_trace, Complex.natCast_re]
  have h := spectralBand_card ρ.weights ρ.weights_nonneg ρ.weights_sum
    (hi := Real.exp (-s + a)) (Real.exp_pos (-s - a))
  convert h using 1
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

theorem typicalProjector_compression_le (ρ : DensityMatrix ι) (s a : ℝ) :
    ((Real.exp (-s + a) : ℂ) • typicalProjector ρ s a -
      typicalProjector ρ s a * ρ.matrix * typicalProjector ρ s a).PosSemidef := by
  rw [ρ.positive.isHermitian.spectral_theorem]
  exact spectralBand_compression_le _ _ _ _

end Nonadditivity.QuantumCoding
