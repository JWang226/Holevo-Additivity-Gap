/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingTensorSpectrum
import Nonadditivity.QuantumCodingFamilySpectrum
import Nonadditivity.QuantumCodingTypicality

/-! # Quantum typical subspaces with explicit error and size bounds

The projectors act on the actual tensor-product state. The concentration
estimate is proved for the eigenvalue product distribution and transferred
through the actual tensor diagonalization.
-/

noncomputable section

namespace Nonadditivity.QuantumCoding

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability of the genuine typical subspace is at least the iid
Chebyshev bound, with no typicality hypothesis. -/
theorem tensorTypicalProjector_acceptance_ge (ρ : DensityMatrix ι) {n : ℕ}
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    1 - QuantumCodingTypicality.variance ρ.weights / ((n : ℝ) * δ ^ 2) ≤
      ((tensorState ρ n).matrix * tensorTypicalProjector ρ n δ).trace.re := by
  rw [tensorTypicalProjector_acceptance]
  have h := QuantumCodingTypicality.spectral_band_mass_ge ρ.weights
    ρ.weights_nonneg ρ.weights_sum n hn δ hδ
  have hlow : -(n : ℝ) * (ρ.vonNeumann + δ) =
      -((n : ℝ) * QuantumCodingTypicality.entropy ρ.weights) - (n : ℝ) * δ := by
    change -(n : ℝ) * (shannon ρ.weights + δ) =
      -((n : ℝ) * shannon ρ.weights) - (n : ℝ) * δ
    ring
  have hhigh : -(n : ℝ) * (ρ.vonNeumann - δ) =
      -((n : ℝ) * QuantumCodingTypicality.entropy ρ.weights) + (n : ℝ) * δ := by
    change -(n : ℝ) * (shannon ρ.weights - δ) =
      -((n : ℝ) * shannon ρ.weights) + (n : ℝ) * δ
    ring
  rw [hlow, hhigh]
  exact h

/-- The same spectral construction applies to varying letters; the band
center is shared by all words of an ensemble. -/
def tensorFamilyBandProjector {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  spectralProjector (tensorFamilyUnitary (fun j => (ρ j).positive.isHermitian.eigenvectorUnitary))
    (spectralBand (tensorFamilyWeights (fun j => (ρ j).weights))
      (Real.exp (-s - a)) (Real.exp (-s + a)))

theorem tensorFamilyBandProjector_idempotent {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) :
    tensorFamilyBandProjector ρ s a * tensorFamilyBandProjector ρ s a =
      tensorFamilyBandProjector ρ s a := spectralProjector_idempotent _ _

theorem tensorFamilyBandProjector_posSemidef {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) : (tensorFamilyBandProjector ρ s a).PosSemidef :=
  spectralProjector_posSemidef _ _

theorem tensorFamilyBandProjector_le_one {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) : (1 - tensorFamilyBandProjector ρ s a).PosSemidef :=
  spectralProjector_le_one _ _

theorem tensorFamilyBandProjector_trace_bound {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) : (tensorFamilyBandProjector ρ s a).trace.re ≤ Real.exp (s + a) := by
  rw [tensorFamilyBandProjector, spectralProjector_trace, Complex.natCast_re]
  have h := spectralBand_card (tensorFamilyWeights (fun j => (ρ j).weights))
    (tensorFamilyWeights_nonneg _ (fun j => (ρ j).weights_nonneg))
    (tensorFamilyWeights_sum _ (fun j => (ρ j).weights_sum))
    (hi := Real.exp (-s + a)) (Real.exp_pos (-s - a))
  convert h using 1
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

theorem tensorFamilyBandProjector_compression_le {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) :
    ((Real.exp (-s + a) : ℂ) • tensorFamilyBandProjector ρ s a -
      tensorFamilyBandProjector ρ s a * (tensorFamilyState ρ).matrix *
        tensorFamilyBandProjector ρ s a).PosSemidef := by
  change (_ - _ * tensorFamilyMatrix (fun j => (ρ j).matrix) * _).PosSemidef
  rw [tensorFamilyMatrix_diagonalization]
  exact spectralBand_compression_le _ _ _ _

theorem tensorFamilyBandProjector_acceptance {n : ℕ} (ρ : Fin n → DensityMatrix ι)
    (s a : ℝ) :
    ((tensorFamilyState ρ).matrix * tensorFamilyBandProjector ρ s a).trace.re =
      ∑ x ∈ spectralBand (tensorFamilyWeights (fun j => (ρ j).weights))
        (Real.exp (-s - a)) (Real.exp (-s + a)),
        tensorFamilyWeights (fun j => (ρ j).weights) x := by
  change (tensorFamilyMatrix (fun j => (ρ j).matrix) * _).trace.re = _
  rw [tensorFamilyMatrix_diagonalization]
  exact spectralProjector_acceptance _ _ _

end Nonadditivity.QuantumCoding
