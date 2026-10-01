/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingPackingAverages
import Nonadditivity.QuantumCodingConditionalTypicality

/-! # Simultaneous global and conditional quantum typicality

These estimates concern actual product output states and actual projectors.
Both lost probability and independently averaged test interference are
proved explicitly. The interference exponent is the ensemble's Holevo
information minus twice the tolerance.
-/

noncomputable section
namespace Nonadditivity.QuantumCoding

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

def ensembleConditionalEntropy (p : α → ℝ) (ρ : α → DensityMatrix ι) : ℝ :=
  ∑ a, p a * (ρ a).vonNeumann

def ensembleConditionalVariance (p : α → ℝ) (ρ : α → DensityMatrix ι) : ℝ :=
  QuantumCodingConditionalTypicality.conditionalVariance p (fun a => (ρ a).weights)

def conditionalTypicalProjector (p : α → ℝ) (ρ : α → DensityMatrix ι)
    (n : ℕ) (δ : ℝ) (x : Fin n → α) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  tensorFamilyBandProjector (fun j => ρ (x j))
    ((n : ℝ) * ensembleConditionalEntropy p ρ) ((n : ℝ) * δ)

theorem conditionalTypicalProjector_posSemidef (p : α → ℝ) (ρ : α → DensityMatrix ι)
    (n : ℕ) (δ : ℝ) (x : Fin n → α) :
    (conditionalTypicalProjector p ρ n δ x).PosSemidef :=
  tensorFamilyBandProjector_posSemidef _ _ _

theorem conditionalTypicalProjector_idempotent (p : α → ℝ) (ρ : α → DensityMatrix ι)
    (n : ℕ) (δ : ℝ) (x : Fin n → α) :
    conditionalTypicalProjector p ρ n δ x * conditionalTypicalProjector p ρ n δ x =
      conditionalTypicalProjector p ρ n δ x :=
  tensorFamilyBandProjector_idempotent _ _ _

theorem conditionalTypicalProjector_trace_bound (p : α → ℝ) (ρ : α → DensityMatrix ι)
    (n : ℕ) (δ : ℝ) (x : Fin n → α) :
    (conditionalTypicalProjector p ρ n δ x).trace.re ≤
      Real.exp ((n : ℝ) * ensembleConditionalEntropy p ρ + (n : ℝ) * δ) :=
  tensorFamilyBandProjector_trace_bound _ _ _

/-- Conditional subspaces accept the actual ensemble word states with a
proved vanishing average error. -/
theorem conditionalTypicalProjector_average_acceptance_ge (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    1 - ensembleConditionalVariance p ρ / ((n : ℝ) * δ ^ 2) ≤
      ∑ x : Fin n → α, tensorWeights p n x *
        ((tensorFamilyState (fun j => ρ (x j))).matrix *
          conditionalTypicalProjector p ρ n δ x).trace.re := by
  simp only [conditionalTypicalProjector, tensorFamilyBandProjector_acceptance]
  exact QuantumCodingConditionalTypicality.average_conditional_band_mass_ge
    p (fun a => (ρ a).weights) hp hs (fun a => (ρ a).weights_nonneg)
      (fun a => (ρ a).weights_sum) n hn δ hδ

theorem tensorState_average_acceptance (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι) (n : ℕ)
    (P : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    (∑ x : Fin n → α, tensorWeights p n x *
      ((tensorFamilyState (fun j => ρ (x j))).matrix * P).trace.re) =
        ((tensorState (DensityMatrix.mixture p hp hs ρ) n).matrix * P).trace.re := by
  rw [tensorState_mixture_matrix]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The global typical subspace accepts the same actual word ensemble. -/
theorem globalTypicalProjector_average_acceptance_ge (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    1 - QuantumCodingTypicality.variance (DensityMatrix.mixture p hp hs ρ).weights /
        ((n : ℝ) * δ ^ 2) ≤
      ∑ x : Fin n → α, tensorWeights p n x *
        ((tensorFamilyState (fun j => ρ (x j))).matrix *
          tensorTypicalProjector (DensityMatrix.mixture p hp hs ρ) n δ).trace.re := by
  rw [tensorState_average_acceptance]
  exact tensorTypicalProjector_acceptance_ge _ hn hδ

/-- The exact one-shot interference estimate needed for random coding.
Its exponential rate is the actual finite ensemble Holevo information. -/
theorem typicalProjectors_average_cross_le (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    (n : ℕ) (δ : ℝ) :
    let σ := DensityMatrix.mixture p hp hs ρ
    let P := tensorTypicalProjector σ n δ
    (∑ y : Fin n → α, ∑ x : Fin n → α,
      tensorWeights p n y * tensorWeights p n x *
      (conditionalTypicalProjector p ρ n δ y * P *
        (tensorFamilyState (fun j => ρ (x j))).matrix * P).trace.re) ≤
      Real.exp (-(n : ℝ) * (σ.vonNeumann - ensembleConditionalEntropy p ρ - 2 * δ)) := by
  dsimp only
  let σ := DensityMatrix.mixture p hp hs ρ
  let P := tensorTypicalProjector σ n δ
  let a := Real.exp (-(n : ℝ) * (σ.vonNeumann - δ))
  let b := Real.exp ((n : ℝ) * ensembleConditionalEntropy p ρ + (n : ℝ) * δ)
  have hcap : ((a : ℂ) • (1 : Matrix (Fin n → ι) (Fin n → ι) ℂ) -
      P * (tensorState σ n).matrix * P).PosSemidef :=
    compression_cap_identity P _ (Real.exp_nonneg _) (tensorTypicalProjector_le_one σ n δ)
      (tensorTypicalProjector_compression_le σ n δ)
  have hmix : (DensityMatrix.mixture (tensorWeights p n)
      (tensorWeights_nonneg p hp n) (tensorWeights_sum p hs n)
      (fun x => tensorFamilyState (fun j => ρ (x j)))).matrix = (tensorState σ n).matrix :=
    (tensorState_mixture_matrix p hp hs ρ n).symm
  have h := average_cross_trace_le (tensorWeights p n) (tensorWeights_nonneg p hp n)
    (tensorWeights_sum p hs n) (fun x => tensorFamilyState (fun j => ρ (x j))) P
    (conditionalTypicalProjector p ρ n δ) (conditionalTypicalProjector_posSemidef p ρ n δ)
    (a := a) (b := b) (Real.exp_nonneg _)
    (conditionalTypicalProjector_trace_bound p ρ n δ) (by rw [hmix]; exact hcap)
  have hab : a * b =
      Real.exp (-(n : ℝ) * (σ.vonNeumann - ensembleConditionalEntropy p ρ - 2 * δ)) := by
    dsimp [a, b]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hab] at h
  exact h

end Nonadditivity.QuantumCoding
