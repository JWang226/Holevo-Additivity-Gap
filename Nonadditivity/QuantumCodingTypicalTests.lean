/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingEnsembleTypicality
import Nonadditivity.QuantumCodingSequential

/-! # Typical subspaces as physical projective tests

This interface supplies the actual global and word-dependent tests used by
the sequential decoder, with unconditional finite-ensemble estimates.
-/

noncomputable section
namespace Nonadditivity.QuantumCoding

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

def globalTypicalTest (σ : DensityMatrix ι) (n : ℕ) (δ : ℝ) :
    ProjectiveTest (Fin n → ι) where
  matrix := tensorTypicalProjector σ n δ
  hermitian := (tensorTypicalProjector_posSemidef σ n δ).isHermitian
  idempotent := tensorTypicalProjector_idempotent σ n δ

def conditionalTypicalTest (p : α → ℝ) (ρ : α → DensityMatrix ι)
    (n : ℕ) (δ : ℝ) (x : Fin n → α) : ProjectiveTest (Fin n → ι) where
  matrix := conditionalTypicalProjector p ρ n δ x
  hermitian := (conditionalTypicalProjector_posSemidef p ρ n δ x).isHermitian
  idempotent := conditionalTypicalProjector_idempotent p ρ n δ x

theorem weighted_rejection_eq (p : α → ℝ) (hs : ∑ a, p a = 1)
    (ρ : α → DensityMatrix ι) (P : α → Matrix ι ι ℂ) :
    (∑ a, p a * ((1 - P a) * (ρ a).matrix).trace.re) =
      1 - ∑ a, p a * ((ρ a).matrix * P a).trace.re := by
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    DensityMatrix.normalized, Complex.one_re, mul_sub, mul_one,
    Finset.sum_sub_distrib, hs]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.trace_mul_comm]

theorem conditionalTypicalTest_mean_rejection_le (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ x : Fin n → α, tensorWeights p n x *
      ((1 - (conditionalTypicalTest p ρ n δ x).matrix) *
        (tensorFamilyState (fun j => ρ (x j))).matrix).trace.re) ≤
      ensembleConditionalVariance p ρ / ((n : ℝ) * δ ^ 2) := by
  rw [weighted_rejection_eq (tensorWeights p n) (tensorWeights_sum p hs n)]
  have h := conditionalTypicalProjector_average_acceptance_ge p hp hs ρ hn hδ
  simp only [conditionalTypicalTest]
  linarith

theorem globalTypicalTest_mean_rejection_le (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ x : Fin n → α, tensorWeights p n x *
      ((1 - (globalTypicalTest (DensityMatrix.mixture p hp hs ρ) n δ).matrix) *
        (tensorFamilyState (fun j => ρ (x j))).matrix).trace.re) ≤
      QuantumCodingTypicality.variance (DensityMatrix.mixture p hp hs ρ).weights /
        ((n : ℝ) * δ ^ 2) := by
  rw [weighted_rejection_eq (tensorWeights p n) (tensorWeights_sum p hs n)]
  have h := globalTypicalProjector_average_acceptance_ge p hp hs ρ hn hδ
  simp only [globalTypicalTest]
  linarith

end Nonadditivity.QuantumCoding
