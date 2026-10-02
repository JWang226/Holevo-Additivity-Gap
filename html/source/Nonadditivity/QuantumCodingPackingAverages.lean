/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingTypicalProjectors
import Nonadditivity.StateEnsembles
import Nonadditivity.AdjointPurity

/-! # The packing cross term for an actual finite quantum ensemble

The average tensor state is proved to be the mixture of the actual word
states. A spectral cap on its global compression and a trace bound on each
conditional projector give the required average interference bound.
-/

noncomputable section
namespace Nonadditivity.QuantumCoding

open Entropy AdjointPurity
open scoped BigOperators ComplexOrder Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Independent sampling of input letters gives the genuine tensor power
of the single-letter average, as an exact matrix identity. -/
theorem tensorState_mixture_matrix (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : α → DensityMatrix ι) (n : ℕ) :
    (tensorState (DensityMatrix.mixture p hp hs ρ) n).matrix =
      ∑ x : Fin n → α, (tensorWeights p n x : ℂ) •
        (tensorFamilyState (fun j => ρ (x j))).matrix := by
  ext u v
  change (∏ j, (∑ a, (p a : ℂ) • (ρ a).matrix) (u j) (v j)) = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ j, (p (x j) : ℂ) * (ρ (x j)).matrix (u j) (v j)) =
    (tensorWeights p n x : ℂ) * ∏ j, (ρ (x j)).matrix (u j) (v j)
  rw [Finset.prod_mul_distrib]
  simp only [tensorWeights, Complex.ofReal_prod]

/-- Lift a spectral cap relative to a projection to a cap by the identity. -/
theorem compression_cap_identity (P R : Matrix ι ι ℂ) {a : ℝ} (ha : 0 ≤ a)
    (hP : (1 - P).PosSemidef) (hcap : ((a : ℂ) • P - P * R * P).PosSemidef) :
    ((a : ℂ) • (1 : Matrix ι ι ℂ) - P * R * P).PosSemidef := by
  have h := (hP.smul (show (0 : ℂ) ≤ (a : ℂ) by exact_mod_cast ha)).add hcap
  convert h using 1
  simp only [smul_sub]
  abel

/-- Any positive test has interference at most its trace times the cap. -/
theorem compressed_trace_le (P R Q : Matrix ι ι ℂ) {a : ℝ}
    (hQ : Q.PosSemidef)
    (hcap : ((a : ℂ) • (1 : Matrix ι ι ℂ) - P * R * P).PosSemidef) :
    (Q * P * R * P).trace.re ≤ a * Q.trace.re := by
  have h : 0 ≤ (Q * ((a : ℂ) • (1 : Matrix ι ι ℂ) - P * R * P)).trace.re :=
    (RCLike.nonneg_iff.mp (trace_mul_nonneg hQ hcap)).1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  simpa only [Matrix.mul_assoc] using (sub_nonneg.mp h)

theorem weighted_compressed_trace (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : α → DensityMatrix ι) (P Q : Matrix ι ι ℂ) :
    (∑ x, p x * (Q * P * (ρ x).matrix * P).trace.re) =
      (Q * P * (DensityMatrix.mixture p hp hs ρ).matrix * P).trace.re := by
  simp only [DensityMatrix.mixture_matrix, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Independent average over the true state and an interfering test. -/
theorem average_cross_trace_le (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : α → DensityMatrix ι)
    (P : Matrix ι ι ℂ) (Q : α → Matrix ι ι ℂ) (hQ : ∀ x, (Q x).PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (htrace : ∀ x, (Q x).trace.re ≤ b)
    (hcap : ((a : ℂ) • (1 : Matrix ι ι ℂ) -
      P * (DensityMatrix.mixture p hp hs ρ).matrix * P).PosSemidef) :
    (∑ y, ∑ x, p y * p x * (Q y * P * (ρ x).matrix * P).trace.re) ≤ a * b := by
  calc
    _ = ∑ y, p y * (Q y * P * (DensityMatrix.mixture p hp hs ρ).matrix * P).trace.re := by
      apply Finset.sum_congr rfl
      intro y _
      have he (x : α) : p y * p x * (Q y * P * (ρ x).matrix * P).trace.re =
          p y * (p x * (Q y * P * (ρ x).matrix * P).trace.re) := mul_assoc _ _ _
      simp only [he, ← Finset.mul_sum]
      rw [weighted_compressed_trace]
    _ ≤ ∑ y, p y * (a * b) := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hp y)
      exact (compressed_trace_le P _ (Q y) (hQ y) hcap).trans
        (mul_le_mul_of_nonneg_left (htrace y) ha)
    _ = a * b := by rw [← Finset.sum_mul, hs, one_mul]

end Nonadditivity.QuantumCoding
