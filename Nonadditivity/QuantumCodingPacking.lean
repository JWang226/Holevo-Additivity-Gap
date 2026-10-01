/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingSampling
import Nonadditivity.QuantumCodingSequential
import Nonadditivity.QuantumCodingDecoderBound

/-! # Finite random packing with actual projective quantum decoders -/

noncomputable section
namespace Nonadditivity.QuantumCoding
open Entropy Operational
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Cross acceptance of a competing conditional projector after the global filter. -/
def crossAcceptance (G Q : ProjectiveTest ι) (ρ : DensityMatrix ι) : ℝ :=
  (Q.matrix * (G.matrix * ρ.matrix * G.matrix)).trace.re

theorem crossAcceptance_nonneg (G Q : ProjectiveTest ι) (ρ : DensityMatrix ι) :
    0 ≤ crossAcceptance G Q ρ := by
  apply (RCLike.nonneg_iff.mp (AdjointPurity.trace_mul_nonneg Q.positive ?_)).1
  simpa only [G.hermitian.eq] using ρ.positive.conjTranspose_mul_mul_same G.matrix

/-- The global spectral ceiling and conditional rank bound control every
independent competing projector's acceptance of the average state. -/
theorem crossAcceptance_le (G Q : ProjectiveTest ι) (ρ : DensityMatrix ι)
    {a b : ℝ} (ha : 0 ≤ a)
    (hflat : ((a : ℂ) • G.matrix - G.matrix * ρ.matrix * G.matrix).PosSemidef)
    (hrank : Q.matrix.trace.re ≤ b) : crossAcceptance G Q ρ ≤ a*b := by
  have h₁ : 0 ≤ (Q.matrix * ((a : ℂ) • G.matrix - G.matrix * ρ.matrix * G.matrix)).trace.re :=
    (RCLike.nonneg_iff.mp (AdjointPurity.trace_mul_nonneg Q.positive hflat)).1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h₁
  have h₂ := (RCLike.nonneg_iff.mp
    (AdjointPurity.trace_mul_nonneg Q.positive G.complement.positive)).1
  change 0 ≤ (Q.matrix * (1-G.matrix)).trace.re at h₂
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h₂
  have h₃ := mul_le_mul_of_nonneg_left (show (Q.matrix*G.matrix).trace.re ≤ b by linarith) ha
  unfold crossAcceptance
  linarith

theorem mean_crossAcceptance (G Q : ProjectiveTest ι)
    (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    (ρ : α → DensityMatrix ι) :
    (∑x, p x * crossAcceptance G Q (ρ x)) =
      crossAcceptance G Q (DensityMatrix.mixture p hp hsum ρ) := by
  simp only [crossAcceptance, DensityMatrix.mixture_matrix, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum,
    Matrix.trace_smul, Complex.re_sum, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Exact independent codebook averaging reduces every distinct-message
interference term to the average output state's spectral ceiling. -/
theorem expected_crossAcceptance_le {J : Type*} [Fintype J] [DecidableEq J]
    (G : ProjectiveTest ι) (Q : α → ProjectiveTest ι)
    (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    (ρ : α → DensityMatrix ι) {a b : ℝ} (ha : 0 ≤ a)
    (hflat : ((a : ℂ) • G.matrix - G.matrix *
      (DensityMatrix.mixture p hp hsum ρ).matrix * G.matrix).PosSemidef)
    (hrank : ∀x, (Q x).matrix.trace.re ≤ b) {i j : J} (hij : i ≠ j) :
    Sampling.expect p (fun c : J → α => crossAcceptance G (Q (c j)) (ρ (c i))) ≤ a*b := by
  rw [Sampling.expect_two p hsum hij (fun x y => crossAcceptance G (Q y) (ρ x))]
  rw [Finset.sum_comm]
  calc
    (∑y, ∑x, p x * p y * crossAcceptance G (Q y) (ρ x)) =
        ∑y, p y * crossAcceptance G (Q y) (DensityMatrix.mixture p hp hsum ρ) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← mean_crossAcceptance]
      simp only [Finset.mul_sum]
      congr 1
      funext x
      ring
    _ ≤ ∑y, p y * (a*b) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (crossAcceptance_le G (Q y) _ ha hflat (hrank y)) (hp y)
    _ = a*b := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The physical decoder associated with one sampled codebook. -/
def packedDecoder {M : ℕ} (hM : 0 < M) (G : ProjectiveTest ι)
    (Q : α → ProjectiveTest ι) (c : Fin M → α) : POVM ι (Fin M) :=
  ProjectiveTest.filteredDecoder G
    (ProjectiveTest.finiteTests (fun i => Q (c i)) G) M hM

/-- Average message error of the actual decoder on the selected physical states. -/
def packedError {M : ℕ} (hM : 0 < M) (G : ProjectiveTest ι)
    (Q : α → ProjectiveTest ι) (ρ : α → DensityMatrix ι) (c : Fin M → α) : ℝ :=
  1 - (M : ℝ)⁻¹ * ∑ i, (packedDecoder hM G Q c).probability (ρ (c i)) i

omit [Fintype α] in
theorem packedError_le_codebookCost {M : ℕ} (hM : 0 < M) (G : ProjectiveTest ι)
    (Q : α → ProjectiveTest ι) (ρ : α → DensityMatrix ι) (c : Fin M → α) :
    packedError hM G Q ρ c ≤ Sampling.codebookCost
      (fun x => ((1-G.matrix)*(ρ x).matrix).trace.re)
      (fun x => ((1-(Q x).matrix)*(ρ x).matrix).trace.re)
      (fun x y => crossAcceptance G (Q y) (ρ x)) c := by
  have h (i : Fin M) := ProjectiveTest.finite_filteredDecoder_error_bound hM G
    (fun j => Q (c j)) (ρ (c i)) i
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => h i))
    (show (0 : ℝ) ≤ (M : ℝ)⁻¹ by positivity)
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hleft : (M : ℝ)⁻¹ * ∑ i, (1 -
      (ProjectiveTest.filteredDecoder G (ProjectiveTest.finiteTests (fun j => Q (c j)) G) M hM).probability
        (ρ (c i)) i) = packedError hM G Q ρ c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul, mul_one, mul_sub, inv_mul_cancel₀ hm]
    rfl
  rw [hleft] at hs
  exact hs

/-- A genuine finite random packing theorem. Its premises concern only the
ensemble's projector masses and average independent interference. The decoding
error estimate is proved from the explicit sequential POVM. -/
theorem exists_packed_codebook {M : ℕ} (hM : 0 < M)
    (G : ProjectiveTest ι) (Q : α → ProjectiveTest ι)
    (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    (ρ : α → DensityMatrix ι) {εG εQ β : ℝ}
    (hG : ∑x, p x * ((1-G.matrix)*(ρ x).matrix).trace.re ≤ εG)
    (hQ : ∑x, p x * ((1-(Q x).matrix)*(ρ x).matrix).trace.re ≤ εQ)
    (hcross : ∑x, ∑y, p x*p y*crossAcceptance G (Q y) (ρ x) ≤ β) :
    ∃c : Fin M → α, packedError hM G Q ρ c ≤ 9*εG+8*εQ+4*(M-1:ℕ)*β := by
  obtain ⟨c, hc⟩ := Sampling.exists_codebook_cost_le p hp hsum hM
    (fun x => ((1-G.matrix)*(ρ x).matrix).trace.re)
    (fun x => ((1-(Q x).matrix)*(ρ x).matrix).trace.re)
    (fun x y => crossAcceptance G (Q y) (ρ x)) hG hQ hcross
  exact ⟨c, (packedError_le_codebookCost hM G Q ρ c).trans hc⟩

/-- Explicit codewords and an actual normalized POVM with the packing error bound. -/
theorem exists_projective_packing {M : ℕ} (hM : 0 < M)
    (G : ProjectiveTest ι) (Q : α → ProjectiveTest ι)
    (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    (ρ : α → DensityMatrix ι) {εG εQ β : ℝ}
    (hG : ∑x, p x * ((1-G.matrix)*(ρ x).matrix).trace.re ≤ εG)
    (hQ : ∑x, p x * ((1-(Q x).matrix)*(ρ x).matrix).trace.re ≤ εQ)
    (hcross : ∑x, ∑y, p x*p y*crossAcceptance G (Q y) (ρ x) ≤ β) :
    ∃c : Fin M → α, ∃D : POVM ι (Fin M),
      1-(M : ℝ)⁻¹ * (∑i, D.probability (ρ (c i)) i) ≤
        9*εG+8*εQ+4*(M-1:ℕ)*β := by
  obtain ⟨c, hc⟩ := exists_packed_codebook hM G Q p hp hsum ρ hG hQ hcross
  exact ⟨c, packedDecoder hM G Q c, hc⟩

/-- Standard spectral packing bound: a global spectral ceiling `a` and
conditional ranks at most `b` give average interference at most `a*b`. -/
theorem exists_spectral_packing {M : ℕ} (hM : 0 < M)
    (G : ProjectiveTest ι) (Q : α → ProjectiveTest ι)
    (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    (ρ : α → DensityMatrix ι) {εG εQ a b : ℝ} (ha : 0 ≤ a)
    (hG : ∑x, p x * ((1-G.matrix)*(ρ x).matrix).trace.re ≤ εG)
    (hQ : ∑x, p x * ((1-(Q x).matrix)*(ρ x).matrix).trace.re ≤ εQ)
    (hflat : ((a : ℂ) • G.matrix - G.matrix *
      (DensityMatrix.mixture p hp hsum ρ).matrix * G.matrix).PosSemidef)
    (hrank : ∀x, (Q x).matrix.trace.re ≤ b) :
    ∃c : Fin M → α, ∃D : POVM ι (Fin M),
      1-(M : ℝ)⁻¹ * (∑i, D.probability (ρ (c i)) i) ≤
        9*εG+8*εQ+4*(M-1:ℕ)*(a*b) := by
  apply exists_projective_packing hM G Q p hp hsum ρ hG hQ
  have h := expected_crossAcceptance_le (J := Fin 2) G Q p hp hsum ρ ha hflat hrank
    (i := 0) (j := 1) (by decide)
  rw [Sampling.expect_two p hsum (show (0 : Fin 2) ≠ 1 by decide)
    (fun x y => crossAcceptance G (Q y) (ρ x))] at h
  exact h

end Nonadditivity.QuantumCoding
