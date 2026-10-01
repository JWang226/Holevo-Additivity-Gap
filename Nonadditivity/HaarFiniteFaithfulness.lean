/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarWordExpansion
import Nonadditivity.FiniteBlockModel

/-! # Recovering matrix coefficients from a finite regular-character model

Exact trace matching separates matrix-valued group polynomials on a bounded
word ball. This supplies the finite-to-regular symmetry bridge without any
norm convergence or approximation hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarFiniteFaithfulness
open HaarWordExpansion
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker

variable {G ι ν : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

/-- Normalized partial trace over the representation's finite index. -/
def blockTrace (A : Matrix (ι × ν) (ι × ν) ℂ) : Matrix ι ι ℂ :=
  fun i j => (∑ u : ν, A (i,u) (j,u)) / Fintype.card ν

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
@[simp] theorem blockTrace_zero : blockTrace (0 : Matrix (ι×ν) (ι×ν) ℂ) = 0 := by
  ext i j
  simp [blockTrace]

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
theorem blockTrace_sum {I : Type*} (s : Finset I)
    (A : I → Matrix (ι×ν) (ι×ν) ℂ) :
    blockTrace (∑ a ∈ s, A a) = ∑ a ∈ s, blockTrace (A a) := by
  ext i j
  simp only [blockTrace, Matrix.sum_apply, ← Finset.sum_div]
  rw [Finset.sum_comm]

omit [Fintype ι] [DecidableEq ι] [DecidableEq ν] in
theorem blockTrace_kronecker (A : Matrix ι ι ℂ) (B : Matrix ν ν ℂ) :
    blockTrace (A ⊗ₖ B) = normalizedTrace B • A := by
  ext i j
  simp only [blockTrace, Matrix.kronecker_apply, ← Finset.mul_sum,
    Matrix.smul_apply, smul_eq_mul, normalizedTrace, Matrix.trace, Matrix.diag_apply]
  ring

omit [DecidableEq G] in
theorem probe_finiteEval (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial G ι) (g : G) :
    blockTrace (finiteEval ρ f * wordHom (ι := ι) ρ g⁻¹) =
      ∑ w ∈ f.support, normalizedTrace (ρ (w*g⁻¹)) • f w := by
  rw [finiteEval_eq_sum, Finset.sum_mul, blockTrace_sum]
  apply Finset.sum_congr rfl
  intro w hw
  change blockTrace ((f w ⊗ₖ ρ w) * ((1 : Matrix ι ι ℂ) ⊗ₖ ρ g⁻¹)) = _
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, ← map_mul,
    blockTrace_kronecker]

theorem recover_coefficient (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial G ι) (g : G)
    (htrace : ∀ w ∈ f.support, normalizedTrace (ρ (w*g⁻¹)) = if w=g then 1 else 0) :
    blockTrace (finiteEval ρ f * wordHom (ι := ι) ρ g⁻¹) = f g := by
  rw [probe_finiteEval]
  calc
    _ = ∑ w ∈ f.support, if w=g then f w else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [htrace w hw]
      split_ifs <;> simp
    _ = _ := by
      by_cases hg : g ∈ f.support
      · simp [hg]
      · simp [hg, Finsupp.notMem_support_iff.mp hg]

/-- Separation is required only on pairwise differences of the actual support. -/
theorem eq_zero_of_finiteEval_eq_zero (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial G ι)
    (htrace : ∀ g ∈ f.support, ∀ w ∈ f.support,
      normalizedTrace (ρ (w*g⁻¹)) = if w=g then 1 else 0)
    (hf : finiteEval ρ f = 0) : f = 0 := by
  apply Finsupp.ext
  intro g
  by_cases hg : g ∈ f.support
  · have h := recover_coefficient ρ f g (htrace g hg)
    rw [hf, Matrix.zero_mul, blockTrace_zero] at h
    exact h.symm
  · exact Finsupp.notMem_support_iff.mp hg

/-- The existing finite tensor model recovers each coefficient of every
polynomial supported in a product word ball of radius `R`. -/
theorem bounded_product_eq_zero_of_finiteEval_eq_zero {K n R : ℕ}
    (f : MatrixPolynomial (Fin n → FreeGroup (Fin K)) ι)
    (hlinear : ∀ g ∈ f.support, ∀ j, FreeGroup.norm (g j) ≤ R)
    (hf : finiteEval (FiniteBlockModel.representation K (2*R) n) f = 0) : f = 0 := by
  apply eq_zero_of_finiteEval_eq_zero _ f ?_ hf
  intro g hg w hw
  have hlen : ∀ j, FreeGroup.norm ((w*g⁻¹) j) ≤ 2*R := by
    intro j
    have h := FreeGroup.norm_mul_le (w j) (g j)⁻¹
    rw [FreeGroup.norm_inv_eq] at h
    exact h.trans (by nlinarith [hlinear w hw j, hlinear g hg j])
  unfold normalizedTrace
  rw [FiniteBlockModel.representation_trace K (2*R) n (w*g⁻¹) hlen]
  have hc : (Fintype.card (Entropy.TensorChainIndex (FiniteBlockModel.LocalIndex K (2*R)) n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases he : w=g
  · simp [he, hc]
  · simp [mul_inv_eq_one, he]

end Nonadditivity.HaarFiniteFaithfulness
