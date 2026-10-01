/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarInvariantSpanning
import Nonadditivity.HaarWeingartenCycles

/-! # Relative permutations in the Weingarten formula

Translation symmetry reduces the two permutation sums to a single inverse-Gram
row, with an exact finite matching multiplicity.  This is the form used by the
weighted absolute row-sum estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarInvariantTensor

open MeasureTheory HaarModel HaarAveraging HaarWeingartenCycles
open scoped BigOperators Matrix Matrix.Norms.L2Operator

theorem gram_apply_relative (N p : ℕ) (σ τ : Perm p) :
    gram N p σ τ = gram N p 1 (σ⁻¹*τ) := by
  rw [gram_apply_card, gram_apply_card]
  congr 1
  rw [card_relative, card_relative]
  simp

theorem gram_apply_mul_left (N p : ℕ) (κ σ τ : Perm p) :
    gram N p (κ*σ) (κ*τ) = gram N p σ τ := by
  calc
    _ = gram N p 1 ((κ*σ)⁻¹*(κ*τ)) := gram_apply_relative N p _ _
    _ = gram N p 1 (σ⁻¹*τ) := by simp [mul_inv_rev, mul_assoc]
    _ = gram N p σ τ := (gram_apply_relative N p σ τ).symm

theorem weingarten_apply_mul_left (N p : ℕ) (κ σ τ : Perm p) :
    weingarten N p (κ*σ) (κ*τ) = weingarten N p σ τ := by
  let e : Perm p ≃ Perm p := Equiv.mulLeft κ
  have hg : (gram N p).submatrix e e = gram N p := by
    ext a b
    exact gram_apply_mul_left N p κ a b
  have hi := congrArg (fun M : Matrix (Perm p) (Perm p) ℂ => M⁻¹) hg
  change ((gram N p).submatrix e e)⁻¹ = (gram N p)⁻¹ at hi
  rw [Matrix.inv_submatrix_equiv] at hi
  exact congrFun (congrFun hi σ) τ

theorem weingarten_apply_relative (N p : ℕ) (σ τ : Perm p) :
    weingarten N p σ τ = weingarten N p 1 (σ⁻¹*τ) := by
  simpa using (weingarten_apply_mul_left N p σ⁻¹ σ τ).symm

/-- Number of row/column matchings with a prescribed relative permutation. -/
def matchingMultiplicity {N p : ℕ} (i j k l : Tuple N p) (π : Perm p) : ℕ :=
  Fintype.card {σ : Perm p // i = k ∘ σ ∧ j = l ∘ (σ*π)}

theorem matchingMultiplicity_eq_sum {N p : ℕ} (i j k l : Tuple N p) (π : Perm p) :
    (matchingMultiplicity i j k l π : ℂ) =
      ∑ σ : Perm p, if i = k ∘ σ ∧ j = l ∘ (σ*π) then 1 else 0 := by
  classical
  simp [matchingMultiplicity, Fintype.card_subtype, ← Finset.sum_boole]

/-- The actual Haar integral expressed using one row of the inverse Gram matrix. -/
theorem integral_entryMonomial_eq_relative {N p : ℕ} (hp : p ≤ N+1)
    (i j k l : Tuple N p) :
    (∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N) =
      ∑ π : Perm p, (matchingMultiplicity i j k l π : ℂ) * weingarten N p 1 π := by
  classical
  rw [integral_entryMonomial_eq_weingarten hp]
  have hs (σ : Perm p) :
      (∑ τ : Perm p, (if i=k∘σ then 1 else 0) * weingarten N p σ τ *
        (if j=l∘τ then 1 else 0)) =
      ∑ π : Perm p, (if i=k∘σ ∧ j=l∘(σ*π) then 1 else 0) * weingarten N p 1 π := by
    rw [← (Equiv.mulLeft σ).sum_comp]
    rotate_left
    · simp
    apply Finset.sum_congr rfl
    intro π _
    change (if i=k∘σ then 1 else 0) * weingarten N p σ (σ*π) *
      (if j=l∘(σ*π) then 1 else 0) = _
    rw [weingarten_apply_relative N p σ (σ*π), inv_mul_cancel_left]
    by_cases hr : i=k∘σ <;> by_cases hc : j=l∘(σ*π) <;> simp [hr,hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  rw [matchingMultiplicity_eq_sum, Finset.sum_mul]

theorem norm_integral_entryMonomial_le_relative {N p : ℕ} (hp : p ≤ N+1)
    (i j k l : Tuple N p) :
    ‖∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N‖ ≤
      ∑ π : Perm p, (matchingMultiplicity i j k l π : ℝ) * ‖weingarten N p 1 π‖ := by
  rw [integral_entryMonomial_eq_relative hp]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, Complex.norm_natCast])

end Nonadditivity.HaarInvariantTensor
