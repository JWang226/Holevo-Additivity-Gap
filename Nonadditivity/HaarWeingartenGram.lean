/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarInvariantTensor

/-! # Exact combinatorics of the permutation Gram matrix

These are finite counting identities for the actual invariant tensors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarInvariantTensor

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

theorem gram_apply_sum (N p : ℕ) (σ τ : Perm p) :
    gram N p σ τ = ∑ y : Tuple N p, if y ∘ σ = y ∘ τ then 1 else 0 := by
  classical
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, contractions,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [eq_comm]

/-- A Gram coefficient counts the tuples constant on the relative permutation. -/
theorem gram_apply_card (N p : ℕ) (σ τ : Perm p) :
    gram N p σ τ = (Fintype.card {y : Tuple N p // y ∘ σ = y ∘ τ} : ℂ) := by
  classical
  rw [gram_apply_sum]
  simp [Fintype.card_subtype, ← Finset.sum_boole]

theorem gram_apply_self (N p : ℕ) (σ : Perm p) :
    gram N p σ σ = (N+1:ℂ)^p := by
  rw [gram_apply_sum]
  simp [Tuple]

theorem gram_apply_nonneg (N p : ℕ) (σ τ : Perm p) : 0 ≤ gram N p σ τ := by
  rw [gram_apply_card]
  exact_mod_cast (Nat.zero_le _)

/-- A nonidentity relative permutation identifies at least one pair of coordinates. -/
theorem gram_card_le_of_ne (N p : ℕ) (σ τ : Perm p) (hστ : σ ≠ τ) :
    Fintype.card {y : Tuple N p // y ∘ σ = y ∘ τ} ≤ (N+1)^(p-1) := by
  classical
  have hf : (σ : Fin p → Fin p) ≠ τ := fun h => hστ (Equiv.ext (congrFun h))
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hf
  let a := σ r
  let b := τ r
  have hab : b ≠ a := Ne.symm hr
  let restrict : {y : Tuple N p // y ∘ σ = y ∘ τ} → ({s : Fin p // s ≠ a} → Fin (N+1)) :=
    fun y s => y.1 s
  have hinj : Function.Injective restrict := by
    intro y z hyz
    apply Subtype.ext
    funext s
    by_cases hs : s=a
    · subst s
      have hy : y.1 a = y.1 b := congrFun y.2 r
      have hz : z.1 a = z.1 b := congrFun z.2 r
      exact hy.trans ((congrFun hyz ⟨b,hab⟩).trans hz.symm)
    · exact congrFun hyz ⟨s,hs⟩
  have hcard : Fintype.card {s : Fin p // s ≠ a} = p-1 := by
    simp [Fintype.card_subtype_compl]
  simpa [Fintype.card_fun, hcard] using Fintype.card_le_of_injective restrict hinj

theorem norm_gram_apply_le_of_ne (N p : ℕ) (σ τ : Perm p) (hστ : σ ≠ τ) :
    ‖gram N p σ τ‖ ≤ (N+1:ℝ)^(p-1) := by
  rw [gram_apply_card]
  norm_num only [Complex.norm_natCast]
  exact_mod_cast gram_card_le_of_ne N p σ τ hστ

end Nonadditivity.HaarInvariantTensor
