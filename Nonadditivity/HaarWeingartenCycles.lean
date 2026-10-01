/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarWeingartenGram
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Quantitative Gram decay from permutation support

A fixed tuple is exactly a function on the permutation cycles.  Every nontrivial
cycle has at least two elements.  These elementary facts give the support decay
needed by the weighted inverse estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarWeingartenCycles

open HaarInvariantTensor
open scoped BigOperators Matrix Matrix.Norms.L2Operator

abbrev Cycles {p : ℕ} (σ : Perm p) := Quotient (Equiv.Perm.SameCycle.setoid σ)

instance {p : ℕ} (σ : Perm p) : Fintype (Cycles σ) := Fintype.ofFinite _

def cycleMap {p : ℕ} (σ : Perm p) (a : Fin p) : Cycles σ := Quotient.mk _ a

theorem cycleMap_apply {p : ℕ} (σ : Perm p) (a : Fin p) :
    cycleMap σ (σ a) = cycleMap σ a :=
  Quotient.sound (Equiv.Perm.SameCycle.rfl.apply_left)

lemma fixed_eq_of_sameCycle {p D : ℕ} (σ : Perm p)
    (y : {y : Fin p → Fin D // y ∘ σ = y}) (a b : Fin p)
    (hab : σ.SameCycle a b) : y.1 a = y.1 b := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  have hy (r : Fin p) : y.1 (σ r) = y.1 r := congrFun y.2 r
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hy]
    exact ih

/-- Functions fixed by the permutation are exactly functions on its cycles. -/
def fixedTupleEquiv (D p : ℕ) (σ : Perm p) :
    {y : Fin p → Fin D // y ∘ σ = y} ≃ (Cycles σ → Fin D) where
  toFun y := Quotient.lift y.1 (fun a b h => fixed_eq_of_sameCycle σ y a b h)
  invFun f := ⟨f ∘ cycleMap σ, by
    funext a
    simp only [Function.comp_apply, cycleMap_apply]⟩
  left_inv y := rfl
  right_inv f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ a => rfl

theorem card_fixedTuple (D p : ℕ) (σ : Perm p) :
    Fintype.card {y : Fin p → Fin D // y ∘ σ = y} = D ^ Fintype.card (Cycles σ) := by
  classical
  rw [Fintype.card_congr (fixedTupleEquiv D p σ)]
  simp

/-- Nontrivial cycles have at least two representatives, counted injectively. -/
theorem card_cycles_support_le (p : ℕ) (σ : Perm p) :
    2 * Fintype.card (Cycles σ) + σ.support.card ≤ 2*p := by
  classical
  let Q := Cycles σ
  let moved : Q → Prop := fun q => σ q.out ≠ q.out
  let J : Q ⊕ {q : Q // moved q} → Fin p :=
    Sum.elim Quotient.out (fun q => σ q.1.out)
  have hcross (q : Q) (r : {q : Q // moved q}) : q.out ≠ σ r.1.out := by
    intro h
    have he : q = r.1 := by
      calc
        q = cycleMap σ q.out := (Quotient.out_eq q).symm
        _ = cycleMap σ (σ r.1.out) := congrArg (cycleMap σ) h
        _ = cycleMap σ r.1.out := cycleMap_apply σ _
        _ = r.1 := Quotient.out_eq _
    have hz : σ r.1.out = r.1.out := by simpa [he] using h.symm
    exact r.2 hz
  have hJ : Function.Injective J := by
    intro q r h
    cases q with
    | inl q =>
      cases r with
      | inl r => exact congrArg Sum.inl (Quotient.out_injective h)
      | inr r => exact False.elim (hcross q r h)
    | inr q =>
      cases r with
      | inl r => exact False.elim (hcross r q h.symm)
      | inr r =>
        exact congrArg Sum.inr (Subtype.ext (Quotient.out_injective (σ.injective h)))
  have hcard := Fintype.card_le_of_injective J hJ
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  let R : {q : Q // ¬moved q} → {a : Fin p // σ a=a} :=
    fun q => ⟨q.1.out, not_not.mp q.2⟩
  have hR : Function.Injective R := by
    intro q r h
    apply Subtype.ext
    exact Quotient.out_injective (congrArg Subtype.val h)
  have hfix := Fintype.card_le_of_injective R hR
  have hpart : Fintype.card {q : Q // ¬moved q} =
      Fintype.card Q - Fintype.card {q : Q // moved q} :=
    Fintype.card_subtype_compl moved
  have hmovle : Fintype.card {q : Q // moved q} ≤ Fintype.card Q :=
    Fintype.card_subtype_le _
  have hfixcard : Fintype.card {a : Fin p // σ a=a} = p - σ.support.card := by
    have hc := Fintype.card_subtype_compl (fun a : Fin p => σ a ≠ a)
    simpa [Fintype.card_subtype, Equiv.Perm.support] using hc
  have hs : σ.support.card ≤ p := by simpa using Finset.card_le_univ σ.support
  change 2 * Fintype.card Q + σ.support.card ≤ 2*p
  omega

/-- Squared fixed-tuple counts carry at least one dimension factor per moved index. -/
theorem card_fixedTuple_sq_mul_support_le (D p : ℕ) (σ : Perm p) (hD : 1 ≤ D) :
    (Fintype.card {y : Fin p → Fin D // y ∘ σ = y})^2 * D^σ.support.card ≤ D^(2*p) := by
  rw [card_fixedTuple, ← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right hD
  have h := card_cycles_support_le p σ
  omega

def relativeFixedEquiv (D p : ℕ) (σ τ : Perm p) :
    {y : Fin p → Fin D // y ∘ σ = y ∘ τ} ≃
      {z : Fin p → Fin D // z ∘ (σ⁻¹*τ) = z} where
  toFun y := ⟨y.1 ∘ σ, by
    funext a
    simpa [Function.comp_apply] using (congrFun y.2 a).symm⟩
  invFun z := ⟨fun a => z.1 (σ.symm a), by
    funext a
    simpa [Function.comp_apply] using (congrFun z.2 a).symm⟩
  left_inv y := by
    apply Subtype.ext
    funext a
    simp [Function.comp_apply]
  right_inv z := by
    apply Subtype.ext
    funext a
    simp [Function.comp_apply]

theorem card_relative (D p : ℕ) (σ τ : Perm p) :
    Fintype.card {y : Fin p → Fin D // y ∘ σ = y ∘ τ} =
      Fintype.card {z : Fin p → Fin D // z ∘ (σ⁻¹*τ) = z} := by
  classical
  exact Fintype.card_congr (relativeFixedEquiv D p σ τ)

/-- Exact support decay of the actual Gram matrix, in a form without real exponents. -/
theorem norm_gram_sq_mul_support_le (N p : ℕ) (σ τ : Perm p) :
    ‖gram N p σ τ‖^2 * (N+1:ℝ)^((σ⁻¹*τ).support.card) ≤ (N+1:ℝ)^(2*p) := by
  rw [gram_apply_card]
  norm_num only [Complex.norm_natCast]
  have h := card_fixedTuple_sq_mul_support_le (N+1) p (σ⁻¹*τ) (by omega)
  rw [← card_relative (N+1) p σ τ] at h
  exact_mod_cast h

/-- The normalized Gram coefficient decays by one square-root dimension factor
for each moved index of the relative permutation. -/
theorem norm_gram_mul_sqrt_pow_le (N p : ℕ) (σ τ : Perm p) :
    ‖gram N p σ τ‖ * (Real.sqrt (N+1))^((σ⁻¹*τ).support.card) ≤ (N+1:ℝ)^p := by
  have hs : ((Real.sqrt (N+1))^((σ⁻¹*τ).support.card))^2 =
      (N+1:ℝ)^((σ⁻¹*τ).support.card) := by
    rw [← pow_mul, Nat.mul_comm _ 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hh : (‖gram N p σ τ‖ * (Real.sqrt (N+1))^((σ⁻¹*τ).support.card))^2 ≤
      ((N+1:ℝ)^p)^2 := by
    rw [mul_pow, hs, ← pow_mul, Nat.mul_comm p 2]
    exact norm_gram_sq_mul_support_le N p σ τ
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hh

end Nonadditivity.HaarWeingartenCycles
