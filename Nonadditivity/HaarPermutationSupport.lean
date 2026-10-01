/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! # Permutation support counting and Hamming distance

A permutation moving exactly `d` points is encoded by a list of its moved
points and their images. This gives a polynomial, rather than factorial,
bound at every fixed support size.
-/

noncomputable section
namespace Nonadditivity.HaarPermutationSupport
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev SupportSize (ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ) :=
  {σ : Equiv.Perm ι // σ.support.card = d}

def enumerate {d : ℕ} (σ : SupportSize ι d) : Fin d ≃ ↥σ.val.support :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using σ.property.symm)

def code {d : ℕ} (σ : SupportSize ι d) : Fin d → ι × ι :=
  fun i => ((enumerate σ i).val, σ.val (enumerate σ i).val)

theorem code_injective (d : ℕ) : Function.Injective (code (ι := ι) (d := d)) := by
  intro σ τ h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have he (i : Fin d) : code σ i = code τ i := congrFun h i
  by_cases hx : x ∈ σ.val.support
  · obtain ⟨i, hi⟩ := (enumerate σ).surjective ⟨x,hx⟩
    have hfirst := congrArg Prod.fst (he i)
    have hsecond := congrArg Prod.snd (he i)
    change (enumerate σ i).val = (enumerate τ i).val at hfirst
    change σ.val (enumerate σ i).val = τ.val (enumerate τ i).val at hsecond
    rw [hi] at hfirst hsecond
    simpa only [← hfirst] using hsecond
  · have hy : x ∉ τ.val.support := by
      intro hy
      obtain ⟨i, hi⟩ := (enumerate τ).surjective ⟨x,hy⟩
      have hfirst := congrArg Prod.fst (he i)
      change (enumerate σ i).val = (enumerate τ i).val at hfirst
      rw [hi] at hfirst
      change (enumerate σ i).val = x at hfirst
      exact hx (by rw [← hfirst]; exact (enumerate σ i).property)
    have hs : σ.val x = x := by simpa using hx
    have ht : τ.val x = x := by simpa using hy
    exact hs.trans ht.symm

/-- The support-size layer has at most `card(ι)^(2*d)` permutations. -/
theorem card_supportSize_le (d : ℕ) :
    Fintype.card (SupportSize ι d) ≤ (Fintype.card ι)^(2*d) := by
  have h := Fintype.card_le_of_injective (code (ι := ι) (d := d)) (code_injective d)
  simpa only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ← pow_two,
    ← pow_mul] using h

def distance (σ τ : Equiv.Perm ι) : ℕ :=
  (Finset.univ.filter (fun x => σ x ≠ τ x)).card

@[simp] theorem distance_self (σ : Equiv.Perm ι) : distance σ σ = 0 := by
  simp [distance]

theorem distance_symm (σ τ : Equiv.Perm ι) : distance σ τ = distance τ σ := by
  unfold distance
  congr 1
  ext x
  simp [ne_comm]

theorem distance_triangle (σ κ τ : Equiv.Perm ι) :
    distance σ τ ≤ distance σ κ + distance κ τ := by
  apply (Finset.card_le_card (show Finset.univ.filter (fun x => σ x ≠ τ x) ⊆
    Finset.univ.filter (fun x => σ x ≠ κ x) ∪
      Finset.univ.filter (fun x => κ x ≠ τ x) from ?_)).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases h : σ x = κ x
  · exact Or.inr (fun ht => hx (h.trans ht))
  · exact Or.inl h

theorem distance_eq_support (σ τ : Equiv.Perm ι) :
    distance σ τ = (σ⁻¹*τ).support.card := by
  unfold distance
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mem_support,
    Equiv.Perm.mul_apply]
  constructor
  · intro h he
    apply h
    have hh := congrArg σ he
    simpa using hh.symm
  · intro h he
    apply h
    rw [← he]
    simp

theorem distance_le_card (σ τ : Equiv.Perm ι) : distance σ τ ≤ Fintype.card ι :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem two_le_distance_of_ne (σ τ : Equiv.Perm ι) (h : σ ≠ τ) : 2 ≤ distance σ τ := by
  rw [distance_eq_support]
  apply Equiv.Perm.two_le_card_support_of_ne_one
  intro he
  apply h
  have hh := congrArg (fun π : Equiv.Perm ι => σ*π) he
  simpa [mul_assoc] using hh.symm

def distanceLayerEquiv (σ : Equiv.Perm ι) (d : ℕ) :
    {τ : Equiv.Perm ι // distance σ τ = d} ≃ SupportSize ι d where
  toFun τ := ⟨σ⁻¹*τ.val, by rw [← distance_eq_support]; exact τ.property⟩
  invFun τ := ⟨σ*τ.val, by rw [distance_eq_support, inv_mul_cancel_left]; exact τ.property⟩
  left_inv τ := by apply Subtype.ext; simp
  right_inv τ := by apply Subtype.ext; simp

theorem card_distance_layer_le (σ : Equiv.Perm ι) (d : ℕ) :
    Fintype.card {τ : Equiv.Perm ι // distance σ τ = d} ≤ (Fintype.card ι)^(2*d) := by
  rw [Fintype.card_congr (distanceLayerEquiv σ d)]
  exact card_supportSize_le d

def supportCode {d : ℕ} (σ : SupportSize ι d) :
    Σ s : {s : Finset ι // s.card=d}, Equiv.Perm ↥s.val :=
  ⟨⟨σ.val.support,σ.property⟩, σ.val.subtypePerm (fun _ => Equiv.Perm.apply_mem_support)⟩

theorem recover_supportCode {d : ℕ} (σ : SupportSize ι d) :
    Equiv.Perm.ofSubtype (supportCode σ).2 = σ.val := by
  apply (Equiv.Perm.ofSubtype_eq_iff (fun _ => Equiv.Perm.apply_mem_support)).mpr
  exact ⟨Finset.Subset.refl _, fun _ => rfl⟩

theorem supportCode_injective (d : ℕ) : Function.Injective (supportCode (ι := ι) (d := d)) := by
  intro σ τ h
  apply Subtype.ext
  rw [← recover_supportCode σ, ← recover_supportCode τ]
  exact congrArg (fun z : Σ s : {s : Finset ι // s.card=d}, Equiv.Perm ↥s.val =>
    Equiv.Perm.ofSubtype z.2) h

/-- The sharper support-layer bound keeps the required moment exponent. -/
theorem card_supportSize_le_pow (d : ℕ) :
    Fintype.card (SupportSize ι d) ≤ (Fintype.card ι)^d := by
  have h := Fintype.card_le_of_injective (supportCode (ι := ι) (d := d)) (supportCode_injective d)
  have hc (s : {s : Finset ι // s.card=d}) : Fintype.card (Equiv.Perm ↥s.val) = d.factorial := by
    rw [Fintype.card_perm, Fintype.card_coe, s.property]
  rw [Fintype.card_sigma] at h
  simp_rw [hc] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, nsmul_eq_mul] at h
  norm_cast at h
  apply h.trans
  rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow _ _

theorem card_distance_layer_le_pow (σ : Equiv.Perm ι) (d : ℕ) :
    Fintype.card {τ : Equiv.Perm ι // distance σ τ = d} ≤ (Fintype.card ι)^d := by
  rw [Fintype.card_congr (distanceLayerEquiv σ d)]
  exact card_supportSize_le_pow d

end Nonadditivity.HaarPermutationSupport
