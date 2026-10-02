/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathMultiplicity
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.List.OfFn

/-! # Singleton entries force disagreement between Haar matchings

A row matching and a column matching that agree at an occurrence pair match
both entry indices. Such an entry occurs on both sides of the Haar moment
and cannot be a singleton. This gives the exact combinatorial source of the
singleton suppression factor in a Weingarten bound.
-/
noncomputable section
namespace Nonadditivity.HaarMatchingSingletons
open HaarPathMultiplicity
variable {E : Type*} [DecidableEq E] {p : ℕ}

lemma not_mem_singletonEdges_of_mem_both {e : E} {l r : List E}
    (hl : e ∈ l) (hr : e ∈ r) : e ∉ singletonEdges (l++r) := by
  intro h
  have hc := (Finset.mem_filter.mp h).2
  rw [List.count_append] at hc
  have hcl := List.count_pos_iff.mpr hl
  have hcr := List.count_pos_iff.mpr hr
  omega

lemma mem_relative_support (σ τ : Equiv.Perm (Fin p)) (a : Fin p) :
    a ∈ (σ⁻¹*τ).support ↔ τ a ≠ σ a := by
  rw [Equiv.Perm.mem_support]
  change σ.symm (τ a) ≠ a ↔ τ a ≠ σ a
  exact not_congr σ.symm_apply_eq

/-- Abstract matching form: agreement of the two matchings pairs the entries,
so every singleton belongs to one of two images of their disagreement set. -/
theorem singletonEdges_le_two_support
    (x y : Fin p → E) (σ τ : Equiv.Perm (Fin p))
    (hmatch : ∀ a, σ a=τ a → x a=y (σ a)) :
    (singletonEdges (List.ofFn x ++ List.ofFn y)).card ≤ 2*(σ⁻¹*τ).support.card := by
  classical
  let S := (σ⁻¹*τ).support
  have hsub : singletonEdges (List.ofFn x ++ List.ofFn y) ⊆
      S.image x ∪ S.image (fun a => y (σ a)) := by
    intro e he
    have hmem := List.mem_append.mp (List.mem_toFinset.mp (Finset.mem_filter.mp he).1)
    rcases hmem with hx | hy
    · obtain ⟨a,ha⟩ := List.mem_ofFn.mp hx
      have hs : a ∈ S := by
        by_contra hn
        have hsame : σ a=τ a := by
          have h := not_iff_not.mpr (mem_relative_support σ τ a)
          exact (not_ne_iff.mp (h.mp hn)).symm
        have hyp : e ∈ List.ofFn y := List.mem_ofFn.mpr ⟨σ a,(hmatch a hsame).symm.trans ha⟩
        exact not_mem_singletonEdges_of_mem_both hx hyp he
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,hs,ha⟩)
    · obtain ⟨b,hb⟩ := List.mem_ofFn.mp hy
      let a := σ⁻¹ b
      have hab : σ a=b := σ.apply_symm_apply b
      have hs : a ∈ S := by
        by_contra hn
        have hsame : σ a=τ a := by
          have h := not_iff_not.mpr (mem_relative_support σ τ a)
          exact (not_ne_iff.mp (h.mp hn)).symm
        have hxp : e ∈ List.ofFn x := List.mem_ofFn.mpr
          ⟨a,(hmatch a hsame).trans (by rw [hab]; exact hb)⟩
        exact not_mem_singletonEdges_of_mem_both hxp hy he
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,hs,by rw [hab]; exact hb⟩)
  calc
    _ ≤ (S.image x ∪ S.image (fun a => y (σ a))).card := Finset.card_le_card hsub
    _ ≤ (S.image x).card+(S.image (fun a => y (σ a))).card := Finset.card_union_le _ _
    _ ≤ S.card+S.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = _ := by dsimp [S]; omega

/-- For actual matrix entries, row/column matching constraints force at least
half as many disagreement positions as there are singleton entry values. -/
theorem singleton_entries_le_two_support
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (i k : Fin p → R) (j l : Fin p → C) (σ τ : Equiv.Perm (Fin p))
    (hrow : i=k ∘ σ) (hcol : j=l ∘ τ) :
    (singletonEdges (List.ofFn (fun a => (i a,j a)) ++
      List.ofFn (fun a => (k a,l a)))).card ≤ 2*(σ⁻¹*τ).support.card := by
  apply singletonEdges_le_two_support _ _ σ τ
  intro a ha
  apply Prod.ext
  · exact congrFun hrow a
  · simpa only [Function.comp_apply,←ha] using congrFun hcol a

end Nonadditivity.HaarMatchingSingletons
