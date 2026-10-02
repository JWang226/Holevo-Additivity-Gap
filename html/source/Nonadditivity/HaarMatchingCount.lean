/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMatchingSingletons
import Mathlib.Algebra.BigOperators.Fin

/-! # Counting entry matchings at a fixed relative permutation

Away from exceptional positions, an entry of total multiplicity at most two
has at most one possible partner. Restricting a matching permutation to the
exceptional positions is therefore injective. Higher multiplicities are
charged to the literal excess-occurrence statistic.
-/
noncomputable section
namespace Nonadditivity.HaarMatchingCount
open HaarPathMultiplicity HaarMatchingSingletons
open scoped BigOperators
variable {E : Type*} [DecidableEq E] {p : ℕ}

lemma count_ofFn_eq_card (f : Fin p → E) (e : E) :
    (List.ofFn f).count e=(Finset.univ.filter (fun a => f a=e)).card := by
  have hs : (List.ofFn f).count e=∑ a, if f a=e then 1 else 0 := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [List.ofFn_succ,List.count_cons,Fin.sum_univ_succ,ih]
      by_cases h : f 0=e <;> simp [h,Nat.add_comm]
  simpa using hs

lemma two_le_count_ofFn (f : Fin p → E) (e : E) (a b : Fin p)
    (ha : f a=e) (hb : f b=e) (hab : a≠b) : 2 ≤ (List.ofFn f).count e := by
  rw [count_ofFn_eq_card]
  have hsub : ({a,b} : Finset (Fin p)) ⊆ Finset.univ.filter (fun i => f i=e) := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [ha,hb]
  have h := Finset.card_le_card hsub
  simpa [hab] using h

/-- Positive occurrences whose combined entry multiplicity is at least three. -/
def marked (x y : Fin p → E) : Finset (Fin p) :=
  Finset.univ.filter (fun a => 3 ≤ (List.ofFn x ++ List.ofFn y).count (x a))

lemma target_unique_of_not_marked (x y : Fin p → E) (a : Fin p)
    (ha : a ∉ marked x y) (b c : Fin p) (hb : y b=x a) (hc : y c=x a) : b=c := by
  by_contra hbc
  have hn : ¬3 ≤ (List.ofFn x ++ List.ofFn y).count (x a) := by
    simpa [marked] using ha
  have hp : 0 < (List.ofFn x).count (x a) :=
    List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨a,rfl⟩)
  have hm := two_le_count_ofFn y (x a) b c hb hc hbc
  rw [List.count_append] at hn
  omega

/-- The number of marked positive occurrences is controlled by three times
all occurrences beyond the second copy of each entry. -/
theorem marked_card_le_three_excess (x y : Fin p → E) :
    (marked x y).card ≤ 3*excessOccurrences (List.ofFn x ++ List.ofFn y) := by
  let L := List.ofFn x ++ List.ofFn y
  let f : E → ℕ := fun e => if 3 ≤ L.count e then 1 else 0
  have he : (marked x y).card=((List.ofFn x).map f).sum := by
    simp [marked,f,L,List.map_ofFn,Fin.sum_ofFn]
  rw [he]
  calc
    _ ≤ (L.map f).sum := by
      dsimp only [L]
      rw [List.map_append,List.sum_append]
      omega
    _ = ∑ e ∈ L.toFinset, L.count e*f e := by
      simpa only [nsmul_eq_mul] using sum_occurrence_weights L f
    _ ≤ 3*excessOccurrences L := by
      rw [excessOccurrences,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      dsimp only [f]
      split_ifs <;> omega

/-- Over-approximation of all matchings: only the nonexceptional positions
are required to pair identical entries. -/
abbrev AgreementMatching (x y : Fin p → E) (S : Finset (Fin p)) :=
  {σ : Equiv.Perm (Fin p) // ∀ a, a ∉ S → x a=y (σ a)}

/-- Restriction to the exceptional and marked positions determines the
entire permutation. This estimate has no probabilistic hypotheses. -/
theorem card_agreementMatching_le (x y : Fin p → E) (S : Finset (Fin p)) :
    Fintype.card (AgreementMatching x y S) ≤ p^(S.card+3*excessOccurrences
      (List.ofFn x ++ List.ofFn y)) := by
  classical
  let B := S ∪ marked x y
  let enc : AgreementMatching x y S → (B → Fin p) := fun σ a => σ.val a.val
  have hi : Function.Injective enc := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro a
    by_cases ha : a ∈ B
    · exact congrFun h ⟨a,ha⟩
    · have hS : a ∉ S := fun hs => ha (Finset.mem_union_left _ hs)
      have hM : a ∉ marked x y := fun hm => ha (Finset.mem_union_right _ hm)
      exact target_unique_of_not_marked x y a hM (σ.val a) (τ.val a)
        (σ.property a hS).symm (τ.property a hS).symm
  have hcard := Fintype.card_le_of_injective enc hi
  have hpow : B.card ≤ S.card+3*excessOccurrences (List.ofFn x ++ List.ofFn y) :=
    (Finset.card_union_le S (marked x y)).trans
      (Nat.add_le_add_left (marked_card_le_three_excess x y) S.card)
  calc
    _ ≤ p^B.card := by simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using hcard
    _ ≤ _ := by
      by_cases hp : p=0
      · subst p
        simp [B,S.eq_empty_of_isEmpty,marked,excessOccurrences]
      · exact Nat.pow_le_pow_right (by omega) hpow

/-- Actual row and column matchings with prescribed relative permutation. -/
abbrev RelativeMatching {R C : Type*} (i k : Fin p → R) (j l : Fin p → C)
    (α : Equiv.Perm (Fin p)) :=
  {σ : Equiv.Perm (Fin p) // i=k ∘ σ ∧ j=l ∘ (σ*α)}

/-- With the relative matching fixed, the number of compatible pairs is
bounded by support size and the actual entry-multiplicity excess. -/
theorem card_relativeMatching_le {R C : Type*} [DecidableEq R] [DecidableEq C]
    (i k : Fin p → R) (j l : Fin p → C) (α : Equiv.Perm (Fin p)) :
    Fintype.card (RelativeMatching i k j l α) ≤ p^(α.support.card+
      3*excessOccurrences (List.ofFn (fun a => (i a,j a)) ++
        List.ofFn (fun a => (k a,l a)))) := by
  classical
  let f : RelativeMatching i k j l α →
      AgreementMatching (fun a => (i a,j a)) (fun a => (k a,l a)) α.support := fun σ =>
    ⟨σ.val,by
      intro a ha
      have hα : α a=a := by simpa only [Equiv.Perm.mem_support,not_not] using ha
      apply Prod.ext
      · exact congrFun σ.property.1 a
      · simpa only [Function.comp_apply,Equiv.Perm.mul_apply,hα] using congrFun σ.property.2 a⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    exact congrArg (fun z : AgreementMatching (fun a => (i a,j a))
      (fun a => (k a,l a)) α.support => z.val) h
  exact (Fintype.card_le_of_injective f hf).trans (card_agreementMatching_le _ _ α.support)

end Nonadditivity.HaarMatchingCount
