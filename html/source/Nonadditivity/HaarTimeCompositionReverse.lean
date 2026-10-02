/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarTimeCompositions

/-! # Reversing actual positive time compositions -/
namespace Nonadditivity.HaarTimeCompositions
open scoped BigOperators

/-- The recursive finite set contains exactly the positive lists of the
prescribed length and total duration. -/
theorem mem_compositions_iff {cuts n : ℕ} {t : List ℕ} :
    t ∈ compositions cuts n ↔
      t.length=cuts+1 ∧ t.sum=n ∧ ∀ a ∈ t, 0 < a := by
  constructor
  · intro ht
    exact ⟨length_of_mem ht,sum_of_mem ht,positive_of_mem ht⟩
  · intro ht
    induction cuts generalizing n t with
    | zero =>
        obtain ⟨hl,hs,hp⟩ := ht
        cases t with
        | nil => simp at hl
        | cons a t =>
            have ht : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
            subst t
            have ha := hp a (by simp)
            simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hs
            subst n
            simp [compositions,show a ≠ 0 by omega]
    | succ cuts ih =>
        obtain ⟨hl,hs,hp⟩ := ht
        cases t with
        | nil => simp at hl
        | cons a t =>
            have ha := hp a (by simp)
            have ht : t.length=cuts+1 := by simp only [List.length_cons] at hl; omega
            have hs' : t.sum=n-((a-1)+1) := by
              simp only [List.sum_cons] at hs
              omega
            have hp' : ∀ b ∈ t, 0 < b := fun b hb => hp b (by simp [hb])
            have hm := ih ⟨ht,hs',hp'⟩
            simp only [compositions,Finset.mem_biUnion,Finset.mem_range,Finset.mem_image]
            refine ⟨a-1,?_,t,hm,?_⟩
            · simp only [List.sum_cons] at hs
              omega
            · congr 1
              omega

@[simp] theorem mem_compositions_reverse_iff {cuts n : ℕ} {t : List ℕ} :
    t.reverse ∈ compositions cuts n ↔ t ∈ compositions cuts n := by
  simp only [mem_compositions_iff,List.length_reverse,List.sum_reverse,List.mem_reverse]

theorem reverse_mem_compositions {cuts n : ℕ} {t : List ℕ}
    (ht : t ∈ compositions cuts n) : t.reverse ∈ compositions cuts n :=
  mem_compositions_reverse_iff.mpr ht

/-- Reversal is an actual permutation of the duration indexing type. -/
def reverseEquiv (cuts n : ℕ) : compositions cuts n ≃ compositions cuts n where
  toFun t := ⟨t.val.reverse,reverse_mem_compositions t.property⟩
  invFun t := ⟨t.val.reverse,reverse_mem_compositions t.property⟩
  left_inv t := Subtype.ext (List.reverse_reverse t.val)
  right_inv t := Subtype.ext (List.reverse_reverse t.val)

/-- Reverse chronological and chronological duration sums agree exactly. -/
theorem sum_reverse {R : Type*} [AddCommMonoid R] (cuts n : ℕ) (f : List ℕ → R) :
    ∑ t ∈ compositions cuts n, f t.reverse = ∑ t ∈ compositions cuts n, f t := by
  apply Finset.sum_bij (fun t _ => t.reverse)
  · intro t ht
    exact reverse_mem_compositions ht
  · intro t ht u hu he
    simpa only [List.reverse_reverse] using congrArg List.reverse he
  · intro t ht
    exact ⟨t.reverse,reverse_mem_compositions ht,List.reverse_reverse t⟩
  · intro t ht
    rfl

end Nonadditivity.HaarTimeCompositions
