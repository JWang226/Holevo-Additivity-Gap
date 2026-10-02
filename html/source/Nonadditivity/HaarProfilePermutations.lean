/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathRefined
import Nonadditivity.HaarMatchingCount
import Mathlib.GroupTheory.Perm.Support

/-! # Profile-preserving permutations of chain positions -/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarProfilePermutations
open scoped BigOperators
variable {I E : Type*} [Fintype I] [DecidableEq I] [DecidableEq E]

/-- Equal label-fiber sizes supply an actual label-preserving bijection. -/
def labelEquiv (f g : I → E)
    (h : ∀ e, Fintype.card {i // f i=e}=Fintype.card {i // g i=e}) : I ≃ I :=
  Equiv.ofFiberEquiv (fun e => Fintype.equivOfCardEq (h e))

theorem labelEquiv_map (f g : I → E)
    (h : ∀ e, Fintype.card {i // f i=e}=Fintype.card {i // g i=e}) (i : I) :
    g (labelEquiv f g h i)=f i := Equiv.ofFiberEquiv_map _ i

lemma restricted_fiber_card (f : I → E) (S : Finset I) (e : E) :
    Fintype.card {i : {i : I // i ∉ S} // f i.val=e} =
      ((Finset.univ.filter (fun i => f i=e)).filter (fun i => i ∉ S)).card := by
  let e' : {i : {i : I // i ∉ S} // f i.val=e} ≃ {i : I // i ∉ S ∧ f i=e} :=
    ⟨fun i => ⟨i.val.val,i.val.property,i.property⟩,
      fun i => ⟨⟨i.val,i.property.1⟩,i.property.2⟩,
      fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr e',Fintype.card_subtype,Finset.filter_filter]
  congr 1
  ext i
  simp [and_comm]

/-- A matching can be chosen to fix any designated positions at which the
labels already agree. This is used for the first and last edges of a chain. -/
theorem exists_perm_labels_fix (f g : I → E) (S : Finset I)
    (hcount : ∀ e, Fintype.card {i // f i=e}=Fintype.card {i // g i=e})
    (hfix : ∀ i ∈ S, f i=g i) :
    ∃ σ : Equiv.Perm I, (∀ i, g (σ i)=f i) ∧ ∀ i ∈ S, σ i=i := by
  have hr : ∀ e, Fintype.card {i : {i : I // i ∉ S} // f i.val=e} =
      Fintype.card {i : {i : I // i ∉ S} // g i.val=e} := by
    intro e
    rw [restricted_fiber_card,restricted_fiber_card]
    have hc := hcount e
    rw [Fintype.card_subtype,Fintype.card_subtype] at hc
    have hs : ((Finset.univ.filter (fun i => f i=e)).filter (fun i => i ∈ S)) =
        ((Finset.univ.filter (fun i => g i=e)).filter (fun i => i ∈ S)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨he,hi⟩
        exact ⟨(hfix i hi).symm.trans he,hi⟩
      · rintro ⟨he,hi⟩
        exact ⟨(hfix i hi).trans he,hi⟩
    have h₁ := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun i => f i=e)) (fun i => i ∈ S)
    have h₂ := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun i => g i=e)) (fun i => i ∈ S)
    rw [hs] at h₁
    omega
  let e := labelEquiv (fun i : {i : I // i ∉ S} => f i.val)
    (fun i : {i : I // i ∉ S} => g i.val) hr
  refine ⟨Equiv.Perm.ofSubtype e,?_,?_⟩
  · intro i
    by_cases hi : i ∈ S
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem e (by simpa using hi)]
      exact (hfix i hi).symm
    · rw [Equiv.Perm.ofSubtype_apply_of_mem e hi]
      exact labelEquiv_map _ _ hr ⟨i,hi⟩
  · intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_not_mem e (by simpa using hi)

section Chains
open HaarPathGraph HaarPathClasses
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
variable {P Q : Path V d m}

lemma coreChainProfile_count (c : P.CoreChain) (a : HaarPathProfiles.Color d) :
    (P.coreChainProfile c).val.count a=(c.val.map color).count a := by
  obtain ⟨q,l,he,hq⟩ := c.property.2
  simp [Path.coreChainProfile,he,HaarPathProfiles.wordProfile]

lemma coreChainProfile_first (c : P.CoreChain) :
    (P.coreChainProfile c).val.first=color (c.val.head (P.toCore_nonempty c.property.1)) := rfl

lemma coreChainProfile_last (c : P.CoreChain) :
    (P.coreChainProfile c).val.last=color (c.val.getLast (P.toCore_nonempty c.property.1)) := by
  obtain ⟨q,l,he,hq⟩ := c.property.2
  simp only [Path.coreChainProfile,he,HaarPathProfiles.wordProfile,List.head_cons,List.tail_cons]
  exact List.getLast_map (l := q::l) (f := color) (by simp)

/-- Equal profiles give a permutation of edge positions preserving colors
and fixing the first and last positions, including chains of length one. -/
theorem exists_coreChain_positionPerm (h : RefinedPattern P Q) (c : P.CoreChain) :
    ∃ σ : Equiv.Perm (Fin c.val.length),
      (∀ i, color (h.samePattern.dartPerm (c.val.get (σ i)))=color (c.val.get i)) ∧
      ∀ i, (i.val=0 ∨ i.val+1=c.val.length) → σ i=i := by
  classical
  let f : Fin c.val.length → HaarPathProfiles.Color d := fun i => color (c.val.get i)
  let g : Fin c.val.length → HaarPathProfiles.Color d :=
    fun i => color (h.samePattern.dartPerm (c.val.get i))
  let S := Finset.univ.filter (fun i : Fin c.val.length => i.val=0 ∨ i.val+1=c.val.length)
  have hprofile := h.profile_eq c
  have hcount : ∀ a, Fintype.card {i // f i=a}=Fintype.card {i // g i=a} := by
    intro a
    have he := congrArg (fun p : HaarPathProfiles.BoundedProfile (HaarPathProfiles.Color d) m => p.val.count a) hprofile
    dsimp only at he
    rw [coreChainProfile_count,coreChainProfile_count] at he
    simp only [SamePattern.coreChainEquiv_apply,SamePattern.coreChainMap_val,List.map_map] at he
    rw [Fintype.card_subtype,Fintype.card_subtype,
      ←HaarMatchingCount.count_ofFn_eq_card,←HaarMatchingCount.count_ofFn_eq_card]
    simpa only [f,g,List.ofFn_comp',List.ofFn_get,List.map_map] using he
  have hfirst : color (c.val.head (P.toCore_nonempty c.property.1)) =
      color (h.samePattern.dartPerm (c.val.head (P.toCore_nonempty c.property.1))) := by
    have he := congrArg (fun p : HaarPathProfiles.BoundedProfile (HaarPathProfiles.Color d) m => p.val.first) hprofile
    simpa only [coreChainProfile_first,SamePattern.coreChainEquiv_apply,
      SamePattern.coreChainMap_val,List.head_map] using he
  have hlast : color (c.val.getLast (P.toCore_nonempty c.property.1)) =
      color (h.samePattern.dartPerm (c.val.getLast (P.toCore_nonempty c.property.1))) := by
    have he := congrArg (fun p : HaarPathProfiles.BoundedProfile (HaarPathProfiles.Color d) m => p.val.last) hprofile
    simpa only [coreChainProfile_last,SamePattern.coreChainEquiv_apply,
      SamePattern.coreChainMap_val,List.getLast_map] using he
  have hfix : ∀ i ∈ S, f i=g i := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    change color (c.val.get i)=color (h.samePattern.dartPerm (c.val.get i))
    rcases hi' with hi | hi
    · have he : c.val.get i=c.val.head (P.toCore_nonempty c.property.1) := by
        simp only [List.get_eq_getElem,List.head_eq_getElem,hi]
      simpa only [he] using hfirst
    · have he : c.val.get i=c.val.getLast (P.toCore_nonempty c.property.1) := by
        simp only [List.get_eq_getElem,List.getLast_eq_getElem]
        congr 1
        omega
      simpa only [he] using hlast
  obtain ⟨σ,hσ,hS⟩ := exists_perm_labels_fix f g S hcount hfix
  exact ⟨σ,hσ,fun i hi => hS i (by simp [S,hi])⟩

end Chains
end Nonadditivity.HaarProfilePermutations
