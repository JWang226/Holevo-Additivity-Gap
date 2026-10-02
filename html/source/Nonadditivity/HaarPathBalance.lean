/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathExpansion

/-! # Local phase balance forces repeated visits

A vertex visited just once away from the root would force a consecutive
inverse pair of colors. Consequently a nonzero Haar path weight can have
at most half as many vertices as steps.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathGraph.Path
open scoped BigOperators
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : HaarPathGraph.Path V d m)

def visitCount (v : V) : ℕ := (Finset.univ.filter (fun i : Fin m => P.vertex i.castSucc=v)).card

def outgoingCount (c : HaarPathProfiles.Color d) (v : V) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => P.vertex i.castSucc=v ∧ P.colors i=c)).card

def incomingCount (c : HaarPathProfiles.Color d) (v : V) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => P.vertex i.succ=v ∧ P.colors i=c)).card

/-- The row/column phase selection rule in the path's own vertex coordinates. -/
def LocallyBalanced : Prop :=
  ∀ c v, P.outgoingCount c v=P.incomingCount (HaarPathGraph.flipColor c) v

lemma visitCount_pos {v : V} (hv : v ∈ P.vertices) : 0 < P.visitCount v := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
  exact Finset.card_pos.mpr ⟨i,by simp [visitCount,hi]⟩

lemma sum_visitCount : ∑ v ∈ P.vertices, P.visitCount v=m := by
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := P.vertices)
    (f := fun i : Fin m => P.vertex i.castSucc) (fun i _ => P.start_mem i)
  simpa [visitCount] using h.symm

lemma two_le_visitCount_of_balanced (hb : P.LocallyBalanced)
    {v : V} (hv : v ∈ P.vertices) (hne : v ≠ P.vertex 0) : 2 ≤ P.visitCount v := by
  have hpos := P.visitCount_pos hv
  by_contra htwo
  have hone : P.visitCount v=1 := by omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hone
  have him : i ∈ Finset.univ.filter (fun i : Fin m => P.vertex i.castSucc=v) := by
    rw [hi]
    exact Finset.mem_singleton_self _
  have hiv : P.vertex i.castSucc=v := (Finset.mem_filter.mp him).2
  have hi0 : 0 < i.val := by
    by_contra hn
    have he : i.castSucc=0 := Fin.ext (by simp; omega)
    exact hne (hiv.symm.trans (congrArg P.vertex he))
  let j : Fin m := ⟨i.val-1,by omega⟩
  have hji : j.val+1=i.val := by dsimp [j]; omega
  have hjs : j.succ=i.castSucc := Fin.ext hji
  have hjv : P.vertex j.succ=v := hjs ▸ hiv
  have hflip : HaarPathGraph.flipColor (HaarPathGraph.flipColor (P.colors j))=P.colors j := by
    cases hc : P.colors j with | mk a b => cases b <;> rfl
  have hin : 0 < P.incomingCount (P.colors j) v := by
    exact Finset.card_pos.mpr ⟨j,by simp [incomingCount,hjv]⟩
  have hout : 0 < P.outgoingCount (HaarPathGraph.flipColor (P.colors j)) v := by
    rw [hb, hflip]
    exact hin
  obtain ⟨k,hk⟩ := Finset.card_pos.mp hout
  have hkparts := (Finset.mem_filter.mp hk).2
  have hki : k=i := by
    have hm : k ∈ Finset.univ.filter (fun i : Fin m => P.vertex i.castSucc=v) := by
      simp [hkparts.1]
    rw [hi] at hm
    exact Finset.mem_singleton.mp hm
  exact P.reduced j i hji (hki ▸ hkparts.2)

/-- Every non-root vertex requires two visits, while the root requires one. -/
theorem twice_vertices_le_length_add_one_of_balanced (hb : P.LocallyBalanced) :
    2*P.vertices.card ≤ m+1 := by
  have hpoint (v : V) (hv : v ∈ P.vertices) :
      2 ≤ P.visitCount v + (if v=P.vertex 0 then 1 else 0) := by
    by_cases h : v=P.vertex 0
    · have hp := P.visitCount_pos hv
      simp only [if_pos h]
      omega
    · simpa [h] using P.two_le_visitCount_of_balanced hb hv h
  have hs := Finset.sum_le_sum hpoint
  have hroot : (P.vertices.filter (fun v => v=P.vertex 0)).card ≤ 1 := by
    apply (Finset.card_le_card (show P.vertices.filter (fun v => v=P.vertex 0) ⊆ {P.vertex 0} from ?_)).trans
    · simp
    · intro v hv
      simpa using (Finset.mem_filter.mp hv).2
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    Finset.sum_ite, Nat.mul_one] at hs
  rw [P.sum_visitCount] at hs
  omega

theorem vertices_le_half_of_balanced (hb : P.LocallyBalanced) (hm : Even m) :
    P.vertices.card ≤ m/2 := by
  have h := P.twice_vertices_le_length_add_one_of_balanced hb
  obtain ⟨k,hk⟩ := hm
  omega

end Nonadditivity.HaarPathGraph.Path
