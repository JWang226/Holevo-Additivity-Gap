/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainReverseAddress
import Nonadditivity.HaarPathProfileReverse
import Nonadditivity.HaarCoreChainWords
import Nonadditivity.HaarPathInternalColors

/-! # Reconstructing graph colors from compatible reduced chain words -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Nonadditivity.HaarPathGraph.Path

open HaarPathProfiles HaarProfileCoefficient
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- A compatible assignment of actual reduced profile words to all orientations.
Only opposite orientations are related; the unoriented edges remain independent. -/
structure ChainColoring where
  value (c : P.CoreChain) : Words d c.val.length (P.coreChainProfile c).val
  reversal (p : P.ChainPosition) :
    (value (P.reversePosition p).1).val (P.reversePosition p).2 =
      flipColor ((value p.1).val p.2)

namespace ChainColoring
variable {P} (F : P.ChainColoring)

def color (q : P.darts) : Color d := P.recolor (fun c => (F.value c).val) q

@[simp] theorem color_position (c : P.CoreChain) (i : Fin c.val.length) :
    F.color (P.positionDart ⟨c,i⟩) = (F.value c).val i := P.recolor_position _ c i

/-- Opposite graph incidences receive opposite signed colors. -/
theorem color_reverse (q : P.darts) :
    F.color ⟨reverse q.val,P.reverse_mem q.property⟩ = flipColor (F.color q) := by
  obtain ⟨p,rfl⟩ := P.positionDart_surjective q
  have he : (⟨reverse (P.positionDart p).val,P.reverse_mem (P.positionDart p).property⟩ : P.darts) =
      P.positionDart (P.reversePosition p) := (P.positionDart_reversePosition p).symm
  rw [he,color_position,color_position]
  exact F.reversal p


/-- Every noninitial position of a stopped chain has non-core source. -/
theorem source_not_core_of_pos (c : P.CoreChain) (i : Fin c.val.length)
    (hi : 0 < i.val) : source c.val[i] ∉ P.coreVertices := by
  apply P.toCore_tail_source_not_core c.property.1
  have ht : i.val-1 < c.val.tail.length := by simp only [List.length_tail]; omega
  have hm := List.get_mem c.val.tail (⟨i.val-1,ht⟩ : Fin c.val.tail.length)
  simpa only [List.get_eq_getElem,List.getElem_tail,Nat.sub_add_cancel hi] using hm

/-- The initial source of a complete chain belongs to the core. -/
theorem source_core_of_zero (c : P.CoreChain) (i : Fin c.val.length)
    (hi : i.val=0) : source c.val[i] ∈ P.coreVertices := by
  obtain ⟨a,l,he,ha⟩ := c.property.2
  change source c.val[i.val] ∈ P.coreVertices
  simpa only [he,hi,List.getElem_cons_zero] using ha

/-- Endpoint profiles fix all outgoing signed colors at core vertices. -/
theorem color_eq_of_source_core (q : P.darts) (hq : source q.val∈P.coreVertices) :
    F.color q=HaarPathGraph.color q.val := by
  obtain ⟨⟨c,i⟩,rfl⟩ := P.positionDart_surjective q
  have hi : i.val=0 := by
    by_contra h
    exact source_not_core_of_pos (P := P) c i (Nat.pos_of_ne_zero h) hq
  rw [F.color_position]
  have hh := (F.value c).property.2.1
  have hn : 0 < c.val.length := by omega
  have hf : (List.ofFn (F.value c).val).head?=some ((F.value c).val ⟨0,hn⟩) := by
    rw [List.head?_eq_some_head (by simpa using Nat.ne_of_gt hn),List.head_ofFn]
  rw [hf] at hh
  have hi' : i=⟨0,hn⟩ := Fin.ext hi
  rw [Option.some.injEq] at hh
  rw [hi',hh,P.coreChainProfile_first]
  simp only [positionDart,List.get_eq_getElem,List.head_eq_getElem]

/-- Adjacent letters in an assigned reduced profile cannot cancel. -/
theorem value_step (c : P.CoreChain) (i : ℕ) (hi : i + 1 < c.val.length) :
    (F.value c).val ⟨i+1,hi⟩ ≠ flipColor ((F.value c).val ⟨i,by omega⟩) := by
  intro he
  have hr := List.isChain_iff_getElem.mp (F.value c).property.1 i
    (by simpa only [List.length_ofFn] using hi)
  simp only [List.getElem_ofFn] at hr
  rw [he] at hr
  have hb := hr rfl
  cases h : ((F.value c).val ⟨i,by omega⟩).2 <;> simp [flipColor,h] at hb

/-- Recoloring preserves injectivity among the two outgoing darts of every
internal vertex, because their colors are adjacent reduced letters. -/
theorem color_injective_internal {q r : P.darts}
    (hq : source q.val∉P.coreVertices) (hs : source q.val=source r.val)
    (hc : F.color q=F.color r) : q=r := by
  by_contra hne
  obtain ⟨⟨c,i⟩,hqi⟩ := P.positionDart_surjective q
  have hi : 0 < i.val := by
    by_contra h
    have hi0 : i.val=0 := by omega
    exact hq (hqi ▸ source_core_of_zero (P := P) c i hi0)
  let j : Fin c.val.length := ⟨i.val-1,by omega⟩
  have hji : j.val+1=i.val := by dsimp [j]; omega
  have ht := P.toCore_step c.property.1 j.val (by omega)
  have he : c.val[j.val+1]=q.val := by
    simpa only [hji] using congrArg Subtype.val hqi
  rw [he] at ht
  let a := P.positionDart ⟨c,j⟩
  have hra : r.val=reverse a.val := by
    apply P.next_dart_unique q.property r.property (P.reverse_mem a.property) hq hs ht.1.symm
    · exact fun h => hne (Subtype.ext h.symm)
    · exact ht.2.symm
  have hr : r=⟨reverse a.val,P.reverse_mem a.property⟩ := Subtype.ext hra
  rw [hr,F.color_reverse,←hqi,F.color_position,F.color_position] at hc
  have hstep := F.value_step c j.val (by omega)
  have hi' : (⟨j.val+1,by omega⟩ : Fin c.val.length)=i := Fin.ext hji
  rw [hi'] at hstep
  exact hstep hc

/-- The assigned profile words preserve the actual local color equality
kernel, which is the defining color constraint of the coarse path class. -/
theorem color_kernel (q r : P.darts) (hs : source q.val=source r.val) :
    F.color q=F.color r ↔ HaarPathGraph.color q.val=HaarPathGraph.color r.val := by
  by_cases hq : source q.val∈P.coreVertices
  · rw [F.color_eq_of_source_core q hq,F.color_eq_of_source_core r (hs ▸ hq)]
  · constructor
    · intro hc
      exact congrArg (fun q : P.darts => HaarPathGraph.color q.val) (F.color_injective_internal hq hs hc)
    · intro hc
      have he := P.internal_color_injective q.property r.property hq hs hc
      exact congrArg F.color (Subtype.ext he)

end ChainColoring
end Nonadditivity.HaarPathGraph.Path
