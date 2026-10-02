/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChainPartition

/-! # Bounded word profiles of actual suppressed chains -/
noncomputable section
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- A maximal core chain visits each unoriented colored edge at most once. -/
theorem coreChain_edges_nodup (c : P.CoreChain) : (c.val.map Prod.fst).Nodup := by
  apply List.Nodup.map_on _ (P.toCore_nodup c.property.1)
  intro q hq q' hq' he
  obtain ⟨e,b⟩ := q
  obtain ⟨e',b'⟩ := q'
  change e=e' at he
  subst e'
  cases b <;> cases b'
  · rfl
  · exact (P.coreChain_not_both_orientations c hq (by simpa [reverse] using hq')).elim
  · exact (P.coreChain_not_both_orientations c hq (by simpa [reverse] using hq')).elim
  · rfl

/-- A suppressed chain has length at most the original path length. -/
theorem coreChain_length_le (c : P.CoreChain) : c.val.length ≤ m := by
  have hsub : (c.val.map Prod.fst).toFinset ⊆ P.edges := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact (Finset.mem_product.mp (P.toCore_mem c.property.1 hq)).1
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (P.coreChain_edges_nodup c),List.length_map] at hc
  have he := List.toFinset_card_le P.edgeList
  rw [P.edgeList_length] at he
  exact hc.trans he

/-- The actual signed-color profile of a suppressed chain, with its required
length bound proved from the original graph. -/
def coreChainProfile (c : P.CoreChain) : HaarPathProfiles.BoundedProfile
    (HaarPathProfiles.Color d) m := by
  let a := c.val.head (P.toCore_nonempty c.property.1)
  let l := c.val.tail
  have he : c.val=a::l := (List.cons_head_tail (P.toCore_nonempty c.property.1)).symm
  refine ⟨HaarPathProfiles.wordProfile (color a) (l.map color), color a, l.map color, ?_, rfl⟩
  have hl := P.coreChain_length_le c
  simpa [he] using hl

end Nonadditivity.HaarPathGraph.Path
