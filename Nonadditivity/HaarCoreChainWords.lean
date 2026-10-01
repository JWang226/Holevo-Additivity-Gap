/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainLabels
import Nonadditivity.HaarPathRefined

/-! # The actual reduced profile word on every oriented core chain -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarPathGraph.Path

open HaarPathProfiles HaarProfileCoefficient
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- Reversing a graph chain gives exactly the inverse signed word. -/
theorem reverse_chain_colors (c : P.CoreChain) :
    (P.coreChainReverse c).val.map color = FreeGroup.invRev (c.val.map color) := by
  change (c.val.reverse.map reverse).map color = _
  simp only [FreeGroup.invRev,List.map_map,List.map_reverse]
  rfl

/-- Reducedness is preserved by inverse-word reversal. -/
theorem reduced_invRev {α : Type*} [DecidableEq α] {l : List (α × Bool)}
    (h : FreeGroup.IsReduced l) : FreeGroup.IsReduced (FreeGroup.invRev l) := by
  apply FreeGroup.isReduced_iff_reduce_eq.mpr
  rw [FreeGroup.reduce_invRev,h.reduce_eq]

/-- Every core chain is reduced, including an orientation not visited by the path. -/
theorem coreChain_colors_reduced (c : P.CoreChain) : FreeGroup.IsReduced (c.val.map color) := by
  have hq := P.toCore_mem c.property.1
    (List.head_mem (P.toCore_nonempty c.property.1))
  obtain ⟨i,_⟩ := P.dart_eq_traversal_or_reverse _ hq
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  obtain ⟨cs,hcs⟩ := P.exists_traversal_chain_decomposition hm
  rcases P.chain_or_reverse_mem_decomposition cs hcs c with hc | hc
  · exact P.chain_colors_reduced cs hcs c hc
  · have hr := reduced_invRev (P.chain_colors_reduced cs hcs (P.coreChainReverse c) hc)
    simpa only [P.reverse_chain_colors, FreeGroup.invRev_invRev] using hr

/-- The literal word on a core chain is an element of its finite profile palette. -/
def coreProfileWord (c : P.CoreChain) : Words d c.val.length (P.coreChainProfile c).val := by
  refine ⟨fun i => color c.val[i], ?_⟩
  have he : List.ofFn (fun i : Fin c.val.length => color c.val[i]) = c.val.map color :=
    List.ofFn_getElem_eq_map c.val color
  rw [he]
  refine ⟨P.coreChain_colors_reduced c, ?_⟩
  cases hc : c.val with
  | nil => exact (P.toCore_nonempty c.property.1 hc).elim
  | cons a l =>
      simp [coreChainProfile, hc, wordProfile, List.getLast?_eq_getLast_of_ne_nil]
      intro x
      constructor <;> simp only [List.count, beq_eq_decide]

@[simp] theorem coreProfileWord_word (c : P.CoreChain) :
    word (P.coreProfileWord c) = P.chainWord c := by
  unfold word chainWord coreProfileWord
  congr 1
  exact List.ofFn_getElem_eq_map c.val color

@[simp] theorem coreWord_toWord (c : P.CoreChain) :
    (P.chainWord c).toWord = c.val.map color :=
  FreeGroup.toWord_mk.trans (P.coreChain_colors_reduced c).reduce_eq

/-- The two orientations evaluate to inverse actual group words. -/
theorem chainWord_reverse (c : P.CoreChain) :
    P.chainWord (P.coreChainReverse c) = (P.chainWord c)⁻¹ := by
  unfold chainWord
  rw [P.reverse_chain_colors,FreeGroup.inv_mk]

end Nonadditivity.HaarPathGraph.Path
