/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathInternalColors
import Nonadditivity.HaarCoreChainReverseAddress

/-! # Exact core endpoints in chain position coordinates

A complete suppressed chain meets the core only at its initial source
and final target. These equivalences also cover one-edge chains and loops.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

theorem coreChain_source_mem_core_iff (c : P.CoreChain) (i : Fin c.val.length) :
    source (c.val.get i) ∈ P.coreVertices ↔ i.val=0 := by
  constructor
  · intro hc
    by_contra hi
    have ht : i.val-1<c.val.tail.length := by
      simp only [List.length_tail]
      have hi' := i.isLt
      omega
    have he : c.val.tail.get ⟨i.val-1,ht⟩=c.val.get i := by
      rw [List.get_tail]
      congr 1
      apply Fin.ext
      change i.val-1+1=i.val
      omega
    have hm : c.val.get i ∈ c.val.tail := he ▸ List.get_mem c.val.tail ⟨i.val-1,ht⟩
    exact P.toCore_tail_source_not_core c.property.1 hm hc
  · intro hi
    obtain ⟨q,l,he,hq⟩ := c.property.2
    have hg : c.val.get i=q := by simp [List.get_eq_getElem,he,hi]
    simpa only [hg] using hq

theorem coreChain_reverse_source_mem_core_iff (c : P.CoreChain) (i : Fin c.val.length) :
    source (reverse (c.val.get i)) ∈ P.coreVertices ↔ i.val+1=c.val.length := by
  let j : Fin (P.coreChainReverse c).val.length :=
    Fin.cast (P.coreChainReverse_length c).symm i.rev
  have he : (P.coreChainReverse c).val.get j=reverse (c.val.get i) := by
    exact congrArg Subtype.val (P.positionDart_reversePosition ⟨c,i⟩)
  rw [← he,P.coreChain_source_mem_core_iff]
  simp only [j,Fin.val_cast,Fin.val_rev]
  have hi := i.isLt
  omega

end Nonadditivity.HaarPathGraph.Path
