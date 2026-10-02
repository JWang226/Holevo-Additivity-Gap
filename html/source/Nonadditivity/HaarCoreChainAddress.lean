/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainLabels

/-! # Exact coordinates of graph darts on suppressed chains

The positions of all oriented core chains partition the literal graph darts.
The address map and its inverse are actual bijections, not chosen encodings
with a coverage or reconstruction premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarPathGraph.Path

variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

abbrev ChainPosition := Σ c : P.CoreChain, Fin c.val.length

def positionDart (p : P.ChainPosition) : P.darts :=
  ⟨p.1.val.get p.2, P.toCore_mem p.1.property.1 (List.get_mem _ _)⟩

/-- A literal oriented dart determines both its chain and its position. -/
theorem positionDart_injective : Function.Injective P.positionDart := by
  rintro ⟨c,i⟩ ⟨c',i'⟩ he
  have heq : c.val.get i = c'.val.get i' := congrArg Subtype.val he
  have hc : c = c' := P.coreChain_eq_of_common_dart c c'
    (List.get_mem _ _) (heq.symm ▸ List.get_mem _ _)
  subst c'
  have hi : i = i' := (P.toCore_nodup c.property.1).injective_get heq
  subst i'
  rfl

/-- Every actual graph dart lies on one of the complete oriented core chains. -/
theorem positionDart_surjective : Function.Surjective P.positionDart := by
  intro q
  obtain ⟨i,hi | hi⟩ := P.dart_eq_traversal_or_reverse q.val q.property
  all_goals
    have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
    obtain ⟨cs,hcs⟩ := P.exists_traversal_chain_decomposition hm
    have hmem : P.traversal i ∈ (cs.map Subtype.val).flatten := by
      rw [hcs]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    obtain ⟨l,hl,hil⟩ := List.mem_flatten.mp hmem
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hl
  · have hqc : q.val ∈ c.val := hi.symm ▸ hil
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hqc
    exact ⟨⟨c,j⟩,Subtype.ext hj⟩
  · have hqc : q.val ∈ (P.coreChainReverse c).val := by
      rw [hi]
      exact List.mem_map.mpr ⟨P.traversal i,List.mem_reverse.mpr hil,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hqc
    exact ⟨⟨P.coreChainReverse c,j⟩,Subtype.ext hj⟩

/-- The canonical finite position address of each oriented dart. -/
def positionEquiv : P.ChainPosition ≃ P.darts :=
  Equiv.ofBijective P.positionDart ⟨P.positionDart_injective,P.positionDart_surjective⟩

@[simp] theorem positionEquiv_apply (p : P.ChainPosition) : P.positionEquiv p = P.positionDart p := rfl

/-- Recolor every graph dart using arbitrary prescribed lists on the chains. -/
def recolor (F : ∀ c : P.CoreChain, Fin c.val.length → HaarPathProfiles.Color d)
    (q : P.darts) : HaarPathProfiles.Color d :=
  F (P.positionEquiv.symm q).1 (P.positionEquiv.symm q).2

@[simp] theorem recolor_position (F : ∀ c : P.CoreChain, Fin c.val.length → HaarPathProfiles.Color d)
    (c : P.CoreChain) (i : Fin c.val.length) :
    P.recolor F (P.positionDart ⟨c,i⟩) = F c i := by
  change F (P.positionEquiv.symm (P.positionEquiv ⟨c,i⟩)).1
    (P.positionEquiv.symm (P.positionEquiv ⟨c,i⟩)).2 = _
  rw [Equiv.symm_apply_apply]

/-- Reading back a recolored chain returns exactly its assigned finite word. -/
theorem recolor_chain (F : ∀ c : P.CoreChain, Fin c.val.length → HaarPathProfiles.Color d)
    (c : P.CoreChain) :
    List.ofFn (fun i : Fin c.val.length => P.recolor F (P.positionDart ⟨c,i⟩)) =
      List.ofFn (F c) := by
  simp only [P.recolor_position]

end Nonadditivity.HaarPathGraph.Path
