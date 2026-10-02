/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarChainColoringPath

/-! # Exact refined color fibre as compatible actual profile assignments -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathGraph HaarPathClasses HaarPathProfiles HaarProfileCoefficient
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
variable {P : Path V d m}

/-- Read the chosen profile word from an actual path in the refined class. -/
def refinedChainWord {Q : Path V d m} (h : RefinedPattern P Q) (c : P.CoreChain) :
    Words d c.val.length (P.coreChainProfile c).val := by
  let v : Fin c.val.length → Color d := fun i => color (h.samePattern.dartPerm c.val[i])
  have he : List.ofFn v=(h.samePattern.coreChainEquiv c).val.map color := by
    simp only [SamePattern.coreChainEquiv_apply,SamePattern.coreChainMap_val,List.map_map]
    simpa only [v,Fin.getElem_fin,Function.comp_def] using
      List.ofFn_getElem_eq_map c.val (color ∘ h.samePattern.dartPerm)
  refine ⟨v,?_⟩
  rw [he,h.profile_eq c]
  have hp := (Q.coreProfileWord (h.samePattern.coreChainEquiv c)).property
  have hw : List.ofFn (Q.coreProfileWord (h.samePattern.coreChainEquiv c)).val=
      (h.samePattern.coreChainEquiv c).val.map color :=
    by
      simpa only [Path.coreProfileWord,Fin.getElem_fin] using
        List.ofFn_getElem_eq_map (h.samePattern.coreChainEquiv c).val color
  simpa only [hw] using hp

/-- A refined path induces compatible words on all chain orientations. -/
def refinedChainColoring {Q : Path V d m} (h : RefinedPattern P Q) : P.ChainColoring where
  value := refinedChainWord h
  reversal p := by
    change color (h.samePattern.dartPerm (P.positionDart (P.reversePosition p)).val)=
      flipColor (color (h.samePattern.dartPerm (P.positionDart p).val))
    rw [P.positionDart_reversePosition,h.samePattern.dartPerm_reverse (P.positionDart p).property]
    rfl

@[simp] theorem refinedChainColoring_color {Q : Path V d m} (h : RefinedPattern P Q)
    (q : P.darts) : (refinedChainColoring h).color q=color (h.samePattern.dartPerm q.val) := by
  obtain ⟨⟨c,i⟩,rfl⟩ := P.positionDart_surjective q
  rw [ChainColoring.color_position]
  rfl

/-- Reconstructing all profile words of a refined path recovers that path when
its vertex labels are fixed. -/
theorem refinedChainColoring_path {Q : Path V d m} (h : RefinedPattern P Q)
    (hv : Q.vertex=P.vertex) : (refinedChainColoring h).path=Q := by
  apply Path.ext_data
  · exact hv.symm
  · funext i
    rw [ChainColoring.path_colors,refinedChainColoring_color,h.samePattern.dartPerm_traversal]
    exact color_dart _ _ _

namespace ChainColoring

@[ext] theorem ext_value {F G : P.ChainColoring} (h : ∀ c, F.value c=G.value c) : F=G := by
  cases F with
  | mk f hf => cases G with
    | mk g hg =>
      have he : f=g := funext h
      subst g
      rfl

/-- A reconstructed path determines the assigned word at every graph dart. -/
theorem path_injective : Function.Injective (path (P := P)) := by
  intro F G he
  have hc (q : P.darts) : F.color q=G.color q := by
    obtain ⟨i,hi | hi⟩ := P.dart_eq_traversal_or_reverse q.val q.property
    · have hq : q=⟨P.traversal i,P.traversal_mem i⟩ := Subtype.ext hi
      rw [hq]
      exact congrArg (fun R : Path V d m => R.colors i) he
    · have hq : q=⟨reverse (P.traversal i),P.reverse_mem (P.traversal_mem i)⟩ := Subtype.ext hi
      rw [hq,F.color_reverse ⟨P.traversal i,P.traversal_mem i⟩,
        G.color_reverse ⟨P.traversal i,P.traversal_mem i⟩]
      exact congrArg flipColor (congrArg (fun R : Path V d m => R.colors i) he)
  apply ext_value
  intro c
  apply Subtype.ext
  funext i
  simpa only [color_position] using hc (P.positionDart ⟨c,i⟩)

/-- Compatible reduced chain words are exactly all literal fixed-vertex paths
of the refined class. -/
def colorFibreEquiv : P.ChainColoring ≃ HaarRefinedVertexFibre.ColorFibre P where
  toFun F := F.colorFibre
  invFun C := refinedChainColoring C.property.2
  left_inv F := path_injective (refinedChainColoring_path F.refinedPattern F.path_vertex)
  right_inv C := Subtype.ext (refinedChainColoring_path C.property.2 C.property.1)

end ChainColoring
end Nonadditivity.HaarPathGraph.Path
