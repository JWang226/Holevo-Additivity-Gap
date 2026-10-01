/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarChainColoring
import Nonadditivity.HaarPathRecoloring
import Nonadditivity.HaarRefinedVertexFibre

/-! # Actual paths reconstructed from reduced chain-profile assignments -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Nonadditivity.HaarPathGraph.Path.ChainColoring
open HaarPathGraph HaarPathClasses HaarPathProfiles HaarProfileCoefficient
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
variable {P : Path V d m} (F : P.ChainColoring)

/-- A compatible reduced-word assignment gives an actual closed reduced path. -/
def path : Path V d m :=
  HaarPathRecoloring.recolorPath P F.color F.color_reverse F.color_kernel

theorem samePattern : SamePattern P F.path :=
  HaarPathRecoloring.recolorPath_samePattern P F.color F.color_reverse F.color_kernel

@[simp] theorem path_vertex : F.path.vertex=P.vertex := rfl
@[simp] theorem path_colors (i : Fin m) :
    F.path.colors i=F.color ⟨P.traversal i,P.traversal_mem i⟩ := rfl

@[simp] theorem color_dartPerm (q : P.darts) :
    HaarPathGraph.color (F.samePattern.dartPerm q.val)=F.color q := by
  rw [HaarPathRecoloring.recolorPath_dartPerm]
  exact color_dart _ _ _

/-- The reconstructed chain has precisely the assigned word, at every position. -/
theorem chain_colors (c : P.CoreChain) :
    (F.samePattern.coreChainEquiv c).val.map HaarPathGraph.color=List.ofFn (F.value c).val := by
  simp only [SamePattern.coreChainEquiv_apply,SamePattern.coreChainMap_val,List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_ofFn]
    have he := F.color_dartPerm (P.positionDart ⟨c,⟨i,by simpa using hi⟩⟩)
    rw [F.color_position] at he
    exact he

/-- Endpoint and count constraints of the palette prove actual refined membership. -/
theorem refinedPattern : RefinedPattern P F.path := by
  refine ⟨F.samePattern,?_⟩
  intro c
  apply Subtype.ext
  apply Profile.ext
  · have hh := (F.value c).property.2.1
    rw [←F.chain_colors c] at hh
    rw [List.head?_map,List.head?_eq_some_head
      (F.path.toCore_nonempty (F.samePattern.coreChainEquiv c).property.1)] at hh
    simpa only [Option.map_some,Option.some.injEq,Path.coreChainProfile_first] using hh.symm
  · have hh := (F.value c).property.2.2.1
    rw [←F.chain_colors c] at hh
    rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil
      (F.path.toCore_nonempty (F.samePattern.coreChainEquiv c).property.1)] at hh
    simpa only [Option.map_some,Option.some.injEq,Path.coreChainProfile_last] using hh.symm
  · funext a
    rw [F.path.coreChainProfile_count (F.samePattern.coreChainEquiv c),F.chain_colors]
    exact ((F.value c).property.2.2.2 a).symm

/-- The path produced from the assignment belongs to the literal fixed-vertex
refined class, with no realizability hypothesis on the chosen words. -/
def colorFibre : HaarRefinedVertexFibre.ColorFibre P :=
  ⟨F.path,F.path_vertex,F.refinedPattern⟩

end Nonadditivity.HaarPathGraph.Path.ChainColoring
