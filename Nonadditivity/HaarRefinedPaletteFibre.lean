/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarChainColoringFibre
import Nonadditivity.HaarChainColoringPalettes

/-! # Exact refined class sums over independent reduced profile words

This is the literal geometric parametrization needed by the coefficient bound:
vertex injections and independent reduced words on unoriented core chains.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarPathGraph.Path
open scoped BigOperators
open HaarPathGraph HaarPathClasses HaarPathProfiles HaarProfileCoefficient
  HaarRefinedVertexFibre HaarPathVertexFibre
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- Independent profile words parametrize the entire actual refined color fibre. -/
def paletteColorFibreEquiv : P.ChainPalette ≃ HaarRefinedVertexFibre.ColorFibre P :=
  P.chainPaletteEquiv.trans ChainColoring.colorFibreEquiv

/-- Exact independent-profile expansion of a genuine refined class sum. -/
theorem sum_refined_fibre_eq_palettes {R : Type*} [AddCommMonoid R]
    (f : (Fin m → Color d) → R) :
    ∑ Q : HaarRefinedVertexFibre.Fibre P, f Q.val.colors =
      Fintype.card (VertexLabels P) •
        ∑ σ : P.ChainPalette, f (P.paletteColoring σ).path.colors := by
  rw [HaarRefinedVertexFibre.sum_fibre_colors]
  rw [←(P.paletteColorFibreEquiv).sum_comp]
  rfl

namespace ChainColoring
variable {P} (F : P.ChainColoring)

@[simp] theorem chainWord_map (c : P.CoreChain) :
    F.path.chainWord (F.samePattern.coreChainEquiv c)=word (F.value c) := by
  unfold Path.chainWord word
  rw [F.chain_colors]

/-- Reading the assigned reduced words along the actual occurrence sequence
recovers the complete recolored path word exactly. -/
theorem assignedWords_flatMap (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList) :
    (cs.map (fun c => word (F.value c))).flatMap FreeGroup.toWord=
      List.ofFn F.path.colors := by
  have hh := F.path.chainWords_flatMap (cs.map F.samePattern.coreChainEquiv)
    (F.samePattern.chain_decomposition_map cs hcs)
  simpa only [List.map_map,Function.comp_def,F.chainWord_map] using hh

/-- All reconstructed segment words concatenate without cancellation. -/
theorem assignedWords_reduced (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList) :
    FreeGroup.IsReduced ((cs.map (fun c => word (F.value c))).flatMap FreeGroup.toWord) := by
  rw [F.assignedWords_flatMap cs hcs]
  exact F.path.colorList_reduced

/-- The literal product of assigned chain words is the full recolored word. -/
theorem assignedWords_prod (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList) :
    (cs.map (fun c => word (F.value c))).prod=FreeGroup.mk (List.ofFn F.path.colors) := by
  rw [←F.assignedWords_flatMap cs hcs,HaarNonbacktracking.mk_flatMap_toWord]

/-- The actual power coefficient on the reconstructed path factors through
its chosen profile words with the exact positive duration expansion. -/
theorem coefficient_factorization {R : Type*} [Ring R]
    (A : MonoidAlgebra R (FreeGroup (Fin d)))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (c : P.CoreChain) (cs : List P.CoreChain)
    (hcs : ((c::cs).map Subtype.val).flatten=P.traversalList) (n : ℕ) :
    (A^n) (FreeGroup.mk (List.ofFn F.path.colors))=
      ∑ times ∈ HaarTimeCompositions.compositions cs.length n,
        HaarNonbacktracking.segmentedProduct A (word (F.value c))
          (cs.map (fun c => word (F.value c))) times := by
  have hh := F.path.coefficient_factorization_chains A hA
    (F.samePattern.coreChainEquiv c) (cs.map F.samePattern.coreChainEquiv)
    (F.samePattern.chain_decomposition_map (c::cs) hcs) n
  simpa only [List.length_map,List.map_map,Function.comp_def,F.chainWord_map] using hh

end ChainColoring
end Nonadditivity.HaarPathGraph.Path
