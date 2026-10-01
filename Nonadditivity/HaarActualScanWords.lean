/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarSkeletonSegmentation
import Nonadditivity.HaarPaletteDecoder
import Nonadditivity.HaarRefinedPaletteFibre
import Nonadditivity.HaarReducedChunks

/-! # Actual decoded chunks of the reconstructed refined path

The decoder's reversed scan is exactly the consecutive occurrence partition
of the original path. Its chunks are reduced and nontrivial, and their product
is the literal recolored word, for every independent profile assignment.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarActualScanWords
open HaarPathGraph HaarProfileCoefficient HaarSkeletonSegmentation HaarPaletteDecoder
  NoncommutativeCS HaarNonbacktracking

variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
    (P : Path V d m) (cs : List P.CoreChain)
    (R : EndpointSkeleton P.unorientedChains
      (Fin.elim0 : Fin 0 → P.unorientedChains) (Fin.elim0 : Fin 0 → P.unorientedChains))

theorem scanWords_eq_actual_chunks
    (hw : R.word=(cs.map P.chainLabel).reverse) (σ : P.ChainPalette) :
    scanWords R (decode (blockDirections P (R.occurrenceBlocks cs.reverse))) (chainEmbed P σ) =
      (R.occurrenceBlocks cs.reverse).map
        (fun block => (block.reverse.map (fun c => word (P.paletteWord σ c))).prod) := by
  have hmap := R.map_occurrenceBlocks P.chainLabel cs.reverse
    (by simpa only [List.map_reverse] using hw.symm)
  apply List.ext_getElem
  · simp [scanWords]
  · intro k hk hk'
    have hkB : k<(R.occurrenceBlocks cs.reverse).length := by simpa using hk'
    have hkR : k<R.blocks.length := by simpa [scanWords] using hk
    have hget : R.blocks[k]=(R.occurrenceBlocks cs.reverse)[k].map P.chainLabel := by
      have he := congrArg (fun ls : List (List P.unorientedChains) => ls.getD k []) hmap
      dsimp only at he
      rw [List.getD_eq_getElem _ _ (by simpa using hkB),
        List.getD_eq_getElem _ _ hkR,List.getElem_map] at he
      exact he.symm
    simp only [scanWords,List.getElem_mapIdx,List.getElem_map]
    rw [hget]
    simp only [List.map_map,Function.comp_def]
    exact decode_actual_block P σ (R.occurrenceBlocks cs.reverse) k hkB

/-- Every remaining reduced-word hypothesis of the analytic segmented
coefficient theorem holds for the actual independent profile palettes. -/
theorem actualScanWords_spec
    (hcs : (cs.map Subtype.val).flatten=P.traversalList)
    (hR : R.Compressed) (hw : R.word=(cs.map P.chainLabel).reverse)
    (σ : P.ChainPalette) :
    let gs := (scanWords R
      (decode (blockDirections P (R.occurrenceBlocks cs.reverse))) (chainEmbed P σ)).reverse
    gs.prod=FreeGroup.mk (List.ofFn (P.paletteColoring σ).path.colors) ∧
      (∀ g∈gs, g≠1) ∧ FreeGroup.IsReduced (gs.flatMap FreeGroup.toWord) := by
  let φ : P.CoreChain → FreeGroup (Fin d) := fun c => word (P.paletteWord σ c)
  let chunks := ((R.occurrenceBlocks cs.reverse).map List.reverse).reverse
  have hw' : cs.reverse.map P.chainLabel=R.word := by
    simpa only [List.map_reverse] using hw.symm
  have hflat : chunks.flatten=cs := R.flatten_map_reversed_occurrenceBlocks P.chainLabel cs hw'
  have hchunks : ∀ c∈chunks, c≠[] := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
    exact fun he => R.occurrenceBlocks_nonempty hR P.chainLabel cs.reverse hw' b hb
      (List.reverse_eq_nil_iff.mp he)
  have hred : FreeGroup.IsReduced ((cs.map φ).flatMap FreeGroup.toWord) :=
    (P.paletteColoring σ).assignedWords_reduced cs hcs
  have hne : ∀ c∈cs, φ c≠1 := fun c _ => word_ne_one (P.paletteWord σ c)
  have hs := occurrence_chunk_spec cs chunks φ hflat hred hne hchunks
  dsimp only at hs
  have hg : (scanWords R
      (decode (blockDirections P (R.occurrenceBlocks cs.reverse))) (chainEmbed P σ)).reverse =
      chunks.map (fun c => (c.map φ).prod) := by
    rw [scanWords_eq_actual_chunks P cs R hw σ]
    simp only [chunks,List.map_reverse,List.map_map,Function.comp_def,φ]
  dsimp only
  rw [hg]
  refine ⟨?_,hs.2.2.1,hs.2.1⟩
  exact hs.2.2.2.trans ((P.paletteColoring σ).assignedWords_prod cs hcs)

end Nonadditivity.HaarActualScanWords
