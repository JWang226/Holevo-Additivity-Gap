/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarRefinedCoefficientFibre
import Nonadditivity.HaarProfileSingletonWeight
import Nonadditivity.HaarActualScanWords
import Nonadditivity.HaarDecodedCoefficientBound

/-! # The actual refined-class coefficient bound

The bound is proved for the literal finite refined class. All profile variables,
operator factors, duration compositions, and graph counts are instantiated from
the actual path; no factorization, fibre, or local norm hypothesis is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Nonadditivity.HaarOperatorPathBridge
open scoped BigOperators
open HaarPathGraph HaarPathClasses HaarPathProfiles HaarProfileCoefficient
  HaarOperatorPolynomial NoncommutativeCS HaarPaletteDecoder HaarSkeletonSegmentation
  HaarProfileAssignmentBound HaarProfilePadding
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The prescribed BC coefficient budget for the actual refined path class. -/
theorem coefficient_bound
    (A : Polynomial (FreeGroup (Fin 2)) E)
    (hA : ∀ g ∈ A.support, g.toWord.length ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (P : Path V 2 m) (hm : 0 < m) :
    ‖refinedCoefficientSum A p P‖ ≤
      (Fintype.card V : ℝ)^P.vertices.card *
        (2:ℝ)^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
        (p:ℝ)^(9*P.defectTwice+11) * ‖regular A‖^p := by
  classical
  obtain ⟨cs,hcs⟩ := P.exists_traversal_chain_decomposition hm
  have hcover : ∀ e : P.unorientedChains, e ∈ (cs.map P.chainLabel).reverse := by
    intro e
    obtain ⟨c,hc,he⟩ := P.chainLabels_cover cs hcs e
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨c,hc,he⟩)
  obtain ⟨R,hw,hR,hn,hc,hexp⟩ := EndpointSkeleton.exists_closed_compiler
    (cs.map P.chainLabel).reverse hcover
  have hcsne : cs≠[] := by
    intro he
    have hh := congrArg List.length hcs
    simp only [he,List.map_nil,List.flatten_nil,List.length_nil,
      Path.traversalList,List.length_ofFn] at hh
    omega
  have hword : R.word≠[] := by
    rw [hw]
    intro he
    have hl := congrArg List.length he
    simp only [List.length_reverse,List.length_map,List.length_nil] at hl
    exact hcsne (List.length_eq_zero_iff.mp hl)
  have hblocks : 1 ≤ R.markedFlags.length := by
    by_contra h
    have he : R.blocks=[] := List.length_eq_zero_iff.mp (by rw [R.length_blocks]; omega)
    exact hword (by rw [←R.flatten_blocks,he]; rfl)
  let size : P.unorientedChains → ℕ := fun e => (P.representative e).val.length
  let profile : P.unorientedChains → Profile (Color 2) :=
    fun e => (P.coreChainProfile (P.representative e)).val
  let hsize : ∀ e, size e≤m := fun e => P.coreChain_length_le (P.representative e)
  let directions := blockDirections P (R.occurrenceBlocks cs.reverse)
  let target : P.ChainPalette → FreeGroup (Fin 2) :=
    fun σ => FreeGroup.mk (List.ofFn (P.paletteColoring σ).path.colors)
  have hdecode : ∀ (σ : P.ChainPalette) k i,
      decode directions k [i] [embedAssignment size profile hsize σ i]=
        orientedWord (forward directions k i) (σ i) :=
    fun σ k i => decode_embedAssignment directions size profile hsize σ k i
  have htarget : ∀ σ : P.ChainPalette,
      (scanWords R (decode directions) (embedAssignment size profile hsize σ)).reverse.prod=target σ := by
    intro σ
    exact (HaarActualScanWords.actualScanWords_spec P cs R hcs hR hw σ).1
  have hne : ∀ (σ : P.ChainPalette) g,
      g∈(scanWords R (decode directions) (embedAssignment size profile hsize σ)).reverse → g≠1 := by
    intro σ
    exact (HaarActualScanWords.actualScanWords_spec P cs R hcs hR hw σ).2.1
  have hred : ∀ σ : P.ChainPalette,
      FreeGroup.IsReduced
        ((scanWords R (decode directions) (embedAssignment size profile hsize σ)).reverse.flatMap FreeGroup.toWord) := by
    intro σ
    exact (HaarActualScanWords.actualScanWords_spec P cs R hcs hR hw σ).2.2
  have hpal := HaarDecodedCoefficientBound.decoded_coefficient_sum_norm_le R hR hn hc hblocks
    A hA size profile hsize (forward directions) (decode directions) hdecode p hp target htarget hne hred
  rw [R.singletonWeight_chain_labels_reverse P cs hcs hn hw] at hpal
  have hpow : (p:ℝ)^(6*Fintype.card P.unorientedChains-1) ≤ (p:ℝ)^(9*P.defectTwice+11) :=
    pow_le_pow_right₀ (by exact_mod_cast hp) (EndpointSkeleton.coefficient_exponent_chain_le P)
  calc
    _ ≤ (Fintype.card V : ℝ)^P.vertices.card *
        ‖∑ σ : P.ChainPalette, (A^p) (target σ)‖ :=
      norm_refinedCoefficientSum_le_palette A p P hm
    _ ≤ (Fintype.card V : ℝ)^P.vertices.card *
        ((2:ℝ)^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(6*Fintype.card P.unorientedChains-1) * ‖regular A‖^p) :=
      mul_le_mul_of_nonneg_left hpal (by positivity)
    _ ≤ (Fintype.card V : ℝ)^P.vertices.card *
        ((2:ℝ)^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11) * ‖regular A‖^p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

end Nonadditivity.HaarOperatorPathBridge
