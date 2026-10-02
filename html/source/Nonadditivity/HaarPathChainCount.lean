/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChains
import Nonadditivity.HaarPathInvolution

/-! # Exact incidence budget for core chains -/
noncomputable section
namespace Nonadditivity.HaarPathGraph.Path
open scoped BigOperators
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

instance coreChainDecidableEq : DecidableEq P.CoreChain := Classical.decEq _

theorem card_coreDarts_eq_sum :
    P.coreDarts.card = ∑ v ∈ P.coreVertices, P.degree v := by
  exact (Finset.sum_card_fiberwise_eq_card_filter P.darts P.coreVertices source).symm

/-- The incidences at core vertices account for exactly twice the Euler
core-edge budget. Internal vertices each consume exactly two incidences. -/
theorem card_coreDarts_eq_twice_budget : P.coreDarts.card = 2*P.coreEdgeBudget := by
  have hfilter : (P.vertices.filter fun v => v ∈ P.coreVertices) = P.coreVertices :=
    Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
  have hdeg (v : V) (hv : v ∈ P.vertices.filter (fun v => v ∉ P.coreVertices)) :
      P.degree v=2 := by
    by_contra h
    have hmem := (Finset.mem_filter.mp hv).1
    have hnot := (Finset.mem_filter.mp hv).2
    exact hnot (Finset.mem_filter.mpr ⟨hmem,Or.inr h⟩)
  have hs := Finset.sum_filter_add_sum_filter_not P.vertices
    (fun v => v ∈ P.coreVertices) P.degree
  have hcards := Finset.card_filter_add_card_filter_not (s := P.vertices)
    (fun v => v ∈ P.coreVertices)
  rw [hfilter,←P.card_coreDarts_eq_sum,P.sum_degrees] at hs
  rw [Finset.sum_congr rfl hdeg] at hs
  simp only [Finset.sum_const,smul_eq_mul] at hs
  rw [hfilter] at hcards
  have hv := P.vertices_le_edges
  dsimp [coreEdgeBudget]
  omega

/-- There are at most twice the Euler budget oriented maximal chains. -/
theorem card_coreChain_le_twice_budget : Fintype.card P.CoreChain ≤ 2*P.coreEdgeBudget := by
  simpa only [P.card_coreDarts_eq_twice_budget] using P.card_coreChain_le_coreDarts

/-- Actual core chains with the two orientations identified. -/
def unorientedChains : Finset (Finset P.CoreChain) :=
  HaarPathInvolution.pairs P.coreChainReverse

/-- The number of actual compressed chains has the BC Euler budget. This
uses first-dart reconstruction and the proved free orientation reversal. -/
theorem card_unorientedChains_le_budget : P.unorientedChains.card ≤ P.coreEdgeBudget := by
  have hp := HaarPathInvolution.twice_card_pairs P.coreChainReverse_involutive
    P.coreChainReverse_ne_self
  have hc := P.card_coreChain_le_twice_budget
  change 2*P.unorientedChains.card = _ at hp
  omega

/-- Core-chain count in the exact exponent form of BC Lemma 5.8. -/
theorem twice_card_unorientedChains_le_defect :
    2*P.unorientedChains.card ≤ 3*P.defectTwice+4 := by
  have hb := P.card_unorientedChains_le_budget
  have hd := P.twice_coreEdgeBudget_le
  omega

/-- Assigning realizable bounded-length profiles to the actual unoriented
core chains costs at most the profile factor in BC Lemma 5.8. -/
theorem card_chainProfileAssignments_le (hm : 0 < m) (hd : 0 < d) :
    Fintype.card (P.unorientedChains → HaarPathProfiles.BoundedProfile
      (HaarPathProfiles.Color d) m) ≤
      (2*d*m^d)^(3*P.defectTwice+4) := by
  rw [Fintype.card_fun,Fintype.card_coe]
  have hp := HaarPathProfiles.card_signedProfile_le d m
  calc
    _ ≤ ((2*d*m^d)^2)^P.unorientedChains.card := Nat.pow_le_pow_left hp _
    _ = (2*d*m^d)^(2*P.unorientedChains.card) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) P.twice_card_unorientedChains_le_defect

end Nonadditivity.HaarPathGraph.Path
