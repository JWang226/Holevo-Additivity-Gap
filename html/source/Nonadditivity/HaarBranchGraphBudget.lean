/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarBranchTimeSum
import Nonadditivity.HaarPathChainCount

/-! # The graph defect exponent for actual branch contractions

This connects the constructed duration sums to the proved compressed-chain
count. The structural interface still requires identifying a refined path
class with such a schedule; no such identification is claimed here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarNonbacktracking.BranchPlan
open scoped BigOperators
open NoncommutativeCS

variable {G E J V : Type*} [Group G] [DecidableEq G]
variable [Fintype J] [DecidableEq J] [DecidableEq V]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The manuscript's `18*chi+11` exponent, written using the integer
`defectTwice = 2*chi`, follows from the literal first/last markers and the
actual number of compressed chains. -/
theorem timeSum_norm_le_graph_budget {A : H G E →L[ℂ] H G E} (hA : IsStationary A)
    {d q k m n : ℕ} (graph : HaarPathGraph.Path V d q)
    (f : Fin (k+1) → graph.unorientedChains)
    (P : BranchPlan G J m n) (hP : 0 < P.blocks)
    (hblocks : P.blocks = HaarPathRuns.blockCount (HaarPathRuns.endpointFlags f))
    (hmarked : P.marked = (HaarPathRuns.endpointFlags f).count true)
    (s : Fin n → J) (t : Fin m → J) (L : ℕ) (hL : 1 ≤ L) :
    ‖timeSum A P s t L‖ ≤ (L:ℝ)^(9*graph.defectTwice+11) * ‖A‖^L *
      (Real.sqrt (Fintype.card J:ℝ))^P.singletons := by
  classical
  have he := HaarPathRuns.occurrence_exponent_le f
  have hc : (Finset.univ.image f).card ≤ graph.unorientedChains.card := by
    simpa only [Fintype.card_coe] using (Finset.card_le_univ (Finset.univ.image f))
  have hg := graph.twice_card_unorientedChains_le_defect
  have hexp : P.blocks-1+P.marked ≤ 9*graph.defectTwice+11 := by
    rw [hblocks,hmarked]
    omega
  have hp : (L:ℝ)^(P.blocks-1+P.marked) ≤ (L:ℝ)^(9*graph.defectTwice+11) :=
    pow_le_pow_right₀ (by exact_mod_cast hL) hexp
  apply (timeSum_norm_le hA P hP s t L).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)

end Nonadditivity.HaarNonbacktracking.BranchPlan
