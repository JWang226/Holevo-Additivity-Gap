/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathProfiles
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Literal edge-multiplicity identities for the Haar path expansion

The list may be the colored edges of an original path or the successive
compressed-edge visits. All cardinal and excess-occurrence estimates are
proved for its actual multiplicities, rather than supplied as hypotheses.
-/
noncomputable section
namespace Nonadditivity.HaarPathMultiplicity
open scoped BigOperators
variable {E : Type*} [DecidableEq E]

/-- Edges that occur exactly once in the given path. -/
def singletonEdges (l : List E) : Finset E := l.toFinset.filter (fun e => l.count e = 1)

/-- Occurrences beyond the first two visits of each edge. -/
def excessOccurrences (l : List E) : ℕ := ∑ e ∈ l.toFinset, (l.count e - 2)

theorem sum_multiplicities (l : List E) :
    ∑ e ∈ l.toFinset, l.count e = l.length := List.sum_toFinset_count_eq_length l

/-- BC equation (30), stated without truncated subtraction on either side. -/
theorem excess_add_twice_edges (l : List E) :
    excessOccurrences l + 2*l.toFinset.card = l.length + (singletonEdges l).card := by
  have hpoint (e : E) (he : e ∈ l.toFinset) :
      (l.count e - 2) + 2 = l.count e + (if l.count e = 1 then 1 else 0) := by
    have hp : 0 < l.count e := List.count_pos_iff.mpr (List.mem_toFinset.mp he)
    split_ifs <;> omega
  have hs := Finset.sum_congr rfl hpoint
  simpa [excessOccurrences, singletonEdges, Finset.sum_add_distrib,
    Finset.sum_ite, sum_multiplicities, mul_comm] using hs

/-- The number of distinct edges is at most `(length + singletons)/2`. -/
theorem twice_edges_le_length_add_singletons (l : List E) :
    2*l.toFinset.card ≤ l.length + (singletonEdges l).card := by
  have h := excess_add_twice_edges l
  omega

/-- Total visits to edges of multiplicity at least four. -/
def highMultiplicityOccurrences (l : List E) : ℕ :=
  ∑ e ∈ l.toFinset, if 4 ≤ l.count e then l.count e else 0

/-- The fourth-and-higher multiplicity cost is controlled by twice the exact
excess. This is the counting step in the BC probabilistic weight estimate. -/
theorem highMultiplicityOccurrences_le_twice_excess (l : List E) :
    highMultiplicityOccurrences l ≤ 2*excessOccurrences l := by
  rw [highMultiplicityOccurrences, excessOccurrences, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  split_ifs <;> omega

/-- First/last visits contribute at most two per distinct compressed edge;
all other visits are precisely the excess counted above. -/
theorem length_le_twice_edges_add_excess (l : List E) :
    l.length ≤ 2*l.toFinset.card + excessOccurrences l := by
  have h := excess_add_twice_edges l
  omega

/-- A second, useful form of BC equation (30). -/
theorem excessOccurrences_eq (l : List E) :
    excessOccurrences l = l.length + (singletonEdges l).card - 2*l.toFinset.card := by
  have h := excess_add_twice_edges l
  omega

/-- Summing a statistic over distinct edges equals its occurrence sum when
weighted by the actual edge multiplicity. -/
theorem sum_occurrence_weights {M : Type*} [AddCommMonoid M]
    (l : List E) (f : E → M) :
    (l.map f).sum = ∑ e ∈ l.toFinset, l.count e • f e := by
  exact Finset.sum_list_map_count l f

end Nonadditivity.HaarPathMultiplicity
