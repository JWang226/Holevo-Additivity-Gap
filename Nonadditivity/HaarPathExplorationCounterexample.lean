/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathExploration

/-! # The terminal-tree-edge correction is necessary

A literal reduced, closed and generator-balanced two-generator path refutes
BC Lemma 5.3's intermediate bound on important times. It does not refute the
lemma's final class count. HaarPathExploration proves the corrected bound.
-/
noncomputable section
namespace Nonadditivity.HaarPathExplorationCounterexample
open HaarPathGraph HaarPathProfiles

/-- Go along an `a` edge, traverse the `b,a,B,A` commutator of two loops,
and return along the original edge. The word is `abaBAA`. -/
def path : Path (Fin 2) 2 6 where
  vertex := ![0,1,1,1,1,1,0]
  colors := ![(0,true),(1,true),(0,true),(1,false),(0,false),(0,false)]
  closed := rfl
  reduced := by decide

theorem balanced_counts :
    (List.ofFn path.colors).count (0,true)=2 ∧
    (List.ofFn path.colors).count (0,false)=2 ∧
    (List.ofFn path.colors).count (1,true)=1 ∧
    (List.ofFn path.colors).count (1,false)=1 := by decide

theorem first_times : path.firstTimes={0} := by decide

theorem important_times : path.importantTimes={1,2,3,4} := by decide

theorem defect_twice : path.defectTwice=2 := by decide

/-- Excluding the final traversal does not remove an important time in this
example: that traversal belongs to the discovery tree. -/
theorem violates_uncorrected_important_bound :
    path.defectTwice+1 <
      (path.importantTimes.filter fun i => i.val+1<6).card := by decide

theorem attains_corrected_important_bound :
    path.importantTimes.card=path.defectTwice+2 := by decide

end Nonadditivity.HaarPathExplorationCounterexample
