/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathRuns
import Nonadditivity.HaarPathChainCount

/-! # A concrete obstruction to the uncorrected BC middle-block count

The two-generator reduced word `aaabABAA` is balanced in each generator.
Taking every graph vertex equal produces the nonzero Haar entry monomial
`|U_a(x,x)|^6 |U_b(x,x)|^2`. It has two loop edges, but seven blocks after
isolating first and last visits. The corrected factor count is in HaarPathRuns.
-/
noncomputable section
namespace Nonadditivity.HaarPathRunCounterexample
open HaarPathGraph HaarPathProfiles HaarPathRuns

/-- The literal reduced closed path at one graph vertex. -/
def path : Path Unit 2 8 where
  vertex := fun _ => ()
  colors := ![(0,true),(0,true),(0,true),(1,true),(0,false),(1,false),(0,false),(0,false)]
  closed := rfl
  reduced := by decide

def labels (i : Fin 8) : Fin 2 := (path.colors i).1

/-- All four signed-generator occurrence counts match the balanced Haar pattern. -/
theorem balanced_counts :
    (List.ofFn path.colors).count (0,true)=3 ∧
    (List.ofFn path.colors).count (0,false)=3 ∧
    (List.ofFn path.colors).count (1,true)=1 ∧
    (List.ofFn path.colors).count (1,false)=1 := by decide

theorem marker_flags : endpointFlags labels =
    [true,false,false,true,false,true,false,true] := by decide

theorem core_budget : path.coreEdgeBudget=2 := by decide

/-- The claimed `r≤3*e_hat` fails for an actual reduced two-generator path.
The replacement exponent theorem remains valid for this example. -/
theorem violates_uncorrected_run_bound :
    3*path.unorientedChains.card < blockCount (endpointFlags labels) := by
  have hc := path.card_unorientedChains_le_budget
  rw [core_budget] at hc
  rw [marker_flags]
  have hr := two_edge_run_counterexample.1
  omega

end Nonadditivity.HaarPathRunCounterexample
