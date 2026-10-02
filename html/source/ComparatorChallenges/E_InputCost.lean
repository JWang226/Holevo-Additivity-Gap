/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/
import Nonadditivity.PrescribedCostInformation
import Nonadditivity.PrescribedCostLogarithms

/-! Expected statements only. The concrete scale is repeated with its exact
value; it is not a definition hole. Neither target proof is imported here. -/
noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology Asymptotics ActualConsequences

def inputLogScale : ℝ := Real.sqrt (2/Real.log 2)

theorem growingFamily_chi_input_cost_bounds :
    ∀ᶠ K : ℕ in atTop,
      inputLogScale/2 ≤ (growingFamily K).chi * Real.sqrt (Scalar.log2 (inputQubits K)) ∧
      (growingFamily K).chi * Real.sqrt (Scalar.log2 (inputQubits K)) ≤
        (9/Real.log 2+1) * (2*inputLogScale) := by
  sorry

theorem growingFamily_two_use_input_cost_lower :
    ∀ᶠ K : ℕ in atTop,
      1/(8*Real.log 2*inputLogScale) ≤
        ((growingFamily K).chiTwo/2)/Real.sqrt (Scalar.log2 (inputQubits K)) ∧
      1/(8*Real.log 2*inputLogScale) ≤
        (growingFamily K).classicalCapacity/Real.sqrt (Scalar.log2 (inputQubits K)) := by
  sorry

end Nonadditivity.PrescribedCost
