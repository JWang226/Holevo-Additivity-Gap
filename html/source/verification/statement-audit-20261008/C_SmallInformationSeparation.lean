import Nonadditivity.OperationalConsequences
/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

/-! Expected statement only; `classicalCapacity` is the independently defined
capacity of actual codes. This challenge does not import its solution module. -/
noncomputable section
namespace Nonadditivity.OperationalConsequences
open ActualConsequences

theorem checked_exists_small_chi_large_capacity_gain_and_two_use_ratio {ε : ℝ}
    (hε : 0 < ε) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧
      A ≤ T.classicalCapacity - T.chi ∧ R ≤ T.twoUseRatio := by
  exact Nonadditivity.OperationalConsequences.exists_small_chi_large_capacity_gain_and_two_use_ratio hε A R

end Nonadditivity.OperationalConsequences
