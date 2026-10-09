import Nonadditivity.DeterministicConsequences
/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

/-! Expected statement only: arbitrarily small positive one-use information and
arbitrarily large two-use information. This challenge does not import its solution module. -/
noncomputable section
namespace Nonadditivity.DeterministicConsequences
open ActualConsequences

theorem checked_actual_small_large {ε R : ℝ} (hε : 0<ε) :
    ∃ T : FiniteQuantumChannel, 0<T.chi ∧ T.chi≤ε ∧ R≤T.chiTwo/2 := by
  exact Nonadditivity.DeterministicConsequences.actual_small_large hε

end Nonadditivity.DeterministicConsequences
