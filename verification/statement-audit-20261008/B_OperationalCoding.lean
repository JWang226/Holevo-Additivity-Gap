import Nonadditivity.OperationalCodingTheorem
/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

/-! Expected statement only; the intentional `sorry` is a Comparator
placeholder, not an assumption or unfinished proof in the solution library. -/
noncomputable section
namespace Nonadditivity.Operational
open Channels RegularizedHolevo

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

theorem checked_operationalCapacity_eq_regularizedHolevoSupremum (T : KrausChannel ι ο κ) :
    operationalCapacity T = sSup (Set.range (normalizedPowerHolevo T)) := by
  exact Nonadditivity.Operational.operationalCapacity_eq_regularizedHolevoSupremum T

end Nonadditivity.Operational
