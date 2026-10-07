/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingHSW
import Nonadditivity.OperationalBlocking
import Nonadditivity.OperationalWeakConverse

/-! # The operational classical coding theorem

Operational capacity is defined independently through actual codewords,
normalized POVM decoders, and vanishing Born error. HSW achievability plus
physical blocking gives the lower bound by every normalized tensor-power
Holevo information. The converse applies to every actual code sequence.
Their combination identifies operational capacity with the regularized
Holevo supremum and its genuine tensor-power limit.
-/

noncomputable section

namespace Nonadditivity.Operational

open Channels RegularizedHolevo

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- HSW codes on a block, physically flattened and padded, attain each
normalized tensor-power Holevo information as a capacity lower bound. -/
theorem normalizedPowerHolevo_le_operationalCapacity (T : KrausChannel ι ο κ)
    (n : ℕ) : normalizedPowerHolevo T n ≤ operationalCapacity T := by
  have hh := QuantumCoding.holevoBits_le_operationalCapacity (positiveTensorPower T n)
  have hb := operationalCapacity_block_le T n
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hn).mpr
  exact (hh.trans hb).trans_eq (mul_comm _ _)

/-- All positive tensor block lengths are included in this operational
lower bound; no unproved coding statement is a premise. -/
theorem regularizedHolevoSupremum_le_operationalCapacity (T : KrausChannel ι ο κ) :
    sSup (Set.range (normalizedPowerHolevo T)) ≤ operationalCapacity T := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact normalizedPowerHolevo_le_operationalCapacity T n

/-- The classical coding theorem for arbitrary finite Kraus channels.
Both sides have their independent, concrete definitions. -/
theorem operationalCapacity_eq_regularizedHolevoSupremum (T : KrausChannel ι ο κ) :
    operationalCapacity T = sSup (Set.range (normalizedPowerHolevo T)) :=
  le_antisymm (operationalCapacity_le_regularizedHolevoSupremum T)
    (regularizedHolevoSupremum_le_operationalCapacity T)

end Nonadditivity.Operational

namespace Nonadditivity.ActualConsequences.FiniteQuantumChannel

open RegularizedHolevo Filter Topology

/-- Operational classical capacity in bits, defined through physical codes. -/
def classicalCapacity (T : FiniteQuantumChannel) : ℝ :=
  Operational.operationalCapacity T.channel

/-- The independently defined operational capacity equals the previously
formalized regularized Holevo quantity. -/
theorem classicalCapacity_eq_regularizedHolevo (T : FiniteQuantumChannel) :
    T.classicalCapacity = T.regularizedHolevo :=
  Operational.operationalCapacity_eq_regularizedHolevoSupremum T.channel

theorem classicalCapacity_nonneg (T : FiniteQuantumChannel) : 0 ≤ T.classicalCapacity :=
  Operational.operationalCapacity_nonneg T.channel

theorem chi_le_classicalCapacity (T : FiniteQuantumChannel) : T.chi ≤ T.classicalCapacity :=
  QuantumCoding.holevoBits_le_operationalCapacity T.channel

theorem half_chiTwo_le_classicalCapacity (T : FiniteQuantumChannel) :
    T.chiTwo / 2 ≤ T.classicalCapacity := by
  rw [classicalCapacity_eq_regularizedHolevo]
  exact T.half_chiTwo_le_regularizedHolevo

/-- The normalized actual tensor-power Holevo informations converge to
the operational classical capacity. -/
theorem normalizedPowerHolevo_tendsto_classicalCapacity (T : FiniteQuantumChannel) :
    Tendsto (normalizedPowerHolevo T.channel) atTop (𝓝 T.classicalCapacity) := by
  rw [classicalCapacity_eq_regularizedHolevo]
  exact T.normalizedPowerHolevo_tendsto

end Nonadditivity.ActualConsequences.FiniteQuantumChannel
