/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HolevoRateLimit

/-! # Regrouping a fixed channel cannot give a linear Holevo gap -/

noncomputable section
namespace Nonadditivity.RegularizedHolevo
open Channels Channels.KrausChannel ActualConsequences Filter Topology

theorem tensor_power_self_holevoBits {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) (n : ℕ) :
    ((positiveTensorPower T n).tensor (positiveTensorPower T n)).holevoBits =
      (positiveTensorPower T (n+n+1)).holevoBits := by
  rw [← positiveTensorPower_split]
  rw [holevoBits_eq_of_map_eq _ _ (fun X => reindexKraus_map _ _ X), holevoBits_reindex]

/-- The normalized two-use nonadditivity gap of increasingly large blocks
of one fixed channel tends to zero. The tensors and information quantities
are those of the actual Kraus maps. -/
theorem normalized_fixed_channel_gap_tendsto_zero (T : FiniteQuantumChannel) :
    Tendsto (fun n =>
      (((positiveTensorPower T.channel n).tensor (positiveTensorPower T.channel n)).holevoBits -
        2 * (positiveTensorPower T.channel n).holevoBits) / ((n+1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hindex : Tendsto (fun n : ℕ => n+n+1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h := ((T.normalizedPowerHolevo_tendsto.comp hindex).sub
    T.normalizedPowerHolevo_tendsto).const_mul 2
  simp only [sub_self, mul_zero] at h
  apply h.congr
  intro n
  rw [tensor_power_self_holevoBits]
  unfold normalizedPowerHolevo
  simp only [Function.comp_apply]
  have hn : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hdouble : (((n+n+1+1 : ℕ) : ℝ)) = 2 * ((n+1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hdouble]
  field_simp

end Nonadditivity.RegularizedHolevo
