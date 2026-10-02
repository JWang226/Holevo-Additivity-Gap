/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalCodingTheorem
import Nonadditivity.DeterministicConsequences
import Nonadditivity.HaarPrescribedConsequences
import Nonadditivity.WeylPowersRegularized

/-! # Operational consequences for the constructed channels

Classical capacity is defined by actual codes with vanishing Born error.
The coding theorem identifies it with the independently defined regularized
Holevo quantity, so the construction's rate conclusions are operational.
-/

noncomputable section

namespace Nonadditivity.ActualConsequences.FiniteQuantumChannel

theorem two_use_gain_le_classical_gain (T : FiniteQuantumChannel) :
    T.chiTwo / 2 - T.chi ≤ T.classicalCapacity - T.chi := by
  exact sub_le_sub_right T.half_chiTwo_le_classicalCapacity _

end Nonadditivity.ActualConsequences.FiniteQuantumChannel

namespace Nonadditivity.OperationalConsequences

open ActualConsequences Filter Topology

/-- The same genuine channel family has vanishing single-use information and
unbounded operational classical capacity. -/
theorem actual_vanishing_chi_diverging_capacity :
    Tendsto (fun K => (DeterministicConsequences.separatingFamily K).chi) atTop (𝓝 0) ∧
    Tendsto (fun K => (DeterministicConsequences.separatingFamily K).classicalCapacity)
      atTop atTop := by
  constructor
  · exact DeterministicConsequences.actual_vanishing_diverging.1
  · simpa only [FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo] using
      DeterministicConsequences.actual_regularizedHolevo_tendsto_atTop

theorem actual_capacity_gain_tendsto_atTop :
    Tendsto (fun K => (DeterministicConsequences.separatingFamily K).classicalCapacity -
      (DeterministicConsequences.separatingFamily K).chi) atTop atTop := by
  simpa only [FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo,
    FiniteQuantumChannel.regularizedGain] using
    DeterministicConsequences.actual_regularizedGain_tendsto_atTop

theorem actual_capacity_ratio_tendsto_atTop :
    Tendsto (fun K => (DeterministicConsequences.separatingFamily K).classicalCapacity /
      (DeterministicConsequences.separatingFamily K).chi) atTop atTop := by
  simpa only [FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo,
    FiniteQuantumChannel.regularizedRatio] using
    DeterministicConsequences.actual_regularizedRatio_tendsto_atTop

/-- Simultaneously small positive one-use information, arbitrarily large
operational gain, and arbitrarily large operational-to-one-use ratio. -/
theorem exists_small_chi_large_capacity_gain_and_ratio {ε : ℝ}
    (hε : 0 < ε) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧
      A ≤ T.classicalCapacity - T.chi ∧ R ≤ T.classicalCapacity / T.chi := by
  simpa only [FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo,
    FiniteQuantumChannel.regularizedGain, FiniteQuantumChannel.regularizedRatio] using
    DeterministicConsequences.exists_small_chi_large_regularized_gain_and_ratio hε A R

/-- The capacity gain and the two-use Holevo ratio can both be arbitrarily
large while the positive single-use information is arbitrarily small. -/
theorem exists_small_chi_large_capacity_gain_and_two_use_ratio {ε : ℝ}
    (hε : 0 < ε) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧
      A ≤ T.classicalCapacity - T.chi ∧ R ≤ T.twoUseRatio := by
  obtain ⟨T, hp, hs, hg, hr⟩ :=
    DeterministicConsequences.exists_small_chi_large_gap_and_ratio hε (2*A) R
  refine ⟨T, hp, hs, ?_, hr⟩
  have hc := T.two_use_gain_le_classical_gain
  unfold FiniteQuantumChannel.gap at hg
  linarith

open HaarPrescribedDimension StructuredHaarConsequences

/-- The prescribed finite dimensions and one-use bound now accompany an
operational capacity gain bound for the very same channel. -/
theorem exists_prescribed_channel_with_capacity_gain {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    ∃ T : FiniteQuantumChannel,
      Fintype.card T.Input = 2 * (localDimension K n)^n * K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧ 2 * (n : ℝ) / (K : ℝ) ≤ T.chi ∧
      T.chi ≤ (n : ℝ) * Scalar.aK K + 2 * Scalar.log2 (kappa n) ∧
      (n : ℝ) * Scalar.deltaK K / 2 - 2 * Scalar.log2 (kappa n) ≤
        T.classicalCapacity - T.chi := by
  let T := prescribedFamily hK n
  have hs := prescribedFamily_spec hK hn
  refine ⟨T, hs.1, hs.2.1, hs.2.2.1,
    prescribedFamily_chi_lower hK hn, hs.2.2.2.1, ?_⟩
  simpa only [T, FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo,
    FiniteQuantumChannel.regularizedGain] using
    prescribedFamily_regularizedGain_lower hK hn

theorem prescribed_capacity_gain_tendsto_atTop {K : ℕ} (hK : 2 ≤ K)
    (hδ : 0 < Scalar.deltaK K) :
    Tendsto (fun n => (prescribedFamily hK n).classicalCapacity -
      (prescribedFamily hK n).chi) atTop atTop := by
  simpa only [FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo,
    FiniteQuantumChannel.regularizedGain] using
    prescribedFamily_regularizedGain_tendsto_atTop_of_delta_pos hK hδ

theorem prescribed_capacity_ratio_eventually {K : ℕ} (hK : 2 ≤ K) {R : ℝ}
    (hR : R < Scalar.log2 K / (2 * (K : ℝ) * Scalar.aK K)) :
    ∀ᶠ n : ℕ in atTop, R ≤ (prescribedFamily hK n).classicalCapacity /
      (prescribedFamily hK n).chi := by
  simpa only [FiniteQuantumChannel.classicalCapacity_eq_regularizedHolevo,
    FiniteQuantumChannel.regularizedRatio] using
    prescribedFamily_regularizedRatio_eventually hK hR

end Nonadditivity.OperationalConsequences

namespace Nonadditivity.WeylPowers

open Channels Channels.KrausChannel

/-- Operational capacity of the actual Weyl extension, with its regularized
minimum entropy taken over every positive number of channel uses. -/
theorem operationalCapacity_weylExtension {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    {d : ℕ} [NeZero d] (T : KrausChannel ι (ZMod d) κ) :
    Operational.operationalCapacity T.weylExtension =
      Scalar.log2 d - sInf (Set.range (normalizedMinimumEntropy T)) := by
  rw [Operational.operationalCapacity_eq_regularizedHolevoSupremum]
  exact regularized_weylExtension_holevo T

end Nonadditivity.WeylPowers
