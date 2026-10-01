/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.CollinsYounProduct
import Nonadditivity.HolevoRateLimit

/-! # Channel separation with only canonical Haar convergence remaining

The full Collins--Youn estimate is supplied by an internal theorem. The
sole remaining analytic input is convergence for the fixed independent
normalized Haar sampling model, at each fixed generator and block count.
-/

namespace Nonadditivity.HaarConsequences

open ActualConsequences Channels.KrausChannel BlockConstruction Filter
open scoped Topology

def AllHaarStrongConvergence : Prop :=
  ∀ (K : ℕ) [NeZero K] (n : ℕ), 2 ≤ K → 1 ≤ n →
    HaarModel.HaarStrongConvergence K n

theorem analyticInputs (hBC : AllHaarStrongConvergence) : AnalyticInputs :=
  ⟨fun _ _ hK hn => CollinsYounProduct.collinsYounBound hK hn, hBC⟩

/-- The fixed-block information estimates need only that block's canonical
Haar convergence. All free-operator and quantum-information estimates are proved. -/
theorem exists_block_channel {K n : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η)
    (hBC : HaarModel.HaarStrongConvergence K n) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      T.chi ≤ (n : ℝ) * Scalar.aK K + η ∧
      (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo ∧
      (n : ℝ) * Scalar.deltaK K - 2 * η ≤ T.gap := by
  obtain ⟨N, ω, h₁, h₂, _⟩ :=
    HaarModel.qualitative_realization_of_CY_and_Haar_strong_convergence
      n hK hn (mul_pos hη Scalar.log_two_pos)
      (CollinsYounProduct.collinsYounBound hK hn) hBC
  let U := HaarModel.sampleUnitary K n N ω
  let T := FiniteQuantumChannel.ofKraus (Conversion.converted (blockChannel U n))
  have hp : 0 < T.chi := PositiveHolevo.block_converted_holevoBits_pos hK U hn
  have hu : T.chi ≤ (n : ℝ) * Scalar.aK K + η :=
    HolevoBits.natural_upper_to_bits n h₁
  have hl : (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo :=
    HolevoBits.natural_lower_to_bits n h₂
  refine ⟨T, hp, hu, hl, ?_⟩
  unfold FiniteQuantumChannel.gap Scalar.deltaK
  rw [mul_sub, ← mul_div_assoc]
  nlinarith only [hu, hl]

theorem exists_large_gap_and_ratio (hBC : AllHaarStrongConvergence) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ A ≤ T.gap ∧ R ≤ T.twoUseRatio :=
  actual_large_gap_and_ratio (analyticInputs hBC) A R

theorem exists_small_chi_large_regularized_gain (hBC : AllHaarStrongConvergence)
    {ε R : ℝ} (hε : 0 < ε) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧ R ≤ T.regularizedGain :=
  actual_small_large_regularizedGain (analyticInputs hBC) hε

theorem exists_large_regularized_gain_and_ratio
    (hBC : AllHaarStrongConvergence) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      A ≤ T.regularizedGain ∧ R ≤ T.regularizedRatio :=
  actual_large_regularizedGain_and_ratio (analyticInputs hBC) A R

/-- A sequence of actual finite channels realizes all four separations. -/
theorem exists_separating_family (hBC : AllHaarStrongConvergence) :
    ∃ T : ℕ → FiniteQuantumChannel,
      Tendsto (fun K => (T K).chi) atTop (𝓝 0) ∧
      Tendsto (fun K => (T K).chiTwo / 2) atTop atTop ∧
      Tendsto (fun K => (T K).gap) atTop atTop ∧
      Tendsto (fun K => (T K).twoUseRatio) atTop atTop := by
  let inputs := analyticInputs hBC
  exact ⟨separatingFamily inputs, (actual_vanishing_diverging inputs).1,
    (actual_vanishing_diverging inputs).2, actual_gap_tendsto_atTop inputs,
    actual_ratio_tendsto_atTop inputs⟩

end Nonadditivity.HaarConsequences
