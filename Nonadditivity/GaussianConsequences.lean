/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianConstruction
import Nonadditivity.GaussianChannelBounds
import Nonadditivity.GaussianScalar
import Nonadditivity.HolevoRateLimit

/-! # Unconditional multiplicative nonadditivity

The actual normalized Gaussian construction supplies every analytic input.
The channels have positive single-use Holevo information, which can be made
arbitrarily small while their two-use ratios become arbitrarily large.
This does not assert unbounded additive gaps.
-/

noncomputable section

namespace Nonadditivity.GaussianConsequences

open ActualConsequences

/-- Explicit dimensions and information bounds for genuine finite channels.
There are no random-matrix or channel-existence hypotheses. -/
theorem exists_channel_bounds {K : ℕ} (hK : 4096 ≤ K)
    (hlog : 0 ≤ Real.log (K : ℝ) - 1) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ 512^2 / ((K : ℝ) * Real.log 2) ∧
      (Real.log (K : ℝ) - 1) / (2 * 512^2) ≤ T.twoUseRatio ∧
      Fintype.card T.Input = 2 * K^4 ∧ Fintype.card T.Output = K := by
  letI : NeZero K := ⟨by omega⟩
  letI : NeZero (K^2) := ⟨pow_ne_zero _ (NeZero.ne K)⟩
  obtain ⟨T, hT⟩ := GaussianConstruction.exists_channel K (K^2) hK le_rfl
  obtain ⟨hp, hu, hr, hi, ho⟩ :=
    GaussianChannelBounds.converted_bounds (by omega : 2 ≤ K) hlog T hT
  refine ⟨FiniteQuantumChannel.ofKraus (Conversion.converted T), hp, hu, hr, ?_, ho⟩
  rw [hi]
  ring

/-- Unconditional small positive Holevo information and arbitrarily large
two-use multiplicative violation, simultaneously. -/
theorem exists_small_chi_large_ratio {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧ R ≤ T.twoUseRatio := by
  obtain ⟨K, hK, hsmall, hlarge, hlog⟩ := GaussianScalar.exists_parameter hε R
  obtain ⟨T, hp, hu, hr, _, _⟩ := exists_channel_bounds hK hlog
  exact ⟨T, hp, hu.trans hsmall, hlarge.trans hr⟩

theorem exists_arbitrarily_large_ratio (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ R ≤ T.twoUseRatio := by
  obtain ⟨T, hp, _, hr⟩ := exists_small_chi_large_ratio (by norm_num : (0 : ℝ) < 1) R
  exact ⟨T, hp, hr⟩

theorem exists_nonadditive_channel :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ 0 < T.gap := by
  obtain ⟨T, hp, hr⟩ := exists_arbitrarily_large_ratio 2
  refine ⟨T, hp, ?_⟩
  have h := (le_div_iff₀ (by positivity : 0 < 2 * T.chi)).mp hr
  unfold FiniteQuantumChannel.gap
  linarith

/-- The established Holevo rate limit has an unbounded multiplicative
advantage too. No operational coding theorem is used. -/
theorem exists_small_chi_large_regularized_ratio {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧ R ≤ T.regularizedRatio := by
  obtain ⟨T, hp, hu, hr⟩ := exists_small_chi_large_ratio hε R
  exact ⟨T, hp, hu, hr.trans (T.two_use_ratio_le_regularizedRatio hp)⟩

end Nonadditivity.GaussianConsequences
