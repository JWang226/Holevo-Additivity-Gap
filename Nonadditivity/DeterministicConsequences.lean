/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DeterministicQualitative
import Nonadditivity.HolevoRateLimit

/-! Unconditional vanishing single-use information and unbounded additive
nonadditivity for actual finite channels. The fixed-moment finite-group model and
spectral damping supply all analytic inputs. An arbitrarily small slack in the
finite two-use bound suffices for these qualitative limits. -/
noncomputable section
namespace Nonadditivity.DeterministicConsequences
open Filter Topology ActualConsequences
open Channels Channels.KrausChannel

/-- Actual finite channels with the integer `sqrt(log)` block length. -/
theorem exists_actual_separating_channel_positive {K : ℕ} (hK : 2 ≤ K) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K - 1 ≤ T.chiTwo / 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hn : 1 ≤ Asymptotics.blockLength K := Asymptotics.blockLength_pos hK
  obtain ⟨T,hpos,h₁,h₂⟩ := DeterministicQualitative.exists_actual_channel_bounds_positive hK hn
    (show 0 < 1/(K : ℝ) by positivity)
  refine ⟨T,hpos,?_,?_⟩
  · calc
      T.chi ≤ (Asymptotics.blockLength K : ℝ)*Scalar.aK K + 1/(K : ℝ) := h₁
      _ ≤ (Asymptotics.blockLength K : ℝ)*(9/((K : ℝ)*Real.log 2)) + 1/(K : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left (Scalar.aK_le hKpos)
          (Nat.cast_nonneg (Asymptotics.blockLength K) : (0 : ℝ) ≤ Asymptotics.blockLength K)
        linarith
      _ = Asymptotics.separationUpper K := by unfold Asymptotics.separationUpper; ring
  · have hraw : 2*Asymptotics.separationLower K - 1/(K : ℝ) ≤ T.chiTwo := by
      convert h₂ using 1
      unfold Asymptotics.separationLower Scalar.log2
      ring
    have hKtwo : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hi : 1/(K : ℝ) ≤ 2 := (div_le_iff₀ hKpos).mpr (by linarith)
    linarith

/-- A sequence of genuine finite Kraus CPTP maps, selected from the proved construction. -/
def separatingFamily (K : ℕ) : FiniteQuantumChannel :=
  if hK : 2 ≤ K then Classical.choose (exists_actual_separating_channel_positive hK)
  else FiniteQuantumChannel.ofKraus (KrausChannel.identity : KrausChannel (Fin 1) (Fin 1) Unit)

theorem separatingFamily_bounds {K : ℕ} (hK : 2 ≤ K) :
    (separatingFamily K).chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K - 1 ≤ (separatingFamily K).chiTwo / 2 := by
  simp only [separatingFamily,dif_pos hK]
  exact (Classical.choose_spec (exists_actual_separating_channel_positive hK)).2

theorem separatingFamily_pos {K : ℕ} (hK : 2 ≤ K) : 0 < (separatingFamily K).chi := by
  simp only [separatingFamily,dif_pos hK]
  exact (Classical.choose_spec (exists_actual_separating_channel_positive hK)).1

/-- No random-matrix or channel-existence assumption remains in this separation. -/
theorem actual_vanishing_diverging :
    Tendsto (fun K => (separatingFamily K).chi) atTop (𝓝 0) ∧
      Tendsto (fun K => (separatingFamily K).chiTwo/2) atTop atTop := by
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun K => (separatingFamily K).chi_nonneg))
    · filter_upwards [eventually_ge_atTop 2] with K hK
      exact (separatingFamily_bounds hK).1
    · exact Asymptotics.separationUpper_tendsto_zero
  · have hl : Tendsto (fun K => Asymptotics.separationLower K - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        Asymptotics.separationLower_tendsto_atTop.atTop_add
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)))
    refine tendsto_atTop_mono' atTop ?_ hl
    filter_upwards [eventually_ge_atTop 2] with K hK
    exact (separatingFamily_bounds hK).2

theorem actual_gap_tendsto_atTop :
    Tendsto (fun K => (separatingFamily K).gap) atTop atTop := by
  obtain ⟨h₁,h₂⟩ := actual_vanishing_diverging
  have hp := h₂.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hn := h₁.const_mul (-2)
  have hh := hp.atTop_add hn
  convert hh using 1
  ext K
  unfold FiniteQuantumChannel.gap
  ring

theorem actual_two_use_gain_tendsto_atTop :
    Tendsto (fun K => (separatingFamily K).chiTwo/2-(separatingFamily K).chi) atTop atTop := by
  have h := actual_gap_tendsto_atTop.atTop_div_const (by norm_num : (0 : ℝ)<2)
  convert h using 1
  ext K
  unfold FiniteQuantumChannel.gap
  ring

theorem actual_ratio_tendsto_atTop :
    Tendsto (fun K => (separatingFamily K).twoUseRatio) atTop atTop := by
  obtain ⟨hχ,htwo⟩ := actual_vanishing_diverging
  have hsmall : ∀ᶠ K in atTop, (separatingFamily K).chi < 1 :=
    hχ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  have hbound : ∀ᶠ K in atTop,
      (separatingFamily K).chiTwo/2 ≤ (separatingFamily K).twoUseRatio := by
    filter_upwards [hsmall,eventually_ge_atTop 2] with K hs hK
    have hp := separatingFamily_pos hK
    have hn := (separatingFamily K).chiTwo_nonneg
    have hm := mul_le_mul_of_nonneg_left hs.le hn
    unfold FiniteQuantumChannel.twoUseRatio
    apply (le_div_iff₀ (by positivity : 0<2*(separatingFamily K).chi)).2
    nlinarith
  exact tendsto_atTop_mono' atTop hbound htwo

/-- Simultaneously small positive information, arbitrarily large additive gap,
and arbitrarily large genuine two-use ratio. -/
theorem exists_small_chi_large_gap_and_ratio {ε : ℝ} (hε : 0<ε) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel,
      0<T.chi ∧ T.chi≤ε ∧ A≤T.gap ∧ R≤T.twoUseRatio := by
  have hs : ∀ᶠ K in atTop, (separatingFamily K).chi<ε :=
    actual_vanishing_diverging.1.eventually (gt_mem_nhds hε)
  have hg : ∀ᶠ K in atTop, A≤(separatingFamily K).gap :=
    actual_gap_tendsto_atTop.eventually (eventually_ge_atTop A)
  have hr : ∀ᶠ K in atTop, R≤(separatingFamily K).twoUseRatio :=
    actual_ratio_tendsto_atTop.eventually (eventually_ge_atTop R)
  obtain ⟨K,hK,hs,hg,hr⟩ := ((eventually_ge_atTop 2).and (hs.and (hg.and hr))).exists
  exact ⟨separatingFamily K,separatingFamily_pos hK,hs.le,hg,hr⟩

theorem actual_unbounded_gap (A : ℝ) :
    ∃ T : FiniteQuantumChannel, 0<T.chi ∧ A≤T.gap := by
  obtain ⟨T,hp,_,hg,_⟩ := exists_small_chi_large_gap_and_ratio
    (by norm_num : (0 : ℝ)<1) A 0
  exact ⟨T,hp,hg⟩

theorem actual_small_large {ε R : ℝ} (hε : 0<ε) :
    ∃ T : FiniteQuantumChannel, 0<T.chi ∧ T.chi≤ε ∧ R≤T.chiTwo/2 := by
  have hs : ∀ᶠ K in atTop, (separatingFamily K).chi<ε :=
    actual_vanishing_diverging.1.eventually (gt_mem_nhds hε)
  have hl : ∀ᶠ K in atTop, R≤(separatingFamily K).chiTwo/2 :=
    actual_vanishing_diverging.2.eventually (eventually_ge_atTop R)
  obtain ⟨K,hK,hs,hl⟩ := ((eventually_ge_atTop 2).and (hs.and hl)).exists
  exact ⟨separatingFamily K,separatingFamily_pos hK,hs.le,hl⟩

/-- The regularized quantity is already proved to equal the tensor-power Holevo rate limit. -/
theorem actual_regularizedHolevo_tendsto_atTop :
    Tendsto (fun K => (separatingFamily K).regularizedHolevo) atTop atTop :=
  tendsto_atTop_mono (fun K => (separatingFamily K).half_chiTwo_le_regularizedHolevo)
    actual_vanishing_diverging.2

theorem actual_regularizedGain_tendsto_atTop :
    Tendsto (fun K => (separatingFamily K).regularizedGain) atTop atTop :=
  tendsto_atTop_mono (fun K => (separatingFamily K).two_use_gain_le_regularizedGain)
    actual_two_use_gain_tendsto_atTop

theorem actual_regularizedRatio_tendsto_atTop :
    Tendsto (fun K => (separatingFamily K).regularizedRatio) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ actual_ratio_tendsto_atTop
  filter_upwards [eventually_ge_atTop 2] with K hK
  exact (separatingFamily K).two_use_ratio_le_regularizedRatio (separatingFamily_pos hK)

/-- Small positive single-use information coexists with arbitrarily large regularized
Holevo gain and ratio. This is a rate statement, without an operational coding theorem. -/
theorem exists_small_chi_large_regularized_gain_and_ratio {ε : ℝ} (hε : 0<ε) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel,
      0<T.chi ∧ T.chi≤ε ∧ A≤T.regularizedGain ∧ R≤T.regularizedRatio := by
  have hs : ∀ᶠ K in atTop, (separatingFamily K).chi<ε :=
    actual_vanishing_diverging.1.eventually (gt_mem_nhds hε)
  have hg : ∀ᶠ K in atTop, A≤(separatingFamily K).regularizedGain :=
    actual_regularizedGain_tendsto_atTop.eventually (eventually_ge_atTop A)
  have hr : ∀ᶠ K in atTop, R≤(separatingFamily K).regularizedRatio :=
    actual_regularizedRatio_tendsto_atTop.eventually (eventually_ge_atTop R)
  obtain ⟨K,hK,hs,hg,hr⟩ := ((eventually_ge_atTop 2).and (hs.and (hg.and hr))).exists
  exact ⟨separatingFamily K,separatingFamily_pos hK,hs.le,hg,hr⟩

end Nonadditivity.DeterministicConsequences
