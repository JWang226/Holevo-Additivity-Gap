/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarModel
import Nonadditivity.HolevoBits
import Nonadditivity.PositiveHolevo
import Nonadditivity.Asymptotics

/-!
# Asymptotic separation for actual finite quantum channels

The channels in this file are actual finite Kraus CPTP maps. They are chosen
from the proved qualitative realization using the specified normalized Haar
matrix model. The two remaining analytic inputs are displayed explicitly:
Collins--Youn's free-operator bound and the canonical Haar strong convergence
statement. No numerical Holevo family or entropy inequality is assumed.

The quantities here are Holevo information in bits. The file makes no
operational-capacity assertion and requires no coding theorem.
-/

noncomputable section

namespace Nonadditivity.ActualConsequences

open Filter Topology
open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.Channels.KrausChannel
open scoped BigOperators Matrix ComplexOrder

/-- A packaged finite quantum channel, retaining its genuine Kraus CPTP map
and all finite Hilbert-space and environment indices. -/
structure FiniteQuantumChannel where
  Input : Type
  Output : Type
  Environment : Type
  inputFinite : Fintype Input
  inputDecidable : DecidableEq Input
  inputNonempty : Nonempty Input
  outputFinite : Fintype Output
  outputDecidable : DecidableEq Output
  outputNonempty : Nonempty Output
  environmentFinite : Fintype Environment
  channel : @KrausChannel Input Output Environment inputFinite inputDecidable outputFinite environmentFinite

attribute [instance] FiniteQuantumChannel.inputFinite FiniteQuantumChannel.inputDecidable
  FiniteQuantumChannel.inputNonempty FiniteQuantumChannel.outputFinite
  FiniteQuantumChannel.outputDecidable FiniteQuantumChannel.outputNonempty
  FiniteQuantumChannel.environmentFinite

namespace FiniteQuantumChannel

/-- Package a concrete channel without changing its input, output, or map. -/
def ofKraus {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : FiniteQuantumChannel where
  Input := ι
  Output := ο
  Environment := κ
  inputFinite := inferInstance
  inputDecidable := inferInstance
  inputNonempty := inferInstance
  outputFinite := inferInstance
  outputDecidable := inferInstance
  outputNonempty := inferInstance
  environmentFinite := inferInstance
  channel := T

def chi (T : FiniteQuantumChannel) : ℝ := T.channel.holevoBits

def chiTwo (T : FiniteQuantumChannel) : ℝ := (T.channel.tensor T.channel).holevoBits

def gap (T : FiniteQuantumChannel) : ℝ := T.chiTwo - 2 * T.chi

def twoUseRatio (T : FiniteQuantumChannel) : ℝ := T.chiTwo / (2 * T.chi)

@[simp] theorem ofKraus_chi {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : (ofKraus T).chi = T.holevoBits := rfl

@[simp] theorem ofKraus_chiTwo {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : (ofKraus T).chiTwo = (T.tensor T).holevoBits := rfl

theorem chi_nonneg (T : FiniteQuantumChannel) : 0 ≤ T.chi := T.channel.holevoBits_nonneg

theorem chiTwo_nonneg (T : FiniteQuantumChannel) : 0 ≤ T.chiTwo :=
  (T.channel.tensor T.channel).holevoBits_nonneg

end FiniteQuantumChannel

/-- The precise global analytic inputs needed to apply the actual-channel
realization to each finite parameter pair. These are operator and random
matrix statements, not assumptions about channel information quantities. -/
structure AnalyticInputs : Prop where
  collinsYoun : ∀ (K n : ℕ), 2 ≤ K → 1 ≤ n → FreeModel.CollinsYounBound K n
  haarStrong : ∀ (K : ℕ) [NeZero K] (n : ℕ), 2 ≤ K → 1 ≤ n →
    HaarModel.HaarStrongConvergence K n

/-- The actual finite-channel existence bound in bits, obtained directly
from the canonical Haar model's analytic premises. -/
theorem exists_actual_channel_bounds_positive (inputs : AnalyticInputs) {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ (n : ℝ) * Scalar.aK K + η ∧
      (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo := by
  letI : NeZero K := ⟨by omega⟩
  have hε : 0 < η * Real.log 2 := mul_pos hη Scalar.log_two_pos
  obtain ⟨N, ω, h₁, h₂, _⟩ :=
    HaarModel.qualitative_realization_of_CY_and_Haar_strong_convergence n hK hn hε
      (inputs.collinsYoun K n hK hn) (inputs.haarStrong K n hK hn)
  let T := Conversion.converted (BlockConstruction.blockChannel
    (HaarModel.sampleUnitary K n N ω) n)
  refine ⟨FiniteQuantumChannel.ofKraus T,
    PositiveHolevo.block_converted_holevoBits_pos hK (HaarModel.sampleUnitary K n N ω) hn,
    ?_, ?_⟩
  · exact HolevoBits.natural_upper_to_bits n h₁
  · exact HolevoBits.natural_lower_to_bits n h₂

theorem exists_actual_channel_bounds (inputs : AnalyticInputs) {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ T : FiniteQuantumChannel,
      T.chi ≤ (n : ℝ) * Scalar.aK K + η ∧
      (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo := by
  obtain ⟨T, _, hu, hl⟩ := exists_actual_channel_bounds_positive inputs hK hn hη
  exact ⟨T, hu, hl⟩

/-- Instantiate the actual construction with the manuscript's integer
`sqrt(log)` block length, rather than postulating a numerical channel family. -/
theorem exists_actual_separating_channel_positive (inputs : AnalyticInputs) {K : ℕ} (hK : 2 ≤ K) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K ≤ T.chiTwo / 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hn : 1 ≤ Asymptotics.blockLength K := Asymptotics.blockLength_pos hK
  obtain ⟨T, hpos, h₁, h₂⟩ := exists_actual_channel_bounds_positive inputs hK hn
    (show 0 < 1 / (K : ℝ) by positivity)
  refine ⟨T, hpos, ?_, ?_⟩
  · calc
      T.chi ≤ (Asymptotics.blockLength K : ℝ) * Scalar.aK K + 1 / (K : ℝ) := h₁
      _ ≤ (Asymptotics.blockLength K : ℝ) * (9 / ((K : ℝ) * Real.log 2)) + 1 / (K : ℝ) :=
        by
          have hh := mul_le_mul_of_nonneg_left (Scalar.aK_le hKpos)
            (Nat.cast_nonneg (Asymptotics.blockLength K) : (0 : ℝ) ≤ Asymptotics.blockLength K)
          linarith
      _ = Asymptotics.separationUpper K := by unfold Asymptotics.separationUpper; ring
  · have hh := div_le_div_of_nonneg_right h₂ (show (0 : ℝ) ≤ 2 by norm_num)
    convert hh using 1
    unfold Asymptotics.separationLower Scalar.log2
    ring

theorem exists_actual_separating_channel (inputs : AnalyticInputs) {K : ℕ} (hK : 2 ≤ K) :
    ∃ T : FiniteQuantumChannel,
      T.chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K ≤ T.chiTwo / 2 := by
  obtain ⟨T, _, hu, hl⟩ := exists_actual_separating_channel_positive inputs hK
  exact ⟨T, hu, hl⟩

/-- An actual finite-dimensional channel sequence selected from the
construction. The first two indices use the identity channel; all later
indices use the proved Haar realization with the exact integer block length. -/
def separatingFamily (inputs : AnalyticInputs) (K : ℕ) : FiniteQuantumChannel :=
  if hK : 2 ≤ K then Classical.choose (exists_actual_separating_channel_positive inputs hK)
  else FiniteQuantumChannel.ofKraus (KrausChannel.identity : KrausChannel (Fin 1) (Fin 1) Unit)

theorem separatingFamily_bounds (inputs : AnalyticInputs) {K : ℕ} (hK : 2 ≤ K) :
    (separatingFamily inputs K).chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K ≤ (separatingFamily inputs K).chiTwo / 2 := by
  simp only [separatingFamily, dif_pos hK]
  exact (Classical.choose_spec (exists_actual_separating_channel_positive inputs hK)).2

/-- Strict positive single-use information of every nontrivial member of
this actual family, derived from the proved universal constructed lower bound. -/
theorem separatingFamily_pos (inputs : AnalyticInputs) {K : ℕ} (hK : 2 ≤ K) :
    0 < (separatingFamily inputs K).chi := by
  simp only [separatingFamily, dif_pos hK]
  exact (Classical.choose_spec (exists_actual_separating_channel_positive inputs hK)).1

/-- Vanishing single-use Holevo information and diverging two-use information
for a sequence of actual finite Kraus CPTP channels. Only the two explicitly
specified analytic inputs are hypotheses. -/
theorem actual_vanishing_diverging (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).chi) atTop (𝓝 0) ∧
      Tendsto (fun K => (separatingFamily inputs K).chiTwo / 2) atTop atTop := by
  obtain ⟨h₁, h₂, _⟩ := Asymptotics.vanishing_diverging_of_bounds
    (fun K => (separatingFamily inputs K).chi)
    (fun K => (separatingFamily inputs K).chiTwo / 2)
    (fun K => (separatingFamily inputs K).chiTwo / 2)
    (fun K => (separatingFamily inputs K).chi_nonneg)
    (fun K hK => (separatingFamily_bounds inputs hK).1)
    (fun K hK => (separatingFamily_bounds inputs hK).2)
    (fun _ => le_rfl)
  exact ⟨h₁, h₂⟩

/-- The actual sequence's additive Holevo gap diverges to infinity. -/
theorem actual_gap_tendsto_atTop (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).gap) atTop atTop := by
  obtain ⟨h₁, h₂⟩ := actual_vanishing_diverging inputs
  have hp := h₂.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hn := h₁.const_mul (-2)
  have hh := hp.atTop_add hn
  convert hh using 1
  ext K
  unfold FiniteQuantumChannel.gap
  ring

/-- Every finite requested additive gap is attained by an actual channel. -/
theorem actual_unbounded_gap (inputs : AnalyticInputs) (R : ℝ) :
    ∃ T : FiniteQuantumChannel, R ≤ T.gap := by
  obtain ⟨K, hK⟩ := ((actual_gap_tendsto_atTop inputs).eventually
    (eventually_ge_atTop R)).exists
  exact ⟨separatingFamily inputs K, hK⟩

/-- Simultaneously arbitrarily small single-use information and arbitrarily
large half-two-use information, attained by a genuine finite CPTP channel. -/
theorem actual_small_large (inputs : AnalyticInputs) {ε R : ℝ} (hε : 0 < ε) :
    ∃ T : FiniteQuantumChannel, T.chi ≤ ε ∧ R ≤ T.chiTwo / 2 := by
  obtain ⟨h₁, h₂⟩ := actual_vanishing_diverging inputs
  have hs : ∀ᶠ K in atTop, (separatingFamily inputs K).chi < ε :=
    h₁.eventually (gt_mem_nhds hε)
  have hl : ∀ᶠ K in atTop, R ≤ (separatingFamily inputs K).chiTwo / 2 :=
    h₂.eventually (eventually_ge_atTop R)
  obtain ⟨K, hs, hl⟩ := (hs.and hl).exists
  exact ⟨separatingFamily inputs K, hs.le, hl⟩

/-- The per-use gain available already with two uses diverges on the actual
channel sequence. This finite-block statement needs no operational coding theorem. -/
theorem actual_two_use_gain_tendsto_atTop (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).chiTwo / 2 -
      (separatingFamily inputs K).chi) atTop atTop := by
  have h := (actual_gap_tendsto_atTop inputs).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  convert h using 1
  ext K
  unfold FiniteQuantumChannel.gap
  ring

/-- Arbitrarily small single-use information and arbitrarily large two-use
per-use gain occur simultaneously for an actual finite quantum channel. -/
theorem actual_small_large_gain (inputs : AnalyticInputs) {ε R : ℝ} (hε : 0 < ε) :
    ∃ T : FiniteQuantumChannel, T.chi ≤ ε ∧ R ≤ T.chiTwo / 2 - T.chi := by
  have hs : ∀ᶠ K in atTop, (separatingFamily inputs K).chi < ε :=
    (actual_vanishing_diverging inputs).1.eventually (gt_mem_nhds hε)
  have hl : ∀ᶠ K in atTop, R ≤ (separatingFamily inputs K).chiTwo / 2 -
      (separatingFamily inputs K).chi :=
    (actual_two_use_gain_tendsto_atTop inputs).eventually (eventually_ge_atTop R)
  obtain ⟨K, hs, hl⟩ := (hs.and hl).exists
  exact ⟨separatingFamily inputs K, hs.le, hl⟩

/-- The genuine two-use ratio diverges, with its denominator proved positive
for all `K ≥ 2`. No channel positivity premise is left to the caller. -/
theorem actual_ratio_tendsto_atTop (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).twoUseRatio) atTop atTop := by
  obtain ⟨hχ, htwo⟩ := actual_vanishing_diverging inputs
  have hsmall : ∀ᶠ K in atTop, (separatingFamily inputs K).chi < 1 :=
    hχ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbound : ∀ᶠ K in atTop,
      (separatingFamily inputs K).chiTwo / 2 ≤ (separatingFamily inputs K).twoUseRatio := by
    filter_upwards [hsmall, eventually_ge_atTop 2] with K hs hK
    have hp := separatingFamily_pos inputs hK
    have hn := (separatingFamily inputs K).chiTwo_nonneg
    have hm := mul_le_mul_of_nonneg_left hs.le hn
    unfold FiniteQuantumChannel.twoUseRatio
    apply (le_div_iff₀ (by positivity : 0 < 2 * (separatingFamily inputs K).chi)).2
    nlinarith
  exact tendsto_atTop_mono' atTop hbound htwo

/-- Arbitrarily large additive and multiplicative violations occur
simultaneously for an actual finite channel with strictly positive information. -/
theorem actual_large_gap_and_ratio (inputs : AnalyticInputs) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ A ≤ T.gap ∧ R ≤ T.twoUseRatio := by
  have hg : ∀ᶠ K in atTop, A ≤ (separatingFamily inputs K).gap :=
    (actual_gap_tendsto_atTop inputs).eventually (eventually_ge_atTop A)
  have hr : ∀ᶠ K in atTop, R ≤ (separatingFamily inputs K).twoUseRatio :=
    (actual_ratio_tendsto_atTop inputs).eventually (eventually_ge_atTop R)
  obtain ⟨K, hK, hg, hr⟩ := ((eventually_ge_atTop 2).and (hg.and hr)).exists
  exact ⟨separatingFamily inputs K, separatingFamily_pos inputs hK, hg, hr⟩

end Nonadditivity.ActualConsequences
