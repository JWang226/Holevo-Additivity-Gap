/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ActualConsequences

/-!
# Regularized Holevo supremum of actual tensor powers

`positiveTensorPower T n` is the actual Kraus tensor power with `n+1` uses.
Its first two powers are literally `T` and `T.tensor T`; no basis invariance
or assumed tensor-product information law is needed to identify them.
The supremum contains every positive integer number of uses, not a subsequence.

This is a regularized Holevo supremum. No operational coding theorem or
identification with operational classical capacity is asserted here.
-/

noncomputable section

namespace Nonadditivity.RegularizedHolevo

open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.ActualConsequences
open scoped Matrix ComplexOrder BigOperators

universe u

/-- Index of a genuine positive tensor power. Index `n` represents `n+1` factors. -/
def PositiveTensorIndex (ι : Type u) : ℕ → Type u
  | 0 => ι
  | n + 1 => PositiveTensorIndex ι n × ι

instance positiveTensorIndexFintype (ι : Type u) [Fintype ι] :
    (n : ℕ) → Fintype (PositiveTensorIndex ι n)
  | 0 => inferInstanceAs (Fintype ι)
  | n + 1 => by
    change Fintype (PositiveTensorIndex ι n × ι)
    letI := positiveTensorIndexFintype ι n
    infer_instance

instance positiveTensorIndexDecidableEq (ι : Type u) [DecidableEq ι] :
    (n : ℕ) → DecidableEq (PositiveTensorIndex ι n)
  | 0 => inferInstanceAs (DecidableEq ι)
  | n + 1 => by
    change DecidableEq (PositiveTensorIndex ι n × ι)
    letI := positiveTensorIndexDecidableEq ι n
    infer_instance

instance positiveTensorIndexNonempty (ι : Type u) [Nonempty ι] :
    (n : ℕ) → Nonempty (PositiveTensorIndex ι n)
  | 0 => inferInstanceAs (Nonempty ι)
  | n + 1 => by
    change Nonempty (PositiveTensorIndex ι n × ι)
    letI := positiveTensorIndexNonempty ι n
    infer_instance

theorem positiveTensorIndex_card (ι : Type u) [Fintype ι] (n : ℕ) :
    Fintype.card (PositiveTensorIndex ι n) = Fintype.card ι ^ (n + 1) := by
  induction n with
  | zero => simp [PositiveTensorIndex]
  | succ n ih =>
    change Fintype.card (PositiveTensorIndex ι n × ι) = _
    rw [Fintype.card_prod, ih]
    exact (pow_succ _ _).symm

/-- Every positive tensor power is constructed from the actual channel Kraus data. -/
def positiveTensorPower {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) :
    (n : ℕ) → KrausChannel (PositiveTensorIndex ι n) (PositiveTensorIndex ο n)
      (PositiveTensorIndex κ n)
  | 0 => T
  | n + 1 => (positiveTensorPower T n).tensor T

@[simp] theorem positiveTensorPower_zero {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : positiveTensorPower T 0 = T := rfl

@[simp] theorem positiveTensorPower_one {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : positiveTensorPower T 1 = T.tensor T := rfl

/-- The normalized Holevo information of the actual `n+1`-use tensor power. -/
def normalizedPowerHolevo {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) (n : ℕ) : ℝ :=
  (positiveTensorPower T n).holevoBits / ((n + 1 : ℕ) : ℝ)

@[simp] theorem normalizedPowerHolevo_zero {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : normalizedPowerHolevo T 0 = T.holevoBits := by
  simp [normalizedPowerHolevo, positiveTensorPower, PositiveTensorIndex,
    positiveTensorIndexFintype, positiveTensorIndexDecidableEq]
  rfl

@[simp] theorem normalizedPowerHolevo_one {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
    (T : KrausChannel ι ο κ) : normalizedPowerHolevo T 1 = (T.tensor T).holevoBits / 2 := rfl

/-- Output dimension bounds every normalized power, with no assumed Holevo
superadditivity, covariance, or tensor-basis invariance. -/
theorem normalizedPowerHolevo_le {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : KrausChannel ι ο κ) (n : ℕ) :
    normalizedPowerHolevo T n ≤ Scalar.log2 (Fintype.card ο) := by
  have hh := (positiveTensorPower T n).holevo_le_of_output_entropy
    (fun ρ => ((positiveTensorPower T n).output ρ).vonNeumann_nonneg)
  simp only [sub_zero, positiveTensorIndex_card, Nat.cast_pow, Real.log_pow] at hh
  have hb := div_le_div_of_nonneg_right hh Scalar.log_two_pos.le
  have hb' : (positiveTensorPower T n).holevoBits ≤
      ((n + 1 : ℕ) : ℝ) * Scalar.log2 (Fintype.card ο) := by
    convert hb using 1
    unfold Scalar.log2
    ring
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold normalizedPowerHolevo
  apply (div_le_iff₀ hn).2
  simpa only [mul_comm] using hb'

end Nonadditivity.RegularizedHolevo

namespace Nonadditivity.ActualConsequences.FiniteQuantumChannel

open Nonadditivity.RegularizedHolevo

/-- Supremum over all positive normalized actual tensor-power Holevo quantities. -/
def regularizedHolevo (T : FiniteQuantumChannel) : ℝ :=
  sSup (Set.range (normalizedPowerHolevo T.channel))

def regularizedGain (T : FiniteQuantumChannel) : ℝ := T.regularizedHolevo - T.chi

def regularizedRatio (T : FiniteQuantumChannel) : ℝ := T.regularizedHolevo / T.chi

theorem normalizedPowerHolevo_bddAbove (T : FiniteQuantumChannel) :
    BddAbove (Set.range (normalizedPowerHolevo T.channel)) := by
  refine ⟨Nonadditivity.Scalar.log2 (Fintype.card T.Output), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact normalizedPowerHolevo_le T.channel n

theorem normalizedPowerHolevo_le_regularized (T : FiniteQuantumChannel) (n : ℕ) :
    normalizedPowerHolevo T.channel n ≤ T.regularizedHolevo :=
  le_csSup T.normalizedPowerHolevo_bddAbove ⟨n, rfl⟩

theorem regularizedHolevo_le_log_output_dim (T : FiniteQuantumChannel) :
    T.regularizedHolevo ≤ Nonadditivity.Scalar.log2 (Fintype.card T.Output) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact normalizedPowerHolevo_le T.channel n

theorem chi_le_regularizedHolevo (T : FiniteQuantumChannel) : T.chi ≤ T.regularizedHolevo := by
  simpa only [normalizedPowerHolevo_zero, chi] using T.normalizedPowerHolevo_le_regularized 0

theorem half_chiTwo_le_regularizedHolevo (T : FiniteQuantumChannel) :
    T.chiTwo / 2 ≤ T.regularizedHolevo := by
  simpa only [normalizedPowerHolevo_one, chiTwo] using T.normalizedPowerHolevo_le_regularized 1

theorem regularizedHolevo_nonneg (T : FiniteQuantumChannel) : 0 ≤ T.regularizedHolevo :=
  T.chi_nonneg.trans T.chi_le_regularizedHolevo

theorem two_use_gain_le_regularizedGain (T : FiniteQuantumChannel) :
    T.chiTwo / 2 - T.chi ≤ T.regularizedGain := by
  unfold regularizedGain
  linarith [T.half_chiTwo_le_regularizedHolevo]

theorem two_use_ratio_le_regularizedRatio (T : FiniteQuantumChannel) (hχ : 0 < T.chi) :
    T.twoUseRatio ≤ T.regularizedRatio := by
  have h := div_le_div_of_nonneg_right T.half_chiTwo_le_regularizedHolevo hχ.le
  convert h using 1
  unfold twoUseRatio
  ring

end Nonadditivity.ActualConsequences.FiniteQuantumChannel

namespace Nonadditivity.ActualConsequences

open Filter Topology

/-- The regularized Holevo supremum diverges along the constructed actual
channel sequence. This assertion does not invoke an operational coding theorem. -/
theorem actual_regularizedHolevo_tendsto_atTop (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).regularizedHolevo) atTop atTop :=
  tendsto_atTop_mono (fun K => (separatingFamily inputs K).half_chiTwo_le_regularizedHolevo)
    (actual_vanishing_diverging inputs).2

theorem actual_regularizedGain_tendsto_atTop (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).regularizedGain) atTop atTop :=
  tendsto_atTop_mono (fun K => (separatingFamily inputs K).two_use_gain_le_regularizedGain)
    (actual_two_use_gain_tendsto_atTop inputs)

theorem actual_regularizedRatio_tendsto_atTop (inputs : AnalyticInputs) :
    Tendsto (fun K => (separatingFamily inputs K).regularizedRatio) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (actual_ratio_tendsto_atTop inputs)
  filter_upwards [eventually_ge_atTop 2] with K hK
  exact (separatingFamily inputs K).two_use_ratio_le_regularizedRatio (separatingFamily_pos inputs hK)

/-- Actual channels simultaneously achieve small single-use information and
large regularized Holevo gain, with a positive ratio denominator. -/
theorem actual_small_large_regularizedGain (inputs : AnalyticInputs) {ε R : ℝ} (hε : 0 < ε) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ ε ∧ R ≤ T.regularizedGain := by
  have hs : ∀ᶠ K in atTop, (separatingFamily inputs K).chi < ε :=
    (actual_vanishing_diverging inputs).1.eventually (gt_mem_nhds hε)
  have hg : ∀ᶠ K in atTop, R ≤ (separatingFamily inputs K).regularizedGain :=
    (actual_regularizedGain_tendsto_atTop inputs).eventually (eventually_ge_atTop R)
  obtain ⟨K, hK, hs, hg⟩ := ((eventually_ge_atTop 2).and (hs.and hg)).exists
  exact ⟨separatingFamily inputs K, separatingFamily_pos inputs hK, hs.le, hg⟩

/-- Both an arbitrarily large regularized Holevo gain and an arbitrarily large
regularized ratio are attained by a genuine finite quantum channel. -/
theorem actual_large_regularizedGain_and_ratio (inputs : AnalyticInputs) (A R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ A ≤ T.regularizedGain ∧ R ≤ T.regularizedRatio := by
  have hg : ∀ᶠ K in atTop, A ≤ (separatingFamily inputs K).regularizedGain :=
    (actual_regularizedGain_tendsto_atTop inputs).eventually (eventually_ge_atTop A)
  have hr : ∀ᶠ K in atTop, R ≤ (separatingFamily inputs K).regularizedRatio :=
    (actual_regularizedRatio_tendsto_atTop inputs).eventually (eventually_ge_atTop R)
  obtain ⟨K, hK, hg, hr⟩ := ((eventually_ge_atTop 2).and (hg.and hr)).exists
  exact ⟨separatingFamily inputs K, separatingFamily_pos inputs hK, hg, hr⟩

end Nonadditivity.ActualConsequences
