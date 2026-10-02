/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalConverse
import Nonadditivity.RegularizedHolevo

/-! # Operational classical capacity from actual quantum codes

The definition quantifies over input density matrices and POVM decoders on
every positive tensor power. Achievability requires vanishing actual average
error. The dimension converse is proved directly from those probabilities.
This definition does not identify capacity with a Holevo supremum.
-/

noncomputable section

namespace Nonadditivity.Operational

open Entropy Channels RegularizedHolevo Filter Topology
open scoped BigOperators ComplexOrder

variable {ι ο κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- Codes for all positive block lengths. Index `n` means `n+1` channel uses. -/
structure CodeSequence (T : KrausChannel ι ο κ) where
  messages : ℕ → ℕ
  messages_pos : ∀ n, 0 < messages n
  code : ∀ n, Code (positiveTensorPower T n) (messages n)

namespace CodeSequence

variable {T : KrausChannel ι ο κ}

/-- Communication rate in bits per channel use. -/
def rate (S : CodeSequence T) (n : ℕ) : ℝ :=
  Scalar.log2 (S.messages n) / ((n + 1 : ℕ) : ℝ)

def VanishingError (S : CodeSequence T) : Prop :=
  Tendsto (fun n => (S.code n).error) atTop (𝓝 0)

def HasRate (S : CodeSequence T) (R : ℝ) : Prop :=
  ∀ r < R, ∀ᶠ n in atTop, r ≤ S.rate n

omit [Nonempty ι] [Nonempty ο] in
theorem rate_nonneg (S : CodeSequence T) (n : ℕ) : 0 ≤ S.rate n := by
  apply div_nonneg _ (by positivity)
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast S.messages_pos n))
    Scalar.log_two_pos.le

private theorem scalar_rate_bound {M d n : ℕ} (hM : 0 < M) (hd : 0 < d)
    (hbound : (M : ℝ) ≤ 2 * (d : ℝ) ^ (n + 1)) :
    Scalar.log2 M / ((n + 1 : ℕ) : ℝ) ≤
      Scalar.log2 d + 1 / ((n + 1 : ℕ) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog := Real.log_le_log hMR hbound
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hdR.ne'),
    Real.log_pow] at hlog
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold Scalar.log2
  apply (div_le_iff₀ hn).mpr
  apply (div_le_iff₀ Scalar.log_two_pos).mpr
  have hid : (Real.log d / Real.log 2 + 1 / ((n + 1 : ℕ) : ℝ)) *
      ((n + 1 : ℕ) : ℝ) * Real.log 2 =
      Real.log 2 + ((n + 1 : ℕ) : ℝ) * Real.log d := by
    field_simp
    ring
  rwa [hid]

omit [Nonempty ι] in
theorem rate_le_output_dimension_of_error_le_half (S : CodeSequence T) (n : ℕ)
    (he : (S.code n).error ≤ 1 / 2) :
    S.rate n ≤ Scalar.log2 (Fintype.card ο) + 1 / ((n + 1 : ℕ) : ℝ) := by
  have h := (S.code n).messages_le_dimension_div_one_sub_error (by norm_num) he
  simp only [positiveTensorIndex_card, Nat.cast_pow] at h
  apply scalar_rate_bound (S.messages_pos n) Fintype.card_pos
  norm_num at h
  linarith

omit [Nonempty ο] in
theorem rate_le_input_dimension_of_error_le_half (S : CodeSequence T) (n : ℕ)
    (he : (S.code n).error ≤ 1 / 2) :
    S.rate n ≤ Scalar.log2 (Fintype.card ι) + 1 / ((n + 1 : ℕ) : ℝ) := by
  have he' : (S.code n).pulledBack.error ≤ 1 / 2 := by
    simpa only [Code.error, Code.pulledBack_success] using he
  have h := (S.code n).pulledBack.messages_le_dimension_div_one_sub_error
    (by norm_num) he'
  simp only [positiveTensorIndex_card, Nat.cast_pow] at h
  apply scalar_rate_bound (S.messages_pos n) Fintype.card_pos
  norm_num at h
  linarith

private theorem inverse_length_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  exact (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).comp
    (tendsto_add_atTop_nat 1)

omit [Nonempty ι] [Nonempty ο] in
private theorem hasRate_le_of_eventual_bound (S : CodeSequence T) {R d : ℝ}
    (hr : S.HasRate R)
    (hbound : ∀ᶠ n in atTop, S.rate n ≤ d + 1 / ((n + 1 : ℕ) : ℝ)) : R ≤ d := by
  by_contra h
  have hlt : d < R := lt_of_not_ge h
  let r := (d + R) / 2
  have hdr : d < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hlimit : Tendsto (fun n : ℕ => d + 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.add inverse_length_tendsto
  have hlow : ∀ᶠ n in atTop, r ≤ d + 1 / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hr r hrR, hbound] with n h₁ h₂ using h₁.trans h₂
  have hrd := ge_of_tendsto hlimit hlow
  linarith

omit [Nonempty ι] in
theorem hasRate_le_log_output_dimension (S : CodeSequence T) {R : ℝ}
    (he : S.VanishingError) (hr : S.HasRate R) : R ≤ Scalar.log2 (Fintype.card ο) := by
  apply hasRate_le_of_eventual_bound S hr
  have hevent : ∀ᶠ n in atTop, (S.code n).error < 1 / 2 :=
    he.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hevent] with n hn
  exact S.rate_le_output_dimension_of_error_le_half n hn.le

omit [Nonempty ο] in
theorem hasRate_le_log_input_dimension (S : CodeSequence T) {R : ℝ}
    (he : S.VanishingError) (hr : S.HasRate R) : R ≤ Scalar.log2 (Fintype.card ι) := by
  apply hasRate_le_of_eventual_bound S hr
  have hevent : ∀ᶠ n in atTop, (S.code n).error < 1 / 2 :=
    he.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hevent] with n hn
  exact S.rate_le_input_dimension_of_error_le_half n hn.le

end CodeSequence

/-- A rate is achievable if actual codes attain every strictly smaller rate
eventually, while their actual average decoding error tends to zero. -/
def AchievableRate (T : KrausChannel ι ο κ) (R : ℝ) : Prop :=
  ∃ S : CodeSequence T, S.VanishingError ∧ S.HasRate R

/-- Operational capacity, defined solely using physical encoders, POVMs,
communication rates and vanishing Born error. -/
def operationalCapacity (T : KrausChannel ι ο κ) : ℝ :=
  sSup {R : ℝ | AchievableRate T R}

/-- The always-correct code carrying a single message. -/
def oneMessage (T : KrausChannel ι ο κ) : Code T 1 where
  encode := fun _ => maximallyMixed ι
  decode := {
    effect := fun _ => 1
    positive := fun _ => Matrix.PosSemidef.one
    complete := by simp }

omit [Nonempty ο] in
@[simp] theorem oneMessage_success (T : KrausChannel ι ο κ) : (oneMessage T).success = 1 := by
  simp [Code.success, oneMessage, POVM.probability, DensityMatrix.normalized]

omit [Nonempty ο] in
@[simp] theorem oneMessage_error (T : KrausChannel ι ο κ) : (oneMessage T).error = 0 := by
  simp [Code.error]

def oneMessageSequence (T : KrausChannel ι ο κ) : CodeSequence T where
  messages := fun _ => 1
  messages_pos := fun _ => Nat.zero_lt_one
  code := fun n => oneMessage (positiveTensorPower T n)

omit [Nonempty ο] in
theorem zero_achievable (T : KrausChannel ι ο κ) : AchievableRate T 0 := by
  refine ⟨oneMessageSequence T, ?_, ?_⟩
  · simp [CodeSequence.VanishingError, oneMessageSequence]
  · intro r hr
    apply Filter.Eventually.of_forall
    intro n
    exact hr.le.trans ((oneMessageSequence T).rate_nonneg n)

omit [Nonempty ι] in
theorem achievableRate_le_log_output_dimension {T : KrausChannel ι ο κ} {R : ℝ}
    (hR : AchievableRate T R) : R ≤ Scalar.log2 (Fintype.card ο) := by
  obtain ⟨S, he, hr⟩ := hR
  exact S.hasRate_le_log_output_dimension he hr

omit [Nonempty ο] in
theorem achievableRate_le_log_input_dimension {T : KrausChannel ι ο κ} {R : ℝ}
    (hR : AchievableRate T R) : R ≤ Scalar.log2 (Fintype.card ι) := by
  obtain ⟨S, he, hr⟩ := hR
  exact S.hasRate_le_log_input_dimension he hr

omit [Nonempty ι] in
theorem achievableRates_bddAbove (T : KrausChannel ι ο κ) :
    BddAbove {R : ℝ | AchievableRate T R} :=
  ⟨Scalar.log2 (Fintype.card ο), fun _ h => achievableRate_le_log_output_dimension h⟩

theorem operationalCapacity_nonneg (T : KrausChannel ι ο κ) : 0 ≤ operationalCapacity T :=
  le_csSup (achievableRates_bddAbove T) (zero_achievable T)

omit [Nonempty ι] in
theorem achievableRate_le_capacity {T : KrausChannel ι ο κ} {R : ℝ}
    (hR : AchievableRate T R) : R ≤ operationalCapacity T :=
  le_csSup (achievableRates_bddAbove T) hR

theorem operationalCapacity_le_log_output_dimension (T : KrausChannel ι ο κ) :
    operationalCapacity T ≤ Scalar.log2 (Fintype.card ο) :=
  csSup_le ⟨0, zero_achievable T⟩ (fun _ h => achievableRate_le_log_output_dimension h)

omit [Nonempty ο] in
theorem operationalCapacity_le_log_input_dimension (T : KrausChannel ι ο κ) :
    operationalCapacity T ≤ Scalar.log2 (Fintype.card ι) :=
  csSup_le ⟨0, zero_achievable T⟩ (fun _ h => achievableRate_le_log_input_dimension h)

end Nonadditivity.Operational
