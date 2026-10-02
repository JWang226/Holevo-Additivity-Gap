/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalCapacity
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Dimension strong converse for genuine quantum codes

Above either the input or output logarithmic dimension, the actual decoding
success tends to zero. The finite bound is exponential in the block length.
-/

noncomputable section

namespace Nonadditivity.Operational.CodeSequence

open Channels RegularizedHolevo Filter Topology

variable {ι ο κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
variable {T : KrausChannel ι ο κ}

private theorem scalar_dimension_ratio_bound {M d n : ℕ} (hM : 0 < M) (hd : 0 < d)
    {R : ℝ} (hR : R ≤ Scalar.log2 M / ((n + 1 : ℕ) : ℝ)) :
    (d : ℝ) ^ (n + 1) / M ≤
      Real.exp (((n + 1 : ℕ) : ℝ) * (Scalar.log2 d - R) * Real.log 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog : R * ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log M := by
    apply (le_div_iff₀ Scalar.log_two_pos).mp
    exact (le_div_iff₀ hn).mp hR
  have heq : (d : ℝ) ^ (n + 1) / M =
      Real.exp (((n + 1 : ℕ) : ℝ) * Real.log d - Real.log M) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hdR, Real.exp_log hMR]
  rw [heq]
  apply Real.exp_le_exp.mpr
  have hcancel : Scalar.log2 d * Real.log 2 = Real.log d := by
    exact div_mul_cancel₀ _ Scalar.log_two_pos.ne'
  calc
    ((n + 1 : ℕ) : ℝ) * Real.log d - Real.log M ≤
        ((n + 1 : ℕ) : ℝ) * Real.log d -
          R * ((n + 1 : ℕ) : ℝ) * Real.log 2 := sub_le_sub_left hlog _
    _ = ((n + 1 : ℕ) : ℝ) * (Scalar.log2 d - R) * Real.log 2 := by
      rw [mul_sub, sub_mul, mul_assoc _ (Scalar.log2 d), hcancel]
      ring

/-- Exponential decoding-success bound at any finite block length. -/
theorem success_le_output_exponential [Nonempty ο] (S : CodeSequence T)
    (n : ℕ) {R : ℝ} (hR : R ≤ S.rate n) :
    (S.code n).success ≤
      Real.exp (((n + 1 : ℕ) : ℝ) * (Scalar.log2 (Fintype.card ο) - R) * Real.log 2) := by
  have h := (S.code n).success_le_dimension_div_messages
  simp only [positiveTensorIndex_card, Nat.cast_pow] at h
  exact h.trans (scalar_dimension_ratio_bound (S.messages_pos n) Fintype.card_pos hR)

theorem success_le_input_exponential [Nonempty ι] (S : CodeSequence T)
    (n : ℕ) {R : ℝ} (hR : R ≤ S.rate n) :
    (S.code n).success ≤
      Real.exp (((n + 1 : ℕ) : ℝ) * (Scalar.log2 (Fintype.card ι) - R) * Real.log 2) := by
  have h := (S.code n).success_le_input_dimension_div_messages
  simp only [positiveTensorIndex_card, Nat.cast_pow] at h
  exact h.trans (scalar_dimension_ratio_bound (S.messages_pos n) Fintype.card_pos hR)

private theorem success_tendsto_zero_of_exponential_bound
    (S : CodeSequence T) {R d : ℝ} (hR : S.HasRate R) (hd : d < R)
    (hbound : ∀ n r, r ≤ S.rate n → (S.code n).success ≤
      Real.exp (((n + 1 : ℕ) : ℝ) * (d - r) * Real.log 2)) :
    Tendsto (fun n => (S.code n).success) atTop (𝓝 0) := by
  let r := (d + R) / 2
  have hdr : d < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hnegative : (d - r) * Real.log 2 < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hdr) Scalar.log_two_pos
  have hlimit : Tendsto
      (fun n : ℕ => Real.exp (((n + 1 : ℕ) : ℝ) * (d - r) * Real.log 2))
      atTop (𝓝 0) := by
    have hq := tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_nonneg ((d - r) * Real.log 2)) (Real.exp_lt_one_iff.mpr hnegative)
    simpa only [← Real.exp_nat_mul, mul_assoc] using hq.comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero' (Eventually.of_forall (fun n => (S.code n).success_nonneg)) _ hlimit
  filter_upwards [hR r hrR] with n hn
  exact hbound n r hn

/-- Every rate strictly above the output dimension forces error to one. -/
theorem error_tendsto_one_of_output_rate [Nonempty ο] (S : CodeSequence T)
    {R : ℝ} (hR : S.HasRate R) (hd : Scalar.log2 (Fintype.card ο) < R) :
    Tendsto (fun n => (S.code n).error) atTop (𝓝 1) := by
  have h := success_tendsto_zero_of_exponential_bound S hR hd
    (fun n _ hn => S.success_le_output_exponential n hn)
  simpa only [sub_zero] using tendsto_const_nhds.sub h

/-- The same strong converse holds above the input dimension. -/
theorem error_tendsto_one_of_input_rate [Nonempty ι] (S : CodeSequence T)
    {R : ℝ} (hR : S.HasRate R) (hd : Scalar.log2 (Fintype.card ι) < R) :
    Tendsto (fun n => (S.code n).error) atTop (𝓝 1) := by
  have h := success_tendsto_zero_of_exponential_bound S hR hd
    (fun n _ hn => S.success_le_input_exponential n hn)
  simpa only [sub_zero] using tendsto_const_nhds.sub h

end Nonadditivity.Operational.CodeSequence
