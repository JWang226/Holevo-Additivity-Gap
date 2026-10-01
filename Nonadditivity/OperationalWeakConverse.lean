/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalProjectedCode
import Nonadditivity.QuantumCodingGentle
import Nonadditivity.OperationalCapacity

/-! # Operational Holevo weak converse from actual decoders

The proof embeds the actual POVM by its concrete Naimark isometry, projects
each successful message into its orthogonal label, and uses the proved gentle
projection and entropy-continuity estimates. No measured relative entropy
or coding inequality is assumed.
-/

noncomputable section

namespace Nonadditivity.Operational

open Entropy Channels QuantumCodingContinuity OperationalFlaggedEntropy RegularizedHolevo
open Filter Topology
open scoped BigOperators ComplexOrder

namespace POVM

variable {ο μ : Type*} [Fintype ο] [DecidableEq ο] [Nonempty ο]
  [Fintype μ] [DecidableEq μ]

/-- The actual orthogonal comparison state is close whenever that message
is decoded with high probability, including zero-probability fallback. -/
theorem projectedState_traceDistance (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    traceDistance (P.projectedState ρ m) (P.dilate ρ) ≤
      Real.sqrt (2 * (1 - P.probability ρ m)) := by
  by_cases h : 0 < P.probability ρ m
  · rw [traceDistance_comm]
    exact traceDistance_gentle_projection (P.dilate ρ) (P.projectedState ρ m)
      (labelProjection m) (labelProjection_hermitian m) (labelProjection_idempotent m)
      (P.probability ρ m) h (P.probability_le_one ρ m)
      (P.labelProjection_compress_trace ρ m)
      (by simpa only [Complex.ofReal_inv] using P.projectedState_matrix_of_pos ρ m h)
  · have hz : P.probability ρ m = 0 :=
      le_antisymm (le_of_not_gt h) (P.probability_nonneg ρ m)
    rw [hz]
    exact (traceDistance_le_one _ _).trans (by norm_num)

end POVM

namespace Code

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
variable {T : KrausChannel ι ο κ} {M : ℕ}

theorem mean_projected_distance_le (C : Code T M) (hM : 0 < M) :
    (∑ m, traceDistance (C.decode.projectedState (T.output (C.encode m)) m)
      (C.decode.dilate (T.output (C.encode m)))) / M ≤ Real.sqrt (2 * C.error) := by
  have h₁ := div_le_div_of_nonneg_right (Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) =>
    C.decode.projectedState_traceDistance (T.output (C.encode m)) m) (Nat.cast_nonneg M)
  have h₂ := mean_sqrt_le_sqrt_mean hM
    (fun m => 2 * (1 - C.decode.probability (T.output (C.encode m)) m))
    (fun m => mul_nonneg (by norm_num) (sub_nonneg.mpr (C.decode.probability_le_one _ m)))
  have he : (∑ m, 2 * (1 - C.decode.probability (T.output (C.encode m)) m)) / M =
      2 * C.error := by
    rw [← Finset.mul_sum, mul_div_assoc, C.mean_failure_eq_error hM]
  rw [he] at h₂
  exact h₁.trans h₂

/-- A finite-block Holevo converse for actual channel input codewords and
actual POVM decoding error. All analytic and coding inequalities are proved. -/
theorem log_messages_le_holevo_add_error (C : Code T M) (hM : 0 < M) :
    Real.log M ≤ T.holevo + 2 * Real.sqrt (2 * C.error) *
      Real.log ((M : ℝ) * Fintype.card ο) + 4 * Real.log 2 := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have h := uniformInformation_le_add_of_mean_traceDistance hM
    (fun m => C.decode.dilate (T.output (C.encode m)))
    (fun m => C.decode.projectedState (T.output (C.encode m)) m)
    (C.mean_projected_distance_le hM)
  rw [uniformInformation_dilate] at h
  have hflag : uniformInformation hM
      (fun m => C.decode.projectedState (T.output (C.encode m)) m) = Real.log M :=
    uniformInformation_flags hM (fun m => C.decode.normalizedBlockState (T.output (C.encode m)) m)
  rw [hflag, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at h
  have hinfo := C.uniformInformation_le_holevo hM
  linarith

/-- At error at most one half, the actual dimension packing estimate
eliminates the message count from the continuity loss. -/
theorem log_messages_le_holevo_add_dimension_error (C : Code T M) (hM : 0 < M)
    (he : C.error ≤ 1 / 2) :
    Real.log M ≤ T.holevo + 2 * Real.sqrt (2 * C.error) *
      (Real.log 2 + 2 * Real.log (Fintype.card ο)) + 4 * Real.log 2 := by
  have hd : (0 : ℝ) < Fintype.card ο := by exact_mod_cast Fintype.card_pos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hp := C.messages_le_dimension_div_one_sub_error (by norm_num) he
  norm_num at hp
  have hprod : (M : ℝ) * Fintype.card ο ≤ 2 * (Fintype.card ο : ℝ) ^ 2 := by
    nlinarith
  have hl := Real.log_le_log (mul_pos hMpos hd) hprod
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hd.ne'),
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm := mul_le_mul_of_nonneg_left hl
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg (2 * C.error)))
  have hh := C.log_messages_le_holevo_add_error hM
  linarith

end Code

namespace CodeSequence

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
variable {T : KrausChannel ι ο κ}

/-- Explicit loss in the finite-block rate converse. -/
def holevoCorrection (S : CodeSequence T) (n : ℕ) : ℝ :=
  4 * Real.sqrt (2 * (S.code n).error) * Scalar.log2 (Fintype.card ο) +
    (2 * Real.sqrt (2 * (S.code n).error) + 4) / ((n + 1 : ℕ) : ℝ)

theorem rate_le_normalizedPowerHolevo_add_correction (S : CodeSequence T) (n : ℕ)
    (he : (S.code n).error ≤ 1 / 2) :
    S.rate n ≤ normalizedPowerHolevo T n + S.holevoCorrection n := by
  have h := (S.code n).log_messages_le_holevo_add_dimension_error (S.messages_pos n) he
  simp only [positiveTensorIndex_card, Nat.cast_pow, Real.log_pow] at h
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hd := div_le_div_of_nonneg_right h (mul_nonneg Scalar.log_two_pos.le hn.le)
  convert hd using 1 <;>
    dsimp [rate, holevoCorrection, normalizedPowerHolevo, KrausChannel.holevoBits, Scalar.log2] <;>
    (field_simp; all_goals ring)

omit [Nonempty ο] in
theorem holevoCorrection_tendsto_zero (S : CodeSequence T) (he : S.VanishingError) :
    Tendsto (S.holevoCorrection) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (2 * (S.code n).error)) atTop (𝓝 0) := by
    simpa using (he.const_mul 2).sqrt
  have hl : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hfirst : Tendsto (fun n => 4 * Real.sqrt (2 * (S.code n).error) *
      Scalar.log2 (Fintype.card ο)) atTop (𝓝 0) := by
    simpa using (hs.const_mul 4).mul_const (Scalar.log2 (Fintype.card ο))
  have hsecond : Tendsto (fun n => (2 * Real.sqrt (2 * (S.code n).error) + 4) /
      ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    exact ((hs.const_mul 2).add_const 4).div_atTop hl
  simpa only [holevoCorrection, zero_add] using hfirst.add hsecond

variable [Nonempty ι]

theorem hasRate_le_regularizedHolevoSupremum (S : CodeSequence T) {R : ℝ}
    (he : S.VanishingError) (hr : S.HasRate R) :
    R ≤ sSup (Set.range (normalizedPowerHolevo T)) := by
  let C := sSup (Set.range (normalizedPowerHolevo T))
  have hb : BddAbove (Set.range (normalizedPowerHolevo T)) := by
    refine ⟨Scalar.log2 (Fintype.card ο), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact normalizedPowerHolevo_le T n
  have hle (n : ℕ) : normalizedPowerHolevo T n ≤ C := le_csSup hb ⟨n, rfl⟩
  have hbound : ∀ᶠ n in atTop, S.rate n ≤ C + S.holevoCorrection n := by
    have hevent : ∀ᶠ n in atTop, (S.code n).error < 1 / 2 :=
      he.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [hevent] with n hn
    have h₁ := S.rate_le_normalizedPowerHolevo_add_correction n hn.le
    linarith [hle n]
  have hlimit : Tendsto (fun n => C + S.holevoCorrection n) atTop (𝓝 C) := by
    simpa using tendsto_const_nhds.add (S.holevoCorrection_tendsto_zero he)
  by_contra h
  have hCR : C < R := lt_of_not_ge h
  let r := (C + R) / 2
  have hCr : C < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hlo : ∀ᶠ n in atTop, r ≤ C + S.holevoCorrection n := by
    filter_upwards [hr r hrR, hbound] with n hn hb using hn.trans hb
  have hc := ge_of_tendsto hlimit hlo
  linarith

end CodeSequence

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- Every operationally achievable rate is bounded by the regularized
Holevo supremum, with no coding theorem used as an assumption. -/
theorem achievableRate_le_regularizedHolevoSupremum {T : KrausChannel ι ο κ} {R : ℝ}
    (hR : AchievableRate T R) : R ≤ sSup (Set.range (normalizedPowerHolevo T)) := by
  obtain ⟨S, he, hr⟩ := hR
  exact S.hasRate_le_regularizedHolevoSupremum he hr

/-- Operational capacity, independently defined through actual encoders and
decoders with vanishing average error, is at most the regularized Holevo
supremum of the genuine tensor powers. -/
theorem operationalCapacity_le_regularizedHolevoSupremum (T : KrausChannel ι ο κ) :
    operationalCapacity T ≤ sSup (Set.range (normalizedPowerHolevo T)) :=
  csSup_le ⟨0, zero_achievable T⟩ (fun _ h => achievableRate_le_regularizedHolevoSupremum h)

end Nonadditivity.Operational
