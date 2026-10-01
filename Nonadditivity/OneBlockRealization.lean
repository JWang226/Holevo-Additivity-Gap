/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.CollinsYounOne
import Nonadditivity.RegularizedHolevo

/-!
# One-block channels with only the Haar convergence input

The single-block free norm estimate is proved internally. Consequently the
single-block construction requires only the precise canonical Haar strong
convergence statement. All information quantities below are in bits.
-/

namespace Nonadditivity.OneBlockRealization

open ActualConsequences Channels.KrausChannel BlockConstruction

/-- The global analytic interface need only supply the free estimate for
two or more blocks; the one-block case is discharged internally. -/
theorem analyticInputs_of_higher_blocks
    (hCY : ∀ K n : ℕ, 2 ≤ K → 2 ≤ n → FreeModel.CollinsYounBound K n)
    (hBC : ∀ (K : ℕ) [NeZero K] (n : ℕ), 2 ≤ K → 1 ≤ n →
      HaarModel.HaarStrongConvergence K n) : AnalyticInputs := by
  refine ⟨?_, hBC⟩
  intro K n hK hn
  by_cases hn1 : n = 1
  · subst n
    exact CollinsYounOne.collinsYounBound_one hK
  · exact hCY K n hK (by omega)

variable {K : ℕ} [NeZero K]

theorem exists_one_block_bounds (hK : 2 ≤ K) {η : ℝ} (hη : 0 < η)
    (hBC : HaarModel.HaarStrongConvergence K 1) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      T.chi ≤ Scalar.aK K + η ∧
      Scalar.log2 K / (K : ℝ) ≤ T.chiTwo ∧
      Scalar.deltaK K - 2 * η ≤ T.gap := by
  obtain ⟨N, ω, h₁, h₂, _⟩ :=
    HaarModel.qualitative_realization_of_CY_and_Haar_strong_convergence
      1 hK (by omega) (mul_pos hη Scalar.log_two_pos)
      (CollinsYounOne.collinsYounBound_one hK) hBC
  let U := HaarModel.sampleUnitary K 1 N ω
  let C := Conversion.converted (blockChannel U 1)
  let T := FiniteQuantumChannel.ofKraus C
  have hp : 0 < T.chi :=
    PositiveHolevo.block_converted_holevoBits_pos hK U (by omega : 1 ≤ 1)
  have hu : T.chi ≤ Scalar.aK K + η := by
    simpa using HolevoBits.natural_upper_to_bits 1 h₁
  have hl : Scalar.log2 K / (K : ℝ) ≤ T.chiTwo := by
    simpa using HolevoBits.natural_lower_to_bits 1 h₂
  refine ⟨T, hp, hu, hl, ?_⟩
  unfold FiniteQuantumChannel.gap Scalar.deltaK
  linarith

/-- Strict nonadditivity of an actual channel with only the specified Haar
norm convergence left as an analytic premise. -/
theorem exists_positive_gap (hK : 2 ≤ K) (hlog : 18 < Real.log (K : ℝ))
    (hBC : HaarModel.HaarStrongConvergence K 1) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ 0 < T.gap := by
  have hδ := Scalar.deltaK_pos (show (0 : ℝ) < K by exact_mod_cast (by omega : 0 < K)) hlog
  obtain ⟨T, hp, _, _, hg⟩ := exists_one_block_bounds hK
    (show 0 < Scalar.deltaK K / 4 by positivity) hBC
  exact ⟨T, hp, by linarith⟩

/-- Strict nonadditivity requires only one-block canonical Haar convergence:
the free estimate and a suitable finite generator count are proved here. -/
theorem exists_nonadditive_channel
    (hBC : ∀ (K : ℕ) [NeZero K], 2 ≤ K → HaarModel.HaarStrongConvergence K 1) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ 0 < T.gap := by
  let K : ℕ := max 2 ⌈Real.exp 19⌉₊
  have hK : 2 ≤ K := le_max_left _ _
  letI : NeZero K := ⟨by omega⟩
  have hceil : (⌈Real.exp 19⌉₊ : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (le_max_right 2 ⌈Real.exp 19⌉₊)
  have hexp : Real.exp 19 ≤ (K : ℝ) := (Nat.le_ceil _).trans hceil
  have hlog := Real.log_le_log (Real.exp_pos 19) hexp
  rw [Real.log_exp] at hlog
  exact exists_positive_gap hK (by linarith) (hBC K hK)

/-- A quantitative ratio bound already follows from one block. -/
theorem exists_one_block_ratio_lower (hK : 2 ≤ K)
    (hBC : HaarModel.HaarStrongConvergence K 1) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      Real.log (K : ℝ) / 36 ≤ T.twoUseRatio := by
  have hKr : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hKpos : (0 : ℝ) < K := by linarith
  have ha := Scalar.aK_pos hKpos
  obtain ⟨T, hp, hu, hl, _⟩ := exists_one_block_bounds hK ha hBC
  refine ⟨T, hp, ?_⟩
  have hnum : 0 ≤ Scalar.log2 K / (K : ℝ) := by
    unfold Scalar.log2
    exact div_nonneg (div_nonneg (Real.log_pos hKr).le Scalar.log_two_pos.le) hKpos.le
  unfold FiniteQuantumChannel.twoUseRatio
  calc
    Real.log (K : ℝ) / 36 = (Real.log (K : ℝ) / 18) / 2 := by ring
    _ ≤ (Scalar.log2 K / (2 * (K : ℝ) * Scalar.aK K)) / 2 :=
      div_le_div_of_nonneg_right (Scalar.ratio_lower hKr) (by norm_num)
    _ = (Scalar.log2 K / (K : ℝ)) / (4 * Scalar.aK K) := by
      field_simp
      ring
    _ ≤ (Scalar.log2 K / (K : ℝ)) / (2 * T.chi) :=
      div_le_div_of_nonneg_left hnum (by positivity) (by linarith)
    _ ≤ T.chiTwo / (2 * T.chi) :=
      div_le_div_of_nonneg_right hl (by positivity)

/-- Arbitrarily large multiplicative nonadditivity needs only canonical
one-block Haar convergence, with the free estimate proved internally. -/
theorem exists_arbitrarily_large_ratio
    (hBC : ∀ (K : ℕ) [NeZero K], 2 ≤ K → HaarModel.HaarStrongConvergence K 1)
    (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ R ≤ T.twoUseRatio := by
  let L : ℝ := 36 * max R 0 + 1
  let K : ℕ := max 2 ⌈Real.exp L⌉₊
  have hK : 2 ≤ K := le_max_left _ _
  letI : NeZero K := ⟨by omega⟩
  have hceil : (⌈Real.exp L⌉₊ : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (le_max_right 2 ⌈Real.exp L⌉₊)
  have hlog := Real.log_le_log (Real.exp_pos L) ((Nat.le_ceil _).trans hceil)
  rw [Real.log_exp] at hlog
  obtain ⟨T, hp, hr⟩ := exists_one_block_ratio_lower hK (hBC K hK)
  refine ⟨T, hp, ?_⟩
  have hmax : R ≤ max R 0 := le_max_left _ _
  dsimp [L] at hlog
  linarith

theorem exists_arbitrarily_large_regularized_ratio
    (hBC : ∀ (K : ℕ) [NeZero K], 2 ≤ K → HaarModel.HaarStrongConvergence K 1)
    (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ R ≤ T.regularizedRatio := by
  obtain ⟨T, hp, hr⟩ := exists_arbitrarily_large_ratio hBC R
  exact ⟨T, hp, hr.trans (T.two_use_ratio_le_regularizedRatio hp)⟩

end Nonadditivity.OneBlockRealization
