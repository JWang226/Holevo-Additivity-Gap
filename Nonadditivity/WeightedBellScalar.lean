/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GeneralBell

/-! # Strict Bell entropy margins from arbitrarily small weight perturbations -/

noncomputable section

namespace Nonadditivity.WeightedBellScalar

open Entropy BellOutput
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section Merged
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The diagonal pair probabilities merge because the corresponding Bell
states coincide; off-diagonal branches retain their product probabilities. -/
def weights (p : κ → ℝ) : MergedLabel κ → ℝ
  | none => ∑ i, p i ^ 2
  | some z => p z.val.1 * p z.val.2

omit [DecidableEq κ] in
theorem weights_nonneg (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (z : MergedLabel κ) :
    0 ≤ weights p z := by
  cases z with
  | none => exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  | some z => exact mul_nonneg (hp _) (hp _)

theorem weights_sum (p : κ → ℝ) (hsum : ∑ i, p i = 1) :
    ∑ z, weights p z = 1 := by
  have h := split_pair_sum (fun z : κ × κ => p z.1 * p z.2)
  have ht : (∑ z : κ × κ, p z.1 * p z.2) = 1 := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hsum, mul_one]
  rw [ht] at h
  simpa only [Fintype.sum_option, weights, pow_two, add_comm] using h.symm

/-- Gibbs' inequality against the normalized uniform Bell mixture gives
the exact supporting line with slope `-log K` at diagonal mass `1/K`. -/
theorem shannon_le_of_merged_distribution [Nonempty κ] (r : MergedLabel κ → ℝ)
    (hr : ∀ z, 0 ≤ r z) (hsum : ∑ z, r z = 1) :
    shannon r ≤ 2 * Real.log (Fintype.card κ) - r none * Real.log (Fintype.card κ) := by
  have hk : (0 : ℝ) < Fintype.card κ := by positivity
  have hq (z : MergedLabel κ) : 0 < mergedWeights z := by
    cases z <;> dsimp [mergedWeights] <;> positivity
  have hb := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    GeneralBell.mul_log_lower (hr z) (hq z))
  have hcross : (∑ z, r z * Real.log (mergedWeights z)) =
      -2 * Real.log (Fintype.card κ) + r none * Real.log (Fintype.card κ) := by
    have hs := hsum
    rw [Fintype.sum_option] at hs
    have hs' : (∑ i, r (some i)) = 1 - r none := by linarith
    simp only [Fintype.sum_option, mergedWeights, one_div, Real.log_inv,
      Real.log_pow, ← Finset.sum_mul]
    rw [hs']
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum,
    mergedWeights_sum, hcross] at hb
  unfold shannon
  linarith

theorem weights_shannon_le [Nonempty κ] (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    shannon (weights p) ≤ 2 * Real.log (Fintype.card κ) -
      (∑ i, p i ^ 2) * Real.log (Fintype.card κ) :=
  shannon_le_of_merged_distribution (weights p) (weights_nonneg p hp) (weights_sum p hsum)

end Merged


/-- A two-coordinate perturbation, defined for every real parameter so its
continuity is available before imposing positivity. -/
def perturbedWeights {K : ℕ} (hK : 2 ≤ K) (t : ℝ) (i : Fin K) : ℝ :=
  1 / (K : ℝ) + (if i = ⟨0, by omega⟩ then t else 0) -
    (if i = ⟨1, by omega⟩ then t else 0)

@[simp] theorem perturbedWeights_zero {K : ℕ} (hK : 2 ≤ K) :
    perturbedWeights hK 0 = fun _ => 1 / (K : ℝ) := by
  funext i
  simp [perturbedWeights]

@[simp] theorem perturbedWeights_zero_index {K : ℕ} (hK : 2 ≤ K) (t : ℝ) :
    perturbedWeights hK t ⟨0, by omega⟩ = 1 / (K : ℝ) + t := by
  simp [perturbedWeights]

@[simp] theorem perturbedWeights_one_index {K : ℕ} (hK : 2 ≤ K) (t : ℝ) :
    perturbedWeights hK t ⟨1, by omega⟩ = 1 / (K : ℝ) - t := by
  simp [perturbedWeights]

theorem perturbedWeights_sum {K : ℕ} (hK : 2 ≤ K) (t : ℝ) :
    ∑ i, perturbedWeights hK t i = 1 := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  simp only [perturbedWeights, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  ring

theorem perturbedWeights_positive {K : ℕ} (hK : 2 ≤ K) {t : ℝ}
    (ht : 0 ≤ t) (htK : t < 1 / (K : ℝ)) (i : Fin K) :
    0 < perturbedWeights hK t i := by
  have hu : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  dsimp [perturbedWeights]
  split_ifs <;> linarith

theorem perturbedWeights_close {K : ℕ} (hK : 2 ≤ K) (t : ℝ) (i : Fin K) :
    |perturbedWeights hK t i - 1 / (K : ℝ)| ≤ |t| := by
  dsimp [perturbedWeights]
  split_ifs <;> ring_nf <;> simp [abs_neg, abs_nonneg]

theorem continuous_perturbedWeights_apply {K : ℕ} (hK : 2 ≤ K) (i : Fin K) :
    Continuous (fun t : ℝ => perturbedWeights hK t i) := by
  unfold perturbedWeights
  split_ifs <;> fun_prop

theorem continuous_perturbedWeights {K : ℕ} (hK : 2 ≤ K) :
    Continuous (perturbedWeights hK) :=
  continuous_pi (continuous_perturbedWeights_apply hK)

theorem perturbedWeights_sum_sq {K : ℕ} (hK : 2 ≤ K) (t : ℝ) :
    ∑ i, perturbedWeights hK t i ^ 2 = 1 / (K : ℝ) + 2 * t ^ 2 := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hpoint (i : Fin K) : perturbedWeights hK t i ^ 2 =
      (1 / (K : ℝ)) ^ 2 +
      (if i = ⟨0, by omega⟩ then 2 * (1 / (K : ℝ)) * t + t ^ 2 else 0) +
      (if i = ⟨1, by omega⟩ then -2 * (1 / (K : ℝ)) * t + t ^ 2 else 0) := by
    by_cases h0 : i = ⟨0, by omega⟩
    · simp [perturbedWeights, h0]
      ring
    · by_cases h1 : i = ⟨1, by omega⟩
      · simp [perturbedWeights, h1]
        ring
      · simp [perturbedWeights, h0, h1]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  ring

/-- The exact strict reserve in Bell entropy is quadratic in the small
weight perturbation. -/
theorem perturbedWeights_shannon_le {K : ℕ} (hK : 2 ≤ K) {t : ℝ}
    (ht : 0 ≤ t) (htK : t < 1 / (K : ℝ)) :
    shannon (weights (perturbedWeights hK t)) ≤
      2 * Real.log (K : ℝ) - Real.log (K : ℝ) / K -
        2 * t ^ 2 * Real.log (K : ℝ) := by
  letI : NeZero K := ⟨by omega⟩
  have h := weights_shannon_le (perturbedWeights hK t)
    (fun i => (perturbedWeights_positive hK ht htK i).le) (perturbedWeights_sum hK t)
  rw [perturbedWeights_sum_sq] at h
  simp only [Fintype.card_fin] at h
  convert h using 1
  ring

theorem perturbation_margin_pos {K : ℕ} (hK : 2 ≤ K) {t : ℝ} (ht : 0 < t) :
    0 < 2 * t ^ 2 * Real.log (K : ℝ) := by
  have hlog : 0 < Real.log (K : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos ht)) hlog

/-- Positive admissible perturbations exist within every prescribed
neighborhood of the uniform weights. -/
theorem exists_perturbation_parameter {K : ℕ} (hK : 2 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / (K : ℝ) ∧ t < ε := by
  have hu : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  refine ⟨min (ε / 2) ((1 / (K : ℝ)) / 2),
    lt_min (half_pos hε) (half_pos hu), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (half_lt_self hu)
  · exact (min_le_left _ _).trans_lt (half_lt_self hε)

end Nonadditivity.WeightedBellScalar
