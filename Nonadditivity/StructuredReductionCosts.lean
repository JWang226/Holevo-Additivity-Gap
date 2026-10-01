/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.StructuredCostBounds
import Nonadditivity.TensorPartitionReduction
import Nonadditivity.WordBallReduction

/-! The literal products of the constructed structured reductions satisfy the
manuscript's numerical budgets. -/

namespace Nonadditivity.StructuredReductionCosts

noncomputable section
open scoped BigOperators
open StructuredCostBounds
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] {K n : ℕ} [NeZero K]

theorem tensor_dimensionCost_le (v : Fin n → Fin K → FreeGroup α) :
    (TensorPartitionReduction.dimensionCost v (tensorSteps n) : ℝ) ≤
      ∏ j ∈ Finset.range (tensorSteps n), 2 * (tensorSupportBound K n (j + 1) : ℝ) := by
  have h := TensorPartitionReduction.dimensionCost_le_prod v (tensorSteps n)
  have he : (∏ j ∈ Finset.range (tensorSteps n), 2 * tensorSupportBound K n (j + 1)) =
      ∏ j ∈ Finset.range (tensorSteps n), 2 * (1 + 2 ^ (j + 2) * K ^ TensorPartitionReduction.width n (j + 1)) := by
    simp only [tensorSupportBound, dyadicCeil_eq_div, TensorPartitionReduction.width, Nat.add_assoc]
  rw [← he] at h
  exact_mod_cast h

theorem tensor_errorCost_le (v : Fin n → Fin K → FreeGroup α) :
    (TensorPartitionReduction.errorCost v (tensorSteps n) : ℝ) ≤
      ∏ j ∈ Finset.range (tensorSteps n), 6 * (tensorSupportBound K n (j + 1) : ℝ) := by
  have h := TensorPartitionReduction.errorCost_le_prod v (tensorSteps n)
  have he : (∏ j ∈ Finset.range (tensorSteps n), 6 * tensorSupportBound K n (j + 1)) =
      ∏ j ∈ Finset.range (tensorSteps n), 6 * (1 + 2 ^ (j + 2) * K ^ TensorPartitionReduction.width n (j + 1)) := by
    simp only [tensorSupportBound, dyadicCeil_eq_div, TensorPartitionReduction.width, Nat.add_assoc]
  rw [← he] at h
  exact_mod_cast h

theorem word_dimensionCost_le (hn : 1 ≤ n) :
    (WordBallReduction.dimensionCost n (wordLength K) (wordSteps K) : ℝ) ≤
      ∏ i ∈ Finset.range (wordSteps K), 2 * (wordSupportBound K n (i + 1) : ℝ) := by
  have h := WordBallReduction.dimensionCost_le n (wordLength K) (wordSteps K) hn
  have he : (∏ i ∈ Finset.range (wordSteps K), 2 * wordSupportBound K n (i + 1)) =
      ∏ i ∈ Finset.range (wordSteps K), 4 * n * 3 ^ WordBallReduction.radius (wordLength K) (i + 1) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [wordSupportBound, dyadicCeil_eq_div, WordBallReduction.radius, Nat.ceilDiv_eq_add_pred_div]
    ring
  rw [← he] at h
  exact_mod_cast h

theorem word_errorCost_le (hn : 1 ≤ n) :
    (WordBallReduction.errorCost n (wordLength K) (wordSteps K) : ℝ) ≤
      ∏ i ∈ Finset.range (wordSteps K), 6 * (wordSupportBound K n (i + 1) : ℝ) := by
  have h := WordBallReduction.errorCost_le n (wordLength K) (wordSteps K) hn
  have he : (∏ i ∈ Finset.range (wordSteps K), 6 * wordSupportBound K n (i + 1)) =
      ∏ i ∈ Finset.range (wordSteps K), 12 * n * 3 ^ WordBallReduction.radius (wordLength K) (i + 1) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [wordSupportBound, dyadicCeil_eq_div, WordBallReduction.radius, Nat.ceilDiv_eq_add_pred_div]
    ring
  rw [← he] at h
  exact_mod_cast h

theorem dimensionCosts_le (v : Fin n → Fin K → FreeGroup α) (hn : 1 ≤ n) :
    (TensorPartitionReduction.dimensionCost v (tensorSteps n) : ℝ) *
      WordBallReduction.dimensionCost n (wordLength K) (wordSteps K) ≤ supportProduct K n 2 := by
  exact mul_le_mul (tensor_dimensionCost_le v) (word_dimensionCost_le hn)
    (by positivity) (by positivity)

theorem errorCosts_le (v : Fin n → Fin K → FreeGroup α) (hn : 1 ≤ n) :
    (TensorPartitionReduction.errorCost v (tensorSteps n) : ℝ) *
      WordBallReduction.errorCost n (wordLength K) (wordSteps K) ≤ supportProduct K n 6 := by
  exact mul_le_mul (tensor_errorCost_le v) (word_errorCost_le hn)
    (by positivity) (by positivity)

theorem prescribed_lower_bound_inv {K n : ℕ} (hK : 2 ≤ K) :
    (Real.sqrt 2 * (K : ℝ) ^ (-((n : ℝ) + 1) / 2))⁻¹ =
      Real.exp (((n : ℝ) + 1) * Real.log K / 2) / Real.sqrt 2 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  rw [Real.rpow_def_of_pos hKr]
  have he : Real.log (K : ℝ) * (-((n : ℝ) + 1) / 2) =
      -(((n : ℝ) + 1) * Real.log K / 2) := by ring
  rw [he, Real.exp_neg, mul_inv_rev, inv_inv]
  rfl

theorem initial_factor_le {K n : ℕ} {ρ : ℝ} (hK : 2 ≤ K)
    (hρ : Real.sqrt 2 * (K : ℝ) ^ (-((n : ℝ) + 1) / 2) ≤ ρ) :
    3 * (1 + ρ⁻¹) ≤ initialFactor K n := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hp : 0 < Real.sqrt 2 * (K : ℝ) ^ (-((n : ℝ) + 1) / 2) := by positivity
  have hi := one_div_le_one_div_of_le hp hρ
  rw [one_div, one_div, prescribed_lower_bound_inv hK] at hi
  dsimp [initialFactor]
  linarith

/-- The error factor of the actual tensor and word chains obeys the full
manuscript budget as soon as the original polynomial contains the prescribed
test. No cardinality or summed-log premise is left. -/
theorem actual_error_bound (v : Fin n → Fin K → FreeGroup α) {ρ : ℝ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hρ : Real.sqrt 2 * (K : ℝ) ^ (-((n : ℝ) + 1) / 2) ≤ ρ) :
    3 * (1 + ρ⁻¹) *
      ((TensorPartitionReduction.errorCost v (tensorSteps n) : ℝ) *
        WordBallReduction.errorCost n (wordLength K) (wordSteps K)) ≤
      Real.exp (Quantitative.gamma (Real.log K) * n) := by
  obtain ⟨_, hn64, _, _⟩ := Quantitative.threshold_consequences hK hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  exact (mul_le_mul (initial_factor_le hK hρ) (errorCosts_le v hn1)
    (by positivity) (initialFactor_pos K n).le).trans (errorProduct_bound hK hn)

/-- The final doubled coefficient size, when the initial Gram space has at
most `J K^n` coordinates, satisfies the manuscript's logarithmic budget. -/
theorem actual_coefficient_bound (v : Fin n → Fin K → FreeGroup α) {d₀ : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hd : d₀ ≤ netCardBound K n * K ^ n) (hdpos : 0 < d₀) :
    Real.log (2 * (2 * d₀ * TensorPartitionReduction.dimensionCost v (tensorSteps n) *
      WordBallReduction.dimensionCost n (wordLength K) (wordSteps K) : ℕ)) ≤
      2 * (K : ℝ) ^ (2 * n) * Real.log (1 + 2 * (n : ℝ)) := by
  obtain ⟨_, hn64, _, _⟩ := Quantitative.threshold_consequences hK hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hdreal : (d₀ : ℝ) ≤ (netCardBound K n : ℝ) * (K : ℝ)^n := by exact_mod_cast hd
  have hp := dimensionCosts_le v hn1
  have hm := mul_le_mul hdreal hp (by positivity)
    (by positivity : 0 ≤ (netCardBound K n : ℝ) * (K : ℝ)^n)
  have hsize : (2 * d₀ * TensorPartitionReduction.dimensionCost v (tensorSteps n) *
      WordBallReduction.dimensionCost n (wordLength K) (wordSteps K) : ℕ) ≤
      coefficientBound K n := by
    dsimp [coefficientBound]
    push_cast
    nlinarith
  have hpos : (0 : ℝ) < (2 * d₀ * TensorPartitionReduction.dimensionCost v (tensorSteps n) *
      WordBallReduction.dimensionCost n (wordLength K) (wordSteps K) : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hdpos)
      (TensorPartitionReduction.dimensionCost_pos v _)) (WordBallReduction.dimensionCost_pos _ _ _)
  exact (Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) hpos)
      (mul_le_mul_of_nonneg_left hsize (by norm_num : (0 : ℝ) ≤ 2))).trans
    (coefficientBound_log_bound hK hn)

end
end Nonadditivity.StructuredReductionCosts
