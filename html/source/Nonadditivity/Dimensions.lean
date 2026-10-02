/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The input-qubit count for the exact integer dimension

These are numerical dimension statements. They do not assert existence of a
channel with these dimensions. Unlike a big-O-only estimate, the ceiling
error below vanishes even after multiplication by the block length.
-/

noncomputable section

namespace Nonadditivity.Dimensions

open Scalar Filter Topology

def inputDimension (K N n : ℕ) : ℕ := 2 * N ^ n * K ^ (2 * n)
def matrixDimension (b : ℝ) (n : ℕ) : ℕ := ⌈Real.exp (b * n)⌉₊
def inputQubits (K N n : ℕ) : ℝ := log2 (inputDimension K N n : ℝ)

theorem input_qubits_formula {K N : ℕ} (n : ℕ) (hK : 0 < K) (hN : 0 < N) :
    inputQubits K N n = 1 + (n : ℝ) * log2 N + 2 * (n : ℝ) * log2 K := by
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold inputQubits inputDimension log2
  push_cast
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hKr),
    Real.log_mul (by norm_num) (pow_ne_zero _ hNr), Real.log_pow, Real.log_pow]
  push_cast
  field_simp

theorem matrixDimension_pos (b : ℝ) (n : ℕ) : 0 < matrixDimension b n := by
  apply Nat.ceil_pos.mpr
  exact Real.exp_pos _

/-- The exact ceiling contributes at most exp(-bn) to its logarithm. -/
theorem log_matrixDimension_error (b : ℝ) (n : ℕ) :
    0 ≤ Real.log (matrixDimension b n : ℝ) - b * n ∧
      Real.log (matrixDimension b n : ℝ) - b * n ≤ Real.exp (-(b * n)) := by
  have hexp : 0 < Real.exp (b * n) := Real.exp_pos _
  have hN : 0 < (matrixDimension b n : ℝ) := by
    exact_mod_cast matrixDimension_pos b n
  have hlo : Real.exp (b * n) ≤ (matrixDimension b n : ℝ) := Nat.le_ceil _
  have hhi : (matrixDimension b n : ℝ) ≤ Real.exp (b * n) + 1 :=
    (Nat.ceil_lt_add_one hexp.le).le
  have hloglo := Real.log_le_log hexp hlo
  rw [Real.log_exp] at hloglo
  have hloghi := Real.log_le_log hN hhi
  have hsplit : Real.exp (b * n) + 1 =
      Real.exp (b * n) * (1 + Real.exp (-(b * n))) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    simp
  rw [hsplit, Real.log_mul hexp.ne' (by positivity), Real.log_exp] at hloghi
  have hsmall := Real.log_le_sub_one_of_pos
      (show 0 < 1 + Real.exp (-(b * n)) by positivity)
  constructor <;> linarith

theorem weighted_log_ceiling_error_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (Real.log (matrixDimension b n : ℝ) - b * n)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(b * n))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
      tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n)
      (log_matrixDimension_error b n).1)
    (fun n => mul_le_mul_of_nonneg_left (log_matrixDimension_error b n).2
      (Nat.cast_nonneg n)) hexp

/-- The input-size equation in the manuscript, including the o(1) ceiling
correction. Written as a remainder tending to zero to avoid informal notation. -/
theorem input_size_remainder_tendsto {K : ℕ} (hK : 0 < K) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => inputQubits K (matrixDimension b n) n -
      (b / Real.log 2 * (n : ℝ) ^ 2 + 2 * (n : ℝ) * log2 K + 1))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) *
      (Real.log (matrixDimension b n : ℝ) - b * n)) / Real.log 2) atTop (𝓝 0) := by
    simpa only [zero_div] using
      (weighted_log_ceiling_error_tendsto hb).div_const (Real.log 2)
  convert h using 1
  ext n
  rw [input_qubits_formula n hK (matrixDimension_pos b n)]
  unfold log2
  ring

end Nonadditivity.Dimensions
