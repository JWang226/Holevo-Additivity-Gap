/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PrescribedCostInformation
import Nonadditivity.PrescribedCostLogarithms

/-! # Matching information bounds in terms of the actual input-qubit cost -/
noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology Asymptotics ActualConsequences

theorem correction_sqrt_log_tendsto_zero :
    Tendsto (fun K : ℕ => finiteSizeCorrection (blockLength K)*Real.sqrt (Real.log K))
      atTop (𝓝 0) := by
  have hb := blockLength_tendsto_atTop.eventually (eventually_ge_atTop 2)
  apply squeeze_zero' _ _ (by simpa using
    sqrt_log_div_blockLength_tendsto_zero.const_mul (16/Real.log 2))
  · filter_upwards [hb] with K hn
    exact mul_nonneg (finiteSizeCorrection_nonneg hn) (Real.sqrt_nonneg _)
  · filter_upwards [hb] with K hn
    have h := mul_le_mul_of_nonneg_right (finiteSizeCorrection_le_inverse hn)
      (Real.sqrt_nonneg (Real.log K))
    convert h using 1
    ring

theorem growingFamily_chi_scaled_bounds :
    ∀ᶠ K : ℕ in atTop,
      1 ≤ (growingFamily K).chi * Real.sqrt (Real.log K) ∧
      (growingFamily K).chi * Real.sqrt (Real.log K) ≤ 9/Real.log 2+1 := by
  have htwo : Tendsto (fun K : ℕ => 2*((blockLength K:ℝ)*Real.sqrt (Real.log K)/K))
      atTop (𝓝 2) := by simpa using normalized_blockLength_tendsto_one.const_mul 2
  have hlo := htwo.eventually (lt_mem_nhds (by norm_num : (1:ℝ)<2))
  have hupper : Tendsto (fun K : ℕ =>
      (9/Real.log 2)*((blockLength K:ℝ)*Real.sqrt (Real.log K)/K) +
        finiteSizeCorrection (blockLength K)*Real.sqrt (Real.log K)/2)
      atTop (𝓝 (9/Real.log 2)) := by
    simpa using (normalized_blockLength_tendsto_one.const_mul (9/Real.log 2)).add
      (correction_sqrt_log_tendsto_zero.div_const 2)
  have hu := hupper.eventually (gt_mem_nhds (by linarith : 9/Real.log 2<9/Real.log 2+1))
  filter_upwards [growingFamily_bounds_eventually,hlo,hu,eventually_ge_atTop 2]
    with K hs hl hu hK
  have hKr : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hsqrt := Real.sqrt_nonneg (Real.log K)
  have hlow := mul_le_mul_of_nonneg_right hs.1 hsqrt
  have hhigh := mul_le_mul_of_nonneg_right hs.2.1 hsqrt
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Scalar.aK_le hKr)
      (Nat.cast_nonneg (blockLength K): (0:ℝ)≤blockLength K)) hsqrt
  have hterm' : (blockLength K:ℝ)*Scalar.aK K*Real.sqrt (Real.log K) ≤
      (9/Real.log 2)*((blockLength K:ℝ)*Real.sqrt (Real.log K)/K) := by
    convert hterm using 1
    ring
  have hlow' : 2*((blockLength K:ℝ)*Real.sqrt (Real.log K)/K) ≤
      (growingFamily K).chi*Real.sqrt (Real.log K) := by
    convert hlow using 1
    ring
  constructor
  · linarith
  · nlinarith

def inputLogScale : ℝ := Real.sqrt (2/Real.log 2)

theorem inputLogScale_pos : 0 < inputLogScale := by
  unfold inputLogScale
  exact Real.sqrt_pos.mpr (by positivity)

theorem input_sqrt_ratio_bounds :
    ∀ᶠ K : ℕ in atTop,
      inputLogScale/2 ≤ Real.sqrt (Scalar.log2 (inputQubits K))/Real.sqrt (Real.log K) ∧
      Real.sqrt (Scalar.log2 (inputQubits K))/Real.sqrt (Real.log K) ≤ 2*inputLogScale := by
  have ht := sqrt_inputLog_ratio_tendsto
  have hlo := ht.eventually (lt_mem_nhds (show inputLogScale/2 < inputLogScale by
    linarith [inputLogScale_pos]))
  have hhi := ht.eventually (gt_mem_nhds (show inputLogScale < 2*inputLogScale by
    linarith [inputLogScale_pos]))
  filter_upwards [hlo,hhi,eventually_ge_atTop 2] with K hl hh hK
  rw [Real.sqrt_div' _ (log_nat_pos hK).le] at hl hh
  exact ⟨hl.le,hh.le⟩

/-- An explicit two-sided Θ bound for χ in the reciprocal square root of
log(input qubits), using the same channel family with quadratic input cost. -/
theorem growingFamily_chi_input_cost_bounds :
    ∀ᶠ K : ℕ in atTop,
      inputLogScale/2 ≤ (growingFamily K).chi*Real.sqrt (Scalar.log2 (inputQubits K)) ∧
      (growingFamily K).chi*Real.sqrt (Scalar.log2 (inputQubits K)) ≤
        (9/Real.log 2+1)*(2*inputLogScale) := by
  filter_upwards [growingFamily_chi_scaled_bounds,input_sqrt_ratio_bounds,eventually_ge_atTop 2]
    with K hc hr hK
  have hsqrt : 0<Real.sqrt (Real.log K) := Real.sqrt_pos.mpr (log_nat_pos hK)
  have he : ((growingFamily K).chi*Real.sqrt (Real.log K))*
      (Real.sqrt (Scalar.log2 (inputQubits K))/Real.sqrt (Real.log K)) =
      (growingFamily K).chi*Real.sqrt (Scalar.log2 (inputQubits K)) := by field_simp
  have hn := mul_nonneg (growingFamily K).chi_nonneg hsqrt.le
  have hlo := mul_le_mul hc.1 hr.1 (div_nonneg inputLogScale_pos.le (by norm_num)) hn
  have hhi := mul_le_mul hc.2 hr.2 (by positivity) (by positivity)
  rw [he] at hlo hhi
  exact ⟨by simpa using hlo,hhi⟩

end Nonadditivity.PrescribedCost
