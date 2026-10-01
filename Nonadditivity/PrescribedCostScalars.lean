/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPrescribedScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Rounded growing-block lengths and the prescribed construction threshold -/

noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology
open Asymptotics

theorem sqrt_log_div_nat_tendsto_zero :
    Tendsto (fun K : ℕ => Real.sqrt (Real.log K) / K) atTop (𝓝 0) := by
  have h : Tendsto (fun K : ℕ => 1 / Real.sqrt K) atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun K => by positivity)) _
    h
  filter_upwards [eventually_ge_atTop 2] with K hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0<K by omega)
  have hs := Real.sqrt_le_sqrt (Real.log_le_self hKr.le)
  have hsq := Real.mul_self_sqrt hKr.le
  apply (div_le_div_iff₀ hKr (Real.sqrt_pos.mpr hKr)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (K:ℝ))]

theorem normalized_blockLength_tendsto_one :
    Tendsto (fun K : ℕ => (blockLength K : ℝ) * Real.sqrt (Real.log K) / K)
      atTop (𝓝 1) := by
  have hu : Tendsto (fun K : ℕ => 1 + Real.sqrt (Real.log K) / K) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add sqrt_log_div_nat_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 2] with K hK
    have hk : (0 : ℝ) < K := by exact_mod_cast (show 0<K by omega)
    have hs := Real.sqrt_pos.mpr (log_nat_pos hK)
    have hc := (div_le_iff₀ hs).mp (Nat.le_ceil ((K:ℝ)/Real.sqrt (Real.log K)))
    exact (le_div_iff₀ hk).mpr (by simpa using hc)
  · filter_upwards [eventually_ge_atTop 2] with K hK
    have hk : (0 : ℝ) < K := by exact_mod_cast (show 0<K by omega)
    have hs := Real.sqrt_pos.mpr (log_nat_pos hK)
    have hc := (Nat.ceil_lt_add_one (div_nonneg hk.le hs.le)).le
    have hm := mul_le_mul_of_nonneg_right hc hs.le
    change (blockLength K : ℝ) * Real.sqrt (Real.log K) / K ≤ _
    apply (div_le_iff₀ hk).mpr
    have hid : (((K:ℝ)/Real.sqrt (Real.log K))+1)*Real.sqrt (Real.log K) =
        (K:ℝ)+Real.sqrt (Real.log K) := by field_simp
    rw [hid] at hm
    convert hm using 1
    field_simp

theorem log_pow_div_sqrt_tendsto_zero (m : ℕ) :
    Tendsto (fun K : ℕ => (Real.log K)^m / Real.sqrt K) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (m:ℝ)
    (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using h

theorem threshold_div_sqrt_tendsto_zero :
    Tendsto (fun K : ℕ => (Quantitative.n₀ K : ℝ) / Real.sqrt K) atTop (𝓝 0) := by
  have hu : Tendsto (fun K : ℕ =>
      (256*(1+Real.log K)^2+1)/Real.sqrt K) atTop (𝓝 0) := by
    have h := ((log_pow_div_sqrt_tendsto_zero 0).const_mul 257).add
      (((log_pow_div_sqrt_tendsto_zero 1).const_mul 512).add
        ((log_pow_div_sqrt_tendsto_zero 2).const_mul 256))
    convert h using 1
    · funext K
      simp only [pow_zero, pow_one]
      ring
    · norm_num
  apply squeeze_zero (fun K => by positivity) (fun K => ?_) hu
  exact div_le_div_of_nonneg_right
    (Nat.ceil_lt_add_one (show (0:ℝ)≤256*(1+Real.log K)^2 by positivity)).le
    (Real.sqrt_nonneg _)

/-- The manuscript's unmodified rounded block length eventually exceeds the
prescribed threshold; the initial maximum in the actual family disappears. -/
theorem threshold_le_blockLength_eventually :
    ∀ᶠ K : ℕ in atTop, Quantitative.n₀ K ≤ blockLength K := by
  have ht := threshold_div_sqrt_tendsto_zero.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))
  filter_upwards [ht, eventually_ge_atTop 2] with K h hK
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hs := (div_lt_iff₀ (Real.sqrt_pos.mpr hk)).mp h
  have hb := sqrt_le_blockLength hK
  exact_mod_cast (show (Quantitative.n₀ K : ℝ) ≤ (blockLength K : ℝ) by linarith)

end Nonadditivity.PrescribedCost
