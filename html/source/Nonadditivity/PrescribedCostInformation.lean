/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PrescribedCostDimensions
import Nonadditivity.OperationalCodingTheorem

/-! # Information and operational capacity along the explicit-cost family -/
noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology Asymptotics ActualConsequences HaarPrescribedDimension
  StructuredHaarConsequences

theorem growingFamily_bounds_eventually :
    ∀ᶠ K : ℕ in atTop,
      2*(blockLength K:ℝ)/K ≤ (growingFamily K).chi ∧
      (growingFamily K).chi ≤ (blockLength K:ℝ)*Scalar.aK K +
        finiteSizeCorrection (blockLength K)/2 ∧
      separationLower K ≤ (growingFamily K).chiTwo/2 := by
  filter_upwards [threshold_le_blockLength_eventually,eventually_ge_atTop 2] with K hn hK
  rw [growingFamily,dif_pos hK]
  have hs := prescribedFamily_spec hK hn
  refine ⟨prescribedFamily_chi_lower hK hn, ?_, ?_⟩
  · rw [← correction_eq]
    linarith [hs.2.2.2.1]
  · have hh := hs.2.2.2.2.1
    have hd := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤2)
    convert hd using 1
    unfold separationLower Scalar.log2
    ring

theorem growingFamily_vanishing_diverging :
    Tendsto (fun K => (growingFamily K).chi) atTop (𝓝 0) ∧
    Tendsto (fun K => (growingFamily K).chiTwo/2) atTop atTop ∧
    Tendsto (fun K => (growingFamily K).classicalCapacity) atTop atTop := by
  have htwo : Tendsto (fun K => (growingFamily K).chiTwo/2) atTop atTop :=
    tendsto_atTop_mono' atTop (growingFamily_bounds_eventually.mono (fun _ h => h.2.2))
      separationLower_tendsto_atTop
  refine ⟨?_,htwo,tendsto_atTop_mono (fun K =>
    (growingFamily K).half_chiTwo_le_classicalCapacity) htwo⟩
  apply squeeze_zero' (g := fun K => separationUpper K+finiteSizeCorrection (blockLength K)/2)
    (Eventually.of_forall (fun K => (growingFamily K).chi_nonneg))
  · filter_upwards [growingFamily_bounds_eventually,eventually_ge_atTop 2] with K hs hK
    have hKr : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
    have ha := mul_le_mul_of_nonneg_left (Scalar.aK_le hKr)
      (Nat.cast_nonneg (blockLength K): (0:ℝ)≤blockLength K)
    have he : (blockLength K:ℝ)*(9/((K:ℝ)*Real.log 2)) ≤ separationUpper K := by
      unfold separationUpper
      have : (0:ℝ)≤1/K := by positivity
      convert le_add_of_nonneg_right (a := 9*(blockLength K:ℝ)/(K*Real.log 2)) this using 1
      ring
    exact hs.2.1.trans (by linarith [ha.trans he])
  · simpa using separationUpper_tendsto_zero.add
      (finiteSizeCorrection_blockLength_tendsto_zero.div_const 2)

/-- The ceiling correction is negligible even at the inverse-square-root
logarithmic scale relevant to the information estimate. -/
theorem sqrt_log_div_blockLength_tendsto_zero :
    Tendsto (fun K : ℕ => Real.sqrt (Real.log K)/(blockLength K:ℝ)) atTop (𝓝 0) := by
  have h := log_div_nat_tendsto_zero.div normalized_blockLength_tendsto_one (by norm_num)
  have h' : Tendsto (fun K : ℕ => (Real.log K/K)/
      ((blockLength K:ℝ)*Real.sqrt (Real.log K)/K)) atTop (𝓝 0) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with K hK
  have hKr : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hsr := Real.sqrt_pos.mpr (log_nat_pos hK)
  have hnr : (0:ℝ)<blockLength K := by exact_mod_cast blockLength_pos hK
  field_simp
  exact (Real.sq_sqrt (log_nat_pos hK).le).symm

theorem finiteSizeCorrection_le_inverse {n : ℕ} (hn : 2≤n) :
    finiteSizeCorrection n ≤ (16/Real.log 2)/(n:ℝ) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hd : 0<(n:ℝ)-1 := by linarith
  have hr : 0<((n:ℝ)+1)/((n:ℝ)-1) := by positivity
  have hl := Real.log_le_sub_one_of_pos hr
  have he : ((n:ℝ)+1)/((n:ℝ)-1)-1=2/((n:ℝ)-1) := by field_simp; ring
  rw [he] at hl
  unfold finiteSizeCorrection
  calc
    _ ≤ 4*(2/((n:ℝ)-1))/Real.log 2 := by gcongr
    _ ≤ 4*(4/(n:ℝ))/Real.log 2 := by
      have hb : 2/((n:ℝ)-1) ≤ 4/(n:ℝ) := by
        apply (div_le_div_iff₀ hd (by linarith : (0:ℝ)<n)).2
        nlinarith
      gcongr
    _ = (16/Real.log 2)/(n:ℝ) := by ring

end Nonadditivity.PrescribedCost
