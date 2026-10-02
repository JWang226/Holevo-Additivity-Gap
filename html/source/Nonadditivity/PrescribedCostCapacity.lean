/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PrescribedCostScaling

/-! # Two-use and operational capacity growth in terms of actual input cost -/
noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology Asymptotics ActualConsequences

/-- The manuscript's Ω(sqrt(log(input qubits))) two-use information bound,
with a positive explicit constant. Operational capacity satisfies it too. -/
theorem growingFamily_two_use_input_cost_lower :
    ∀ᶠ K : ℕ in atTop,
      1/(8*Real.log 2*inputLogScale) ≤
        ((growingFamily K).chiTwo/2)/Real.sqrt (Scalar.log2 (inputQubits K)) ∧
      1/(8*Real.log 2*inputLogScale) ≤
        (growingFamily K).classicalCapacity/Real.sqrt (Scalar.log2 (inputQubits K)) := by
  have hn := normalized_blockLength_tendsto_one.eventually
    (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  filter_upwards [hn,input_sqrt_ratio_bounds,growingFamily_bounds_eventually,eventually_ge_atTop 2]
    with K hn hr hb hK
  have hs : 0<Real.sqrt (Real.log K) := Real.sqrt_pos.mpr (log_nat_pos hK)
  have hL := inputLogScale_pos
  have hl := Scalar.log_two_pos
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hq : 0<Real.sqrt (Scalar.log2 (inputQubits K)) := by
    have h := (lt_div_iff₀ hs).mp ((half_pos hL).trans_le hr.1)
    simpa using h
  have hroot := (div_le_iff₀ hs).mp hr.2
  have hstep : (1/(8*Real.log 2*inputLogScale))*Real.sqrt (Scalar.log2 (inputQubits K)) ≤
      Real.sqrt (Real.log K)/(4*Real.log 2) := by
    have h := mul_le_mul_of_nonneg_left hroot
      (by positivity : 0≤1/(8*Real.log 2*inputLogScale))
    convert h using 1
    field_simp
    ring
  have hsep : Real.sqrt (Real.log K)/(4*Real.log 2) ≤ separationLower K := by
    calc
      _ = (1/2:ℝ)*Real.sqrt (Real.log K)/(2*Real.log 2) := by ring
      _ ≤ ((blockLength K:ℝ)*Real.sqrt (Real.log K)/K)*
          Real.sqrt (Real.log K)/(2*Real.log 2) := by gcongr
      _ = separationLower K := by
        unfold separationLower
        have hsq := Real.sq_sqrt (log_nat_pos hK).le
        field_simp
        nlinarith
  have ht := (le_div_iff₀ hq).mpr ((hstep.trans hsep).trans hb.2.2)
  exact ⟨ht,ht.trans (div_le_div_of_nonneg_right
    (growingFamily K).half_chiTwo_le_classicalCapacity hq.le)⟩

end Nonadditivity.PrescribedCost
