/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PrescribedCostDimensions

/-! # Logarithmic input-cost scale of the actual growing family -/
noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology Asymptotics

def inputQubits (K : ℕ) : ℝ := Scalar.log2 (Fintype.card (growingFamily K).Input)

theorem inputQubits_div_sq_tendsto :
    Tendsto (fun K : ℕ => inputQubits K/(K:ℝ)^2) atTop (𝓝 (280/Real.log 2)) :=
  growingFamily_input_qubits_div_sq_tendsto

theorem inputQubits_pos_eventually : ∀ᶠ K : ℕ in atTop, 0 < inputQubits K := by
  have hc : (0:ℝ)<280/Real.log 2 := by positivity
  have hh := inputQubits_div_sq_tendsto.eventually (lt_mem_nhds hc)
  filter_upwards [hh,eventually_ge_atTop 2] with K h hK
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  simpa using (lt_div_iff₀ (sq_pos_of_pos hk)).mp h

/-- Taking the logarithm of the actual input-qubit count gives twice ln K
at leading order, because that count is asymptotic to a positive multiple of K². -/
theorem log_inputQubits_div_log_tendsto :
    Tendsto (fun K : ℕ => Real.log (inputQubits K)/Real.log K) atTop (𝓝 2) := by
  have hc : (0:ℝ)<280/Real.log 2 := by positivity
  have hlogK : Tendsto (fun K : ℕ => Real.log (K:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (inputQubits_div_sq_tendsto.log hc.ne').div_atTop hlogK
  have h' : Tendsto (fun K : ℕ =>
      Real.log (inputQubits K/(K:ℝ)^2)/Real.log K + 2) atTop (𝓝 2) := by
    simpa using h.add_const 2
  apply h'.congr'
  filter_upwards [inputQubits_pos_eventually,eventually_ge_atTop 2] with K hq hK
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hl := (log_nat_pos hK).ne'
  rw [Real.log_div hq.ne' (pow_ne_zero _ hk.ne'),Real.log_pow]
  field_simp
  ring

/-- The logarithm is in bits, as in the manuscript's information quantities. -/
theorem log2_inputQubits_div_log_tendsto :
    Tendsto (fun K : ℕ => Scalar.log2 (inputQubits K)/Real.log K)
      atTop (𝓝 (2/Real.log 2)) := by
  convert log_inputQubits_div_log_tendsto.div_const (Real.log 2) using 1
  funext K
  unfold Scalar.log2
  ring

theorem sqrt_inputLog_ratio_tendsto :
    Tendsto (fun K : ℕ => Real.sqrt (Scalar.log2 (inputQubits K)/Real.log K))
      atTop (𝓝 (Real.sqrt (2/Real.log 2))) :=
  log2_inputQubits_div_log_tendsto.sqrt

end Nonadditivity.PrescribedCost
