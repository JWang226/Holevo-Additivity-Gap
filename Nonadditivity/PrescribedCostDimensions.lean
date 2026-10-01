/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PrescribedCostScalars

/-! # Exact quadratic input-qubit cost along the growing-parameter separation -/

noncomputable section
namespace Nonadditivity.PrescribedCost
open Filter Topology Asymptotics
open ActualConsequences HaarPrescribedDimension StructuredHaarConsequences

def scalarInputQubits (K : ℕ) : ℝ :=
  Dimensions.inputQubits K (Dimensions.matrixDimension
    (Quantitative.dimensionExponent (Real.log K)) (blockLength K)) (blockLength K)

theorem log_div_nat_tendsto_zero :
    Tendsto (fun K : ℕ => Real.log K / K) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  simpa only [Real.rpow_one] using h.comp tendsto_natCast_atTop_atTop

theorem normalized_dimension_leading_tendsto :
    Tendsto (fun K : ℕ => Quantitative.dimensionExponent (Real.log K) *
      (blockLength K : ℝ)^2 / (K:ℝ)^2) atTop (𝓝 280) := by
  have h := ((normalized_blockLength_tendsto_one.pow 2).const_mul 280).add
    ((blockLength_div_tendsto_zero.pow 2).const_mul 80)
  have h' : Tendsto (fun K : ℕ =>
      280*((blockLength K:ℝ)*Real.sqrt (Real.log K)/K)^2 +
        80*((blockLength K:ℝ)/K)^2) atTop (𝓝 280) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with K hK
  simp only [Quantitative.dimensionExponent, div_pow, mul_pow,
    Real.sq_sqrt (log_nat_pos hK).le]
  ring

theorem normalized_ceiling_error_tendsto :
    Tendsto (fun K : ℕ => ((blockLength K:ℝ) *
      (Real.log (Dimensions.matrixDimension (Quantitative.dimensionExponent (Real.log K))
        (blockLength K) : ℝ) - Quantitative.dimensionExponent (Real.log K)*(blockLength K))) /
        (K:ℝ)^2) atTop (𝓝 0) := by
  have hupper : Tendsto (fun K : ℕ => (blockLength K:ℝ)/(K:ℝ)^2) atTop (𝓝 0) := by
    have h := blockLength_div_tendsto_zero.div_atTop tendsto_natCast_atTop_atTop
    simpa only [div_div, ← pow_two] using h
  apply squeeze_zero' (Eventually.of_forall (fun K =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Dimensions.log_matrixDimension_error _ _).1) (sq_nonneg _))) _ hupper
  filter_upwards [eventually_ge_atTop 2] with K hK
  have hb : 0 ≤ Quantitative.dimensionExponent (Real.log K) := by
    unfold Quantitative.dimensionExponent
    have hlog := (log_nat_pos hK).le
    positivity
  have he := (Dimensions.log_matrixDimension_error
    (Quantitative.dimensionExponent (Real.log K)) (blockLength K)).2
  have he1 : Real.exp (-(Quantitative.dimensionExponent (Real.log K)*(blockLength K))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hb (Nat.cast_nonneg _)))
  exact div_le_div_of_nonneg_right (by nlinarith [show (0:ℝ) ≤ blockLength K from Nat.cast_nonneg _]) (sq_nonneg (K:ℝ))

/-- The exact rounded prescribed input dimension has the manuscript's
leading qubit cost `(280/log 2)*K^2`. -/
theorem scalarInputQubits_div_sq_tendsto :
    Tendsto (fun K : ℕ => scalarInputQubits K/(K:ℝ)^2)
      atTop (𝓝 (280/Real.log 2)) := by
  have hconst : Tendsto (fun K : ℕ => 1/(K:ℝ)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, one_div, inv_pow, zero_pow (by decide : 2 ≠ 0)] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun K : ℕ => (K:ℝ)) atTop atTop)).pow 2
  have hlinear : Tendsto (fun K : ℕ =>
      (2/Real.log 2)*((blockLength K:ℝ)/K)*(Real.log K/K)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (blockLength_div_tendsto_zero.const_mul (2/Real.log 2)).mul log_div_nat_tendsto_zero
  have h := ((hconst.add (normalized_dimension_leading_tendsto.div_const (Real.log 2))).add
    hlinear).add (normalized_ceiling_error_tendsto.div_const (Real.log 2))
  have h' : Tendsto (fun K : ℕ => 1/(K:ℝ)^2 +
      (Quantitative.dimensionExponent (Real.log K)*(blockLength K:ℝ)^2/(K:ℝ)^2)/Real.log 2 +
      (2/Real.log 2)*((blockLength K:ℝ)/K)*(Real.log K/K) +
      (((blockLength K:ℝ)*(Real.log (Dimensions.matrixDimension
        (Quantitative.dimensionExponent (Real.log K)) (blockLength K):ℝ) -
        Quantitative.dimensionExponent (Real.log K)*(blockLength K)))/(K:ℝ)^2)/Real.log 2)
      atTop (𝓝 (280/Real.log 2)) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with K hK
  unfold scalarInputQubits
  rw [Dimensions.input_qubits_formula (blockLength K) (by omega)
    (Dimensions.matrixDimension_pos _ _)]
  unfold Scalar.log2
  ring

/-- The actual prescribed channel at the growing block length. Initial
indices use the threshold built into `prescribedFamily`; eventually none do. -/
def growingFamily (K : ℕ) : FiniteQuantumChannel :=
  if hK : 2 ≤ K then prescribedFamily hK (blockLength K)
  else prescribedFamily (K := 2) (by decide) 1

theorem growingFamily_input_qubits_eventually :
    ∀ᶠ K : ℕ in atTop,
      Scalar.log2 (Fintype.card (growingFamily K).Input) = scalarInputQubits K := by
  filter_upwards [threshold_le_blockLength_eventually, eventually_ge_atTop 2] with K hn hK
  rw [growingFamily, dif_pos hK, (prescribedFamily_spec hK hn).1]
  rfl

/-- The input cost statement concerns the actual selected channels, not a
dimension sequence disconnected from the quantum construction. -/
theorem growingFamily_input_qubits_div_sq_tendsto :
    Tendsto (fun K : ℕ => Scalar.log2 (Fintype.card (growingFamily K).Input)/(K:ℝ)^2)
      atTop (𝓝 (280/Real.log 2)) := by
  apply scalarInputQubits_div_sq_tendsto.congr'
  filter_upwards [growingFamily_input_qubits_eventually] with K hK
  rw [hK]

end Nonadditivity.PrescribedCost
