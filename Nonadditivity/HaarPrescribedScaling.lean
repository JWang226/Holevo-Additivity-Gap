/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPrescribedConsequences

/-! # Output-size scaling of the actual prescribed-dimension channels

The output size is exactly the block length times `log₂ K`. The genuine
Holevo gap has the dimension upper bound and the proved construction lower
bound, giving linear growth and the manuscript's normalized lower limit.
-/

noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open ActualConsequences Filter Topology

/-- The exact output-qubit count, beyond the construction threshold. -/
theorem prescribedFamily_output_qubits {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    Scalar.log2 (Fintype.card (prescribedFamily hK n).Output) =
      (n : ℝ) * Scalar.log2 K := by
  rw [(prescribedFamily_spec hK hn).2.1]
  unfold Scalar.log2
  rw [Nat.cast_pow, Real.log_pow]
  ring

theorem log2_ge_one {K : ℕ} (hK : 2 ≤ K) : 1 ≤ Scalar.log2 K := by
  unfold Scalar.log2
  apply (le_div_iff₀ Scalar.log_two_pos).2
  simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hK : (2 : ℝ) ≤ K)

/-- Two actual uses carry at most twice the output-qubit count. -/
theorem prescribedFamily_chiTwo_upper {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    (prescribedFamily hK n).chiTwo ≤ 2 * (n : ℝ) * Scalar.log2 K := by
  have h := (prescribedFamily hK n).half_chiTwo_le_regularizedHolevo.trans
    (prescribedFamily hK n).regularizedHolevo_le_log_output_dim
  rw [prescribedFamily_output_qubits hK hn] at h
  linarith

/-- Nonnegativity of single-use Holevo information supplies the matching
linear dimension upper bound for the actual additive gap. -/
theorem prescribedFamily_gap_upper {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    (prescribedFamily hK n).gap ≤ 2 * (n : ℝ) * Scalar.log2 K := by
  have h := prescribedFamily_chiTwo_upper hK hn
  have hchi := (prescribedFamily hK n).chi_nonneg
  unfold FiniteQuantumChannel.gap
  linarith

theorem prescribedFamily_gap_upper_eventually {K : ℕ} (hK : 2 ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      (prescribedFamily hK n).gap ≤ (n : ℝ) * (2 * Scalar.log2 K) := by
  filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
  convert prescribedFamily_gap_upper hK hn using 1
  ring

/-- Explicit eventual linear bounds: the lower slope is positive whenever
the manuscript's `δ_K` is positive. -/
theorem prescribedFamily_gap_linear_bounds {K : ℕ} (hK : 2 ≤ K)
    (hδ : 0 < Scalar.deltaK K) :
    ∀ᶠ n : ℕ in atTop,
      (Scalar.deltaK K / 2) * n ≤ (prescribedFamily hK n).gap ∧
      (prescribedFamily hK n).gap ≤ (2 * Scalar.log2 K) * n := by
  have hl := Asymptotics.eventually_linear_gap
    (fun n => (prescribedFamily hK n).gap) hδ
    (prescribedFamily_gap_lower_eventually hK)
  filter_upwards [hl, prescribedFamily_gap_upper_eventually hK] with n hn hu
  exact ⟨hn, by simpa only [mul_comm] using hu⟩

/-- The actual gap per block has the manuscript's lower asymptotic slope. -/
theorem prescribedFamily_gap_liminf {K : ℕ} (hK : 2 ≤ K) :
    Scalar.deltaK K ≤ liminf (fun n : ℕ => (prescribedFamily hK n).gap / n) atTop :=
  Asymptotics.normalized_gap_liminf (fun n => (prescribedFamily hK n).gap)
    (prescribedFamily_gap_lower_eventually hK) (prescribedFamily_gap_upper_eventually hK)

/-- The guaranteed fraction of the actual output size. The denominator is
the logarithm of the channel's genuine output dimension. -/
theorem prescribedFamily_output_normalized_gap_liminf {K : ℕ} (hK : 2 ≤ K) :
    Scalar.deltaK K / Scalar.log2 K ≤
      liminf (fun n : ℕ => (prescribedFamily hK n).gap /
        Scalar.log2 (Fintype.card (prescribedFamily hK n).Output)) atTop := by
  have h := Asymptotics.output_normalized_gap_liminf
    (fun n => (prescribedFamily hK n).gap) (log2_ge_one hK)
    (prescribedFamily_gap_lower_eventually hK) (prescribedFamily_gap_upper_eventually hK)
  apply h.trans_eq
  apply liminf_congr
  filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
  rw [prescribedFamily_output_qubits hK hn]

end Nonadditivity.HaarPrescribedDimension
