/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPrescribedScaling

/-! # The real-valued lower limit of the prescribed channel's two-use ratio -/

noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open ActualConsequences Filter Topology

theorem prescribedFamily_ratio_upper_eventually {K : ℕ} (hK : 2 ≤ K) :
    ∀ᶠ n : ℕ in atTop, (prescribedFamily hK n).twoUseRatio ≤
      (K : ℝ) * Scalar.log2 K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlog : 0 ≤ Scalar.log2 K := (log2_ge_one hK).trans' (by norm_num)
  filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
  have hp := (prescribedFamily_spec hK hn).2.2.1
  have hlo := (div_le_iff₀ hKr).mp (prescribedFamily_chi_lower hK hn)
  have hhi := prescribedFamily_chiTwo_upper hK hn
  have hm := mul_le_mul_of_nonneg_right hlo hlog
  have hc : 0 ≤ (prescribedFamily hK n).chi * (K : ℝ) * Scalar.log2 K :=
    mul_nonneg (mul_nonneg hp.le hKr.le) hlog
  unfold FiniteQuantumChannel.twoUseRatio
  apply (div_le_iff₀ (by positivity : 0 < 2 * (prescribedFamily hK n).chi)).2
  nlinarith

/-- The manuscript's ratio lower limit, with boundedness proved for the
actual channel family rather than assumed for a scalar surrogate. -/
theorem prescribedFamily_ratio_liminf {K : ℕ} (hK : 2 ≤ K) :
    Scalar.log2 K / (2 * (K : ℝ) * Scalar.aK K) ≤
      liminf (fun n => (prescribedFamily hK n).twoUseRatio) atTop := by
  have hl : ∀ᶠ n : ℕ in atTop, 0 ≤ (prescribedFamily hK n).twoUseRatio := by
    filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
    exact div_nonneg (prescribedFamily hK n).chiTwo_nonneg
      (mul_nonneg (by norm_num) (prescribedFamily_spec hK hn).2.2.1.le)
  apply (le_liminf_iff'
    (isBoundedUnder_of_eventually_le (prescribedFamily_ratio_upper_eventually hK)).isCoboundedUnder_ge
    (isBoundedUnder_of_eventually_ge hl)).2
  intro R hR
  exact prescribedFamily_ratio_eventually hK hR

theorem prescribedFamily_ratio_liminf_manuscript {K : ℕ} (hK : 2 ≤ K) :
    1 + Scalar.deltaK K / (2 * Scalar.aK K) ≤
      liminf (fun n => (prescribedFamily hK n).twoUseRatio) atTop ∧
    Real.log (K : ℝ) / 18 ≤ 1 + Scalar.deltaK K / (2 * Scalar.aK K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  rw [Scalar.ratio_identity hKr]
  exact ⟨prescribedFamily_ratio_liminf hK,
    Scalar.ratio_lower (by exact_mod_cast (show 1 < K by omega))⟩

end Nonadditivity.HaarPrescribedDimension
