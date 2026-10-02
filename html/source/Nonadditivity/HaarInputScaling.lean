/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPrescribedScaling

/-! # Matching square-root input-qubit scaling of the actual Holevo gap -/
noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open Filter Topology ActualConsequences

def inputLeading (K : ℕ) : ℝ := Quantitative.dimensionExponent (Real.log K)/Real.log 2

theorem inputLeading_pos {K : ℕ} (hK : 2≤K) : 0 < inputLeading K := by
  have hl : 0≤Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤K by omega))
  unfold inputLeading Quantitative.dimensionExponent
  positivity

theorem prescribed_input_div_sq_tendsto {K : ℕ} (hK : 2≤K) :
    Tendsto (fun n : ℕ => Scalar.log2 (Fintype.card (prescribedFamily hK n).Input)/(n:ℝ)^2)
      atTop (𝓝 (inputLeading K)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he := (prescribedFamily_input_size_remainder_tendsto hK).mul (hi.pow 2)
  have hh := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => inputLeading K)
    atTop (𝓝 (inputLeading K))).add (hi.const_mul (2*Scalar.log2 K))).add
      (hi.pow 2)).add he
  simp only [mul_zero,add_zero,zero_pow (by decide : 2≠0)] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold inputLeading
  field_simp
  ring

theorem prescribed_sqrt_input_div_tendsto {K : ℕ} (hK : 2≤K) :
    Tendsto (fun n : ℕ => Real.sqrt (Scalar.log2 (Fintype.card (prescribedFamily hK n).Input))/(n:ℝ))
      atTop (𝓝 (Real.sqrt (inputLeading K))) := by
  apply (prescribed_input_div_sq_tendsto hK).sqrt.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg n)]

/-- The stated Θ(sqrt(input qubits)) gap with positive explicit comparison
constants and the actual channel dimension inside the square root. -/
theorem prescribed_gap_sqrt_input_bounds {K : ℕ} (hK : 2≤K)
    (hδ : 0<Scalar.deltaK K) :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,
      c*Real.sqrt (Scalar.log2 (Fintype.card (prescribedFamily hK n).Input)) ≤
        (prescribedFamily hK n).gap ∧
      (prescribedFamily hK n).gap ≤
        C*Real.sqrt (Scalar.log2 (Fintype.card (prescribedFamily hK n).Input)) := by
  let s := Real.sqrt (inputLeading K)
  have hs : 0<s := Real.sqrt_pos.mpr (inputLeading_pos hK)
  have hlog : 0<Scalar.log2 K := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (log2_ge_one hK)
  refine ⟨Scalar.deltaK K/(4*s),4*Scalar.log2 K/s,by positivity,by positivity,?_⟩
  have hl := (prescribed_sqrt_input_div_tendsto hK).eventually
    (lt_mem_nhds (show s/2<s by linarith))
  have hu := (prescribed_sqrt_input_div_tendsto hK).eventually
    (gt_mem_nhds (show s<2*s by linarith))
  filter_upwards [hl,hu,prescribedFamily_gap_linear_bounds hK hδ,eventually_ge_atTop 1]
    with n hnlo hnhi hg hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hlo := (lt_div_iff₀ hnR).mp hnlo
  have hhi := (div_lt_iff₀ hnR).mp hnhi
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<4*s)).2
    nlinarith [mul_le_mul_of_nonneg_left hhi.le hδ.le,
      mul_le_mul_of_nonneg_left hg.1 hs.le]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hs).2
    nlinarith [mul_le_mul_of_nonneg_left hlo.le hlog.le,
      mul_le_mul_of_nonneg_left hg.2 hs.le]

end Nonadditivity.HaarPrescribedDimension
