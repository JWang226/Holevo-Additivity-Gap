/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPrescribedBound
import Nonadditivity.HolevoRateLimit
import Nonadditivity.Dimensions

/-! # Asymptotic consequences for the prescribed-dimension channels

Every information quantity in this module belongs to the actual finite CPTP
channel selected from the unconditional prescribed-dimension construction.
The regularized quantity is the tensor-power Holevo rate, with no operational
coding interpretation required.
-/
noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open ActualConsequences StructuredHaarConsequences Filter Topology

/-- A genuine channel at every index, with the construction threshold used
only for the finitely many initial terms. -/
def prescribedFamily {K : ℕ} (hK : 2 ≤ K) (n : ℕ) : FiniteQuantumChannel :=
  Classical.choose (exists_prescribed_channel_with_lower_bound hK
    (le_max_left (Quantitative.n₀ K) n))

theorem prescribedFamily_spec {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    Fintype.card (prescribedFamily hK n).Input = 2*(localDimension K n)^n*K^(2*n) ∧
    Fintype.card (prescribedFamily hK n).Output = K^n ∧
    0 < (prescribedFamily hK n).chi ∧
    (prescribedFamily hK n).chi ≤ (n:ℝ)*Scalar.aK K+2*Scalar.log2 (kappa n) ∧
    (n:ℝ)*Scalar.log2 K/(K:ℝ) ≤ (prescribedFamily hK n).chiTwo ∧
    (n:ℝ)*Scalar.deltaK K-4*Scalar.log2 (kappa n) ≤
      (prescribedFamily hK n).gap := by
  have h := Classical.choose_spec (exists_prescribed_channel_with_lower_bound hK
    (le_max_left (Quantitative.n₀ K) n))
  have hs := And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.2))
  simpa only [prescribedFamily, max_eq_right hn] using hs

/-- The positive one-use information has the supplementary explicit lower
bound for the very same selected channel. -/
theorem prescribedFamily_chi_lower {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    2*(n:ℝ)/(K:ℝ) ≤ (prescribedFamily hK n).chi := by
  have h := (Classical.choose_spec (exists_prescribed_channel_with_lower_bound hK
    (le_max_left (Quantitative.n₀ K) n))).2.2.2.1
  simpa only [prescribedFamily, max_eq_right hn] using h

theorem correction_eq (n : ℕ) :
    4*Scalar.log2 (kappa n) = Asymptotics.finiteSizeCorrection n := by
  unfold Scalar.log2 kappa Asymptotics.finiteSizeCorrection
  ring

/-- The finite regularized gain follows already from two tensor uses. -/
theorem prescribedFamily_regularizedGain_lower {K n : ℕ} (hK : 2 ≤ K)
    (hn : Quantitative.n₀ K ≤ n) :
    (n:ℝ)*Scalar.deltaK K/2-2*Scalar.log2 (kappa n) ≤
      (prescribedFamily hK n).regularizedGain := by
  have h := (prescribedFamily_spec hK hn).2.2.2.2.2
  have ht := (prescribedFamily hK n).two_use_gain_le_regularizedGain
  unfold FiniteQuantumChannel.gap at h
  linarith

theorem prescribedFamily_gap_lower_eventually {K : ℕ} (hK : 2 ≤ K) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)*Scalar.deltaK K-Asymptotics.finiteSizeCorrection n ≤
      (prescribedFamily hK n).gap := by
  filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
  simpa only [correction_eq] using (prescribedFamily_spec hK hn).2.2.2.2.2

/-- With the manuscript's positive slope, the actual additive gap diverges. -/
theorem prescribedFamily_gap_tendsto_atTop_of_delta_pos {K : ℕ} (hK : 2 ≤ K)
    (hδ : 0 < Scalar.deltaK K) :
    Tendsto (fun n => (prescribedFamily hK n).gap) atTop atTop := by
  apply Asymptotics.gap_tendsto_atTop
    (fun n => (prescribedFamily hK n).gap) hδ
  exact prescribedFamily_gap_lower_eventually hK

theorem prescribedFamily_gap_tendsto_atTop {K : ℕ} (hK : 2 ≤ K)
    (hlog : 18 < Real.log (K:ℝ)) :
    Tendsto (fun n => (prescribedFamily hK n).gap) atTop atTop :=
  prescribedFamily_gap_tendsto_atTop_of_delta_pos hK
    (Scalar.deltaK_pos (by exact_mod_cast (show 0<K by omega)) hlog)

theorem prescribedFamily_regularizedGain_tendsto_atTop_of_delta_pos {K : ℕ} (hK : 2 ≤ K)
    (hδ : 0 < Scalar.deltaK K) :
    Tendsto (fun n => (prescribedFamily hK n).regularizedGain) atTop atTop := by
  have h := (prescribedFamily_gap_tendsto_atTop_of_delta_pos hK hδ).atTop_div_const
    (by norm_num : (0:ℝ)<2)
  apply tendsto_atTop_mono (fun n => ?_) h
  have ht := (prescribedFamily hK n).two_use_gain_le_regularizedGain
  unfold FiniteQuantumChannel.gap
  linarith

theorem prescribedFamily_regularizedGain_tendsto_atTop {K : ℕ} (hK : 2 ≤ K)
    (hlog : 18 < Real.log (K:ℝ)) :
    Tendsto (fun n => (prescribedFamily hK n).regularizedGain) atTop atTop :=
  prescribedFamily_regularizedGain_tendsto_atTop_of_delta_pos hK
    (Scalar.deltaK_pos (by exact_mod_cast (show 0<K by omega)) hlog)

/-- Every strict threshold below the explicit asymptotic ratio is attained
eventually by the actual two-use Holevo ratio. -/
theorem prescribedFamily_ratio_eventually {K : ℕ} (hK : 2 ≤ K) {R : ℝ}
    (hR : R < Scalar.log2 K/(2*(K:ℝ)*Scalar.aK K)) :
    ∀ᶠ n : ℕ in atTop, R ≤ (prescribedFamily hK n).twoUseRatio := by
  have hK0 : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have ha := Scalar.aK_pos hK0
  have hb : 0 ≤ Scalar.log2 K/(K:ℝ) := by
    unfold Scalar.log2
    exact div_nonneg (div_nonneg (Real.log_nonneg
      (by exact_mod_cast (show 1≤K by omega)))
      Scalar.log_two_pos.le) hK0.le
  apply Asymptotics.eventually_ratio_of_holevo_bounds
    (fun n => (prescribedFamily hK n).chi)
    (fun n => (prescribedFamily hK n).chiTwo) ha hb
    (by convert hR using 1; ring)
  · filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
    exact (prescribedFamily_spec hK hn).2.2.1
  · filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
    have h := (prescribedFamily_spec hK hn).2.2.2.1
    rw [← correction_eq]
    linarith
  · filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
    convert (prescribedFamily_spec hK hn).2.2.2.2.1 using 1; ring

theorem prescribedFamily_regularizedRatio_eventually {K : ℕ} (hK : 2 ≤ K) {R : ℝ}
    (hR : R < Scalar.log2 K/(2*(K:ℝ)*Scalar.aK K)) :
    ∀ᶠ n : ℕ in atTop, R ≤ (prescribedFamily hK n).regularizedRatio := by
  filter_upwards [prescribedFamily_ratio_eventually hK hR,
    eventually_ge_atTop (Quantitative.n₀ K)] with n hr hn
  exact hr.trans ((prescribedFamily hK n).two_use_ratio_le_regularizedRatio
    (prescribedFamily_spec hK hn).2.2.1)

/-- The manuscript's quadratic input-qubit expansion holds for the actual
channels, with its ceiling remainder tending to zero. -/
theorem prescribedFamily_input_size_remainder_tendsto {K : ℕ} (hK : 2 ≤ K) :
    Tendsto (fun n : ℕ => Scalar.log2 (Fintype.card (prescribedFamily hK n).Input) -
      (Quantitative.dimensionExponent (Real.log K)/Real.log 2*(n:ℝ)^2 +
        2*(n:ℝ)*Scalar.log2 K+1)) atTop (𝓝 0) := by
  have hK0 : 0<K := by omega
  have hlog : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤K by omega))
  have hb : 0 < Quantitative.dimensionExponent (Real.log K) := by
    unfold Quantitative.dimensionExponent
    positivity
  have h := Dimensions.input_size_remainder_tendsto hK0 hb
  apply h.congr'
  filter_upwards [eventually_ge_atTop (Quantitative.n₀ K)] with n hn
  rw [(prescribedFamily_spec hK hn).1]
  rfl

end Nonadditivity.HaarPrescribedDimension
