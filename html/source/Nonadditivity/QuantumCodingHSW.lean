/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingTypicalTests
import Nonadditivity.QuantumCodingPacking
import Nonadditivity.QuantumCodingChannelWords
import Nonadditivity.QuantumCodingRates

/-! # Achievability of finite-ensemble Holevo information

The codes below have actual density-matrix codewords on channel tensor
powers and normalized POVM decoders. Their error is the Born error, bounded
by the independently proved spectral typicality and sequential packing
estimates. No coding theorem or capacity identification is assumed.
-/

noncomputable section
namespace Nonadditivity.QuantumCoding

open Entropy Channels Operational RegularizedHolevo
open scoped BigOperators ComplexOrder Matrix

variable {ι ο κ α : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ] [Fintype α]

def outputEnsembleInformation (T : KrausChannel ι ο κ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι) : ℝ :=
  (DensityMatrix.mixture p hp hs (fun a => T.output (ρ a))).vonNeumann -
    ensembleConditionalEntropy p (fun a => T.output (ρ a))

def ensembleCodingVariance (T : KrausChannel ι ο κ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι) : ℝ :=
  9 * QuantumCodingTypicality.variance
    (DensityMatrix.mixture p hp hs (fun a => T.output (ρ a))).weights +
  8 * ensembleConditionalVariance p (fun a => T.output (ρ a))

/-- Actual finite-block codes with the explicit HSW packing estimate. -/
theorem finite_ensemble_codes (T : KrausChannel ι ο κ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    (n M : ℕ) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : Code (positiveTensorPower T n) M,
      C.error ≤ ensembleCodingVariance T p hp hs ρ /
        (((n + 1 : ℕ) : ℝ) * δ ^ 2) +
        4 * (M - 1 : ℕ) * Real.exp (-((n + 1 : ℕ) : ℝ) *
          (outputEnsembleInformation T p hp hs ρ - 2 * δ)) := by
  let out := fun a => T.output (ρ a)
  let σ := DensityMatrix.mixture p hp hs out
  let G := globalTypicalTest σ (n + 1) δ
  let Q := conditionalTypicalTest p out (n + 1) δ
  let w := tensorWeights p (n + 1)
  let states := fun x : Fin (n + 1) → α => tensorFamilyState (fun j => out (x j))
  have hcross : (∑ x, ∑ y, w x * w y * crossAcceptance G (Q y) (states x)) ≤
      Real.exp (-((n + 1 : ℕ) : ℝ) * (σ.vonNeumann - ensembleConditionalEntropy p out - 2 * δ)) := by
    have h := typicalProjectors_average_cross_le p hp hs out (n + 1) δ
    rw [Finset.sum_comm]
    simpa only [crossAcceptance, G, Q, globalTypicalTest, conditionalTypicalTest,
      states, w, Matrix.mul_assoc, mul_comm] using h
  obtain ⟨c, D, hD⟩ := exists_projective_packing hM G Q w
    (tensorWeights_nonneg p hp (n + 1)) (tensorWeights_sum p hs (n + 1)) states
    (globalTypicalTest_mean_rejection_le p hp hs out (Nat.succ_pos n) hδ)
    (conditionalTypicalTest_mean_rejection_le p hp hs out (Nat.succ_pos n) hδ) hcross
  refine ⟨wordCode T n M (fun m j => ρ (c m j)) D, ?_⟩
  rw [wordCode_error]
  have herr : 1 - (∑ m, D.probability
      (tensorFamilyState (fun j => T.output (ρ (c m j)))) m) / (M : ℝ) =
      1 - (M : ℝ)⁻¹ * ∑ m, D.probability (states (c m)) m := by
    simp only [states, out, div_eq_mul_inv, mul_comm]
  rw [herr]
  convert hD using 1
  unfold ensembleCodingVariance outputEnsembleInformation
  dsimp [out, σ]
  ring

/-- Every nonnegative rate strictly below a finite input ensemble's Holevo
information is attained by actual channel codes with error tending to zero. -/
theorem ensemble_rate_achievable [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι)
    {r : ℝ} (hr : 0 ≤ r) (hinfo : r < outputEnsembleInformation T p hp hs ρ) :
    AchievableRate T (r / Real.log 2) := by
  let χ := outputEnsembleInformation T p hp hs ρ
  let δ := (χ - r) / 4
  have hδ : 0 < δ := by dsimp [δ, χ]; linarith
  have hgap : r < χ - 2 * δ := by dsimp [δ, χ]; linarith
  apply achievableRate_of_finite_codes T hr hgap
    (ensembleCodingVariance T p hp hs ρ / δ ^ 2)
  intro n
  obtain ⟨C, hC⟩ := finite_ensemble_codes T p hp hs ρ n (expMessages r n)
    (expMessages_pos r n) hδ
  refine ⟨C, hC.trans ?_⟩
  have hc : ((expMessages r n - 1 : ℕ) : ℝ) ≤ (expMessages r n : ℝ) := by
    exact_mod_cast Nat.sub_le (expMessages r n) 1
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))
      (Real.exp_nonneg (-((n + 1 : ℕ) : ℝ) * (χ - 2 * δ)))
  have hdiv : ensembleCodingVariance T p hp hs ρ / (((n + 1 : ℕ) : ℝ) * δ ^ 2) =
      (ensembleCodingVariance T p hp hs ρ / δ ^ 2) / ((n + 1 : ℕ) : ℝ) := by
    rw [div_div, mul_comm]
  rw [hdiv]
  exact add_le_add (le_refl _) hm

theorem ensemble_information_le_capacity [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (ρ : α → DensityMatrix ι) :
    outputEnsembleInformation T p hp hs ρ / Real.log 2 ≤ operationalCapacity T := by
  apply le_of_forall_lt_imp_le_of_dense
  intro q hq
  by_cases hq0 : 0 ≤ q
  · have h := ensemble_rate_achievable T p hp hs ρ
      (mul_nonneg hq0 Scalar.log_two_pos.le) ((lt_div_iff₀ Scalar.log_two_pos).mp hq)
    have hcap := achievableRate_le_capacity h
    simpa only [mul_div_cancel_right₀ _ Scalar.log_two_pos.ne'] using hcap
  · exact (le_of_not_ge hq0).trans (operationalCapacity_nonneg T)

/-- HSW lower bound for the actual single-use Holevo supremum. Every finite
output ensemble is lifted to real channel inputs, then encoded by the
constructed vanishing-error codes. -/
theorem holevoBits_le_operationalCapacity [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) : T.holevoBits ≤ operationalCapacity T := by
  apply (div_le_iff₀ Scalar.log_two_pos).mpr
  change StateEnsembles.quantity T.outputs ≤ operationalCapacity T * Real.log 2
  unfold StateEnsembles.quantity
  have hne : (Set.range (fun e : StateEnsembles.Ensemble T.outputs => e.information)).Nonempty := by
    obtain ⟨σ, hσ⟩ := T.outputs_nonempty
    exact ⟨_, ⟨StateEnsembles.singleton σ hσ, rfl⟩⟩
  apply csSup_le hne
  rintro _ ⟨e, rfl⟩
  have hex : ∀ a, ∃ ρ : DensityMatrix ι, T.output ρ = e.state a := e.state_mem
  choose input hinput using hex
  have hinfo : outputEnsembleInformation T e.weight e.weight_nonneg e.weight_sum input =
      e.information := by
    unfold outputEnsembleInformation ensembleConditionalEntropy
    simp_rw [hinput]
    rfl
  have h := ensemble_information_le_capacity T e.weight e.weight_nonneg e.weight_sum input
  rw [hinfo] at h
  exact (div_le_iff₀ Scalar.log_two_pos).mp h

end Nonadditivity.QuantumCoding
