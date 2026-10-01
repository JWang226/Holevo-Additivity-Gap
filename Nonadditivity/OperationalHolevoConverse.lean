/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalNaimark
import Nonadditivity.QuantumCodingContinuity
import Nonadditivity.QuantumCodingTraceDistance

/-! # Entropy estimates for actual finite quantum codes -/

noncomputable section

namespace Nonadditivity.Operational

open Entropy Channels QuantumCodingContinuity
open scoped BigOperators ComplexOrder

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

def uniformWeight (M : ℕ) : Fin M → ℝ := fun _ => 1 / (M : ℝ)

theorem uniformWeight_nonneg (M : ℕ) (m : Fin M) : 0 ≤ uniformWeight M m := by
  unfold uniformWeight
  positivity

theorem uniformWeight_sum {M : ℕ} (hM : 0 < M) : ∑ m, uniformWeight M m = 1 := by
  simp [uniformWeight, Nat.ne_of_gt hM]

theorem mean_sqrt_le_sqrt_mean {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ)
    (ha : ∀ m, 0 ≤ a m) :
    (∑ m, Real.sqrt (a m)) / M ≤ Real.sqrt ((∑ m, a m) / M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin M))
    (f := fun _ => (1 : ℝ)) (g := a) (fun _ => zero_le_one) ha
  simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have haSum : 0 ≤ ∑ m, a m := Finset.sum_nonneg fun m _ => ha m
  have hrootSum : 0 ≤ ∑ m, Real.sqrt (a m) := by positivity
  have hsq : (∑ m, Real.sqrt (a m)) ^ 2 ≤ (M : ℝ) * ∑ m, a m := by
    have hs2 := sq_le_sq₀ hrootSum
      (mul_nonneg (Real.sqrt_nonneg (M : ℝ)) (Real.sqrt_nonneg (∑ m, a m))) |>.mpr hs
    simpa only [mul_pow, Real.sq_sqrt hMpos.le, Real.sq_sqrt haSum] using hs2
  apply Real.le_sqrt_of_sq_le
  have hh := div_le_div_of_nonneg_right hsq (sq_nonneg (M : ℝ))
  convert hh using 1 <;> field_simp

def uniformAverage {M : ℕ} (hM : 0 < M) (ρ : Fin M → DensityMatrix ο) : DensityMatrix ο :=
  DensityMatrix.mixture (uniformWeight M) (uniformWeight_nonneg M) (uniformWeight_sum hM) ρ

def uniformInformation {M : ℕ} (hM : 0 < M) (ρ : Fin M → DensityMatrix ο) : ℝ :=
  (uniformAverage hM ρ).vonNeumann - (∑ m, (ρ m).vonNeumann) / M

namespace Code

variable {T : KrausChannel ι ο κ} {M : ℕ}

def outputEnsemble (C : Code T M) (hM : 0 < M) : StateEnsembles.Ensemble T.outputs where
  size := M
  weight := uniformWeight M
  weight_nonneg := uniformWeight_nonneg M
  weight_sum := uniformWeight_sum hM
  state := fun m => T.output (C.encode m)
  state_mem := fun m => ⟨C.encode m, rfl⟩

theorem outputEnsemble_information (C : Code T M) (hM : 0 < M) :
    (C.outputEnsemble hM).information = uniformInformation hM (fun m => T.output (C.encode m)) := by
  unfold StateEnsembles.Ensemble.information uniformInformation
  congr 1
  simp [outputEnsemble, uniformWeight, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  left
  rfl

theorem uniformInformation_le_holevo [Nonempty ο] (C : Code T M) (hM : 0 < M) :
    uniformInformation hM (fun m => T.output (C.encode m)) ≤ T.holevo := by
  rw [← C.outputEnsemble_information hM]
  exact le_csSup (StateEnsembles.information_bddAbove T.outputs) ⟨C.outputEnsemble hM, rfl⟩

theorem mean_failure_eq_error (C : Code T M) (hM : 0 < M) :
    (∑ m, (1 - C.decode.probability (T.output (C.encode m)) m)) / M = C.error := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  simp only [Code.error, Code.success, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_div,
    div_self hMne]

end Code

/-- Isometric Naimark dilation preserves the actual uniform ensemble's
Holevo information, including its average state. -/
theorem uniformInformation_dilate {μ : Type*} [Fintype μ] [DecidableEq μ]
    (P : POVM ο μ) {M : ℕ} (hM : 0 < M) (ρ : Fin M → DensityMatrix ο) :
    uniformInformation hM (fun m => P.dilate (ρ m)) = uniformInformation hM ρ := by
  unfold uniformInformation uniformAverage
  rw [← P.dilate_mixture]
  simp only [POVM.dilate_entropy]

/-- Two ensembles with controlled mean trace distance and controlled
average-state distance have close Holevo informations. These distance
premises will be supplied by the actual decoder's gentle projection. -/
theorem uniformInformation_le_add_of_traceDistance [Nonempty ο]
    {M : ℕ} (hM : 0 < M) (ρ σ : Fin M → DensityMatrix ο) {t : ℝ}
    (haverage : traceDistance (uniformAverage hM σ) (uniformAverage hM ρ) ≤ t)
    (hstates : (∑ m, traceDistance (σ m) (ρ m)) / M ≤ t) :
    uniformInformation hM σ ≤ uniformInformation hM ρ +
      2 * t * Real.log (Fintype.card ο) + 4 * Real.log 2 := by
  have hd : 0 ≤ Real.log (Fintype.card ο : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have ha := (le_abs_self ((uniformAverage hM σ).vonNeumann -
    (uniformAverage hM ρ).vonNeumann)).trans
      (vonNeumann_traceDistance_bound_uniform (uniformAverage hM σ) (uniformAverage hM ρ))
  have ha' : (uniformAverage hM σ).vonNeumann - (uniformAverage hM ρ).vonNeumann ≤
      t * Real.log (Fintype.card ο) + 2 * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right haverage hd
    linarith
  have hs (m : Fin M) : (ρ m).vonNeumann - (σ m).vonNeumann ≤
      traceDistance (σ m) (ρ m) * Real.log (Fintype.card ο) + 2 * Real.log 2 := by
    have hh := vonNeumann_traceDistance_bound_uniform (σ m) (ρ m)
    have hl := (neg_le_abs ((σ m).vonNeumann - (ρ m).vonNeumann)).trans hh
    linarith
  have hb := div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hs m) hMpos.le
  have hleft : (∑ m, ((ρ m).vonNeumann - (σ m).vonNeumann)) / (M : ℝ) =
      (∑ m, (ρ m).vonNeumann) / M - (∑ m, (σ m).vonNeumann) / M := by
    rw [Finset.sum_sub_distrib, sub_div]
  have hright : (∑ m : Fin M, (traceDistance (σ m) (ρ m) *
      Real.log (Fintype.card ο) + 2 * Real.log 2)) / M =
      ((∑ m, traceDistance (σ m) (ρ m)) / M) * Real.log (Fintype.card ο) +
        2 * Real.log 2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hleft, hright] at hb
  have hc := mul_le_mul_of_nonneg_right hstates hd
  unfold uniformInformation
  linarith

/-- Convexity of trace distance discharges the average-state requirement,
so only the mean of the individual actual state distances is needed. -/
theorem uniformInformation_le_add_of_mean_traceDistance [Nonempty ο]
    {M : ℕ} (hM : 0 < M) (ρ σ : Fin M → DensityMatrix ο) {t : ℝ}
    (hstates : (∑ m, traceDistance (σ m) (ρ m)) / M ≤ t) :
    uniformInformation hM σ ≤ uniformInformation hM ρ +
      2 * t * Real.log (Fintype.card ο) + 4 * Real.log 2 := by
  apply uniformInformation_le_add_of_traceDistance hM ρ σ _ hstates
  have h := traceDistance_mixture_le (uniformWeight M) (uniformWeight_nonneg M)
    (uniformWeight_sum hM) σ ρ
  change traceDistance (uniformAverage hM σ) (uniformAverage hM ρ) ≤ _ at h
  have he : (∑ m, uniformWeight M m * traceDistance (σ m) (ρ m)) =
      (∑ m, traceDistance (σ m) (ρ m)) / M := by
    simp only [uniformWeight, ← Finset.mul_sum]
    ring
  rw [he] at h
  exact h.trans hstates

end Nonadditivity.Operational
