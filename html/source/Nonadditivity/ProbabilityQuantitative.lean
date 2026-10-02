/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp

/-! # The explicit probability of a favorable realization -/

noncomputable section
namespace Nonadditivity.Probability
open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The exact probability fraction used after the manuscript's expectation
bound. Nonnegativity is satisfied by the actual random operator norm. -/
theorem favorable_realization_probability {f : Ω → ℝ}
    (hf : Integrable f μ) (hnonneg : 0 ≤ᵐ[μ] f)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hmean : (∫ ω, f ω ∂μ) ≤ (1 + ε / 2) * ρ) :
    ε / (2 * (1 + ε)) ≤ μ.real {ω | f ω ≤ (1 + ε) * ρ} := by
  let c := (1 + ε) * ρ
  have hc : 0 < c := by dsimp [c]; positivity
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hf c
  have hsub : μ.real {ω | c < f ω} ≤ μ.real {ω | c ≤ f ω} :=
    measureReal_mono (fun _ h => (show c < f _ from h).le)
  have ht : NullMeasurableSet {ω | c < f ω} μ :=
    hf.aemeasurable.nullMeasurable measurableSet_Ioi
  have hcomp := measureReal_compl₀ ht
  have hcomp' : μ.real {ω | f ω ≤ c} = 1 - μ.real {ω | c < f ω} := by
    simpa only [Set.compl_setOf, not_lt, probReal_univ] using hcomp
  change ε / (2 * (1 + ε)) ≤ μ.real {ω | f ω ≤ c}
  rw [hcomp']
  have hbad : c * μ.real {ω | c < f ω} ≤ (1 + ε / 2) * ρ :=
    (mul_le_mul_of_nonneg_left hsub hc.le).trans (hm.trans hmean)
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + ε))).2
  dsimp [c] at hbad
  nlinarith

end Nonadditivity.Probability
