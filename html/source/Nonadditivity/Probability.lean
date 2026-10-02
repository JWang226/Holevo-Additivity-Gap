/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-!
# Extracting a realization from the expectation estimate

The random-matrix expectation estimate is an explicit hypothesis. The
existence and positive probability of a favorable realization are proved
using the actual measure-theoretic integral on a probability space.
-/

noncomputable section

namespace Nonadditivity.Probability

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem positive_measure_sublevel {f : Ω → ℝ} (hf : Integrable f μ) {c : ℝ}
    (hmean : (∫ ω, f ω ∂μ) < c) : 0 < μ {ω | f ω ≤ c} := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hae : ∀ᵐ ω ∂μ, c ≤ f ω := by
    have hnot : ∀ᵐ ω ∂μ, ¬ f ω ≤ c := by
      rw [ae_iff]
      simpa using hzero
    filter_upwards [hnot] with ω hω
    exact (lt_of_not_ge hω).le
  have h := integral_mono_ae (integrable_const c) hf hae
  have hconst : (∫ _ : Ω, c ∂μ) = c := by simp
  rw [hconst] at h
  exact (not_le_of_gt hmean) h

/-- The existence step following (En-bound). It does not postulate a good
sample, and does not need an a priori finite sample space. -/
theorem favorable_realization {f : Ω → ℝ} (hf : Integrable f μ)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hmean : (∫ ω, f ω ∂μ) ≤ (1 + ε / 2) * ρ) :
    ∃ ω, f ω ≤ (1 + ε) * ρ := by
  have hlt : (∫ ω, f ω ∂μ) < (1 + ε) * ρ := by nlinarith
  have hmeasure := positive_measure_sublevel hf hlt
  have hnonempty : ({ω | f ω ≤ (1 + ε) * ρ} : Set Ω).Nonempty := by
    by_contra hempty
    have hz : ({ω | f ω ≤ (1 + ε) * ρ} : Set Ω) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    rw [hz, measure_empty] at hmeasure
    exact (lt_irrefl _) hmeasure
  exact hnonempty

end Nonadditivity.Probability
