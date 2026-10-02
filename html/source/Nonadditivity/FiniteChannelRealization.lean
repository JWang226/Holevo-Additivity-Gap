/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FiniteRealization
import Nonadditivity.Conversion

/-! # Realization of actual channels from norm convergence

The analytic premises concern pointwise convergence in probability of
concrete Kraus adjoints and the norm of their limit. A joint entropy witness
is stated separately here; the unitary block construction supplies it.
-/

noncomputable section

namespace Nonadditivity.FiniteChannelRealization

open Entropy Channels Channels.KrausChannel AdjointPurity Conversion
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} [NeZero d]

/-- Finite-dimensional actual channels with both Holevo bounds, derived
from pointwise norm convergence and an actual entangled entropy witness. -/
theorem eventually_exists_converted_bounds
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {D : ν → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    {η : ν → Type*} [∀ i, Fintype (η i)]
    (μ : (i : ν) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (T : (i : ν) → Ω i → KrausChannel (D i) (ZMod d) (η i)) (l : Filter ν)
    (limitNorm : Matrix (ZMod d) (ZMod d) ℂ → ℝ) {κ c B : ℝ}
    (hκ : 1 < κ) (hc : 0 < c)
    (hlimit : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 → limitNorm A ≤ c)
    (hconvergence : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      ∀ ε : ℝ, 0 < ε → Filter.Tendsto
      (fun i => μ i {ω | ε ≤ |‖(T i ω).adjointMap A‖ - limitNorm A|}) l (nhds 0))
    (hjoint : ∀ i ω, ∃ ρ : DensityMatrix (D i × D i),
      (((T i ω).tensor (T i ω).conjugate).output ρ).vonNeumann ≤ B) :
    Filter.Eventually (fun i => ∃ ω,
      (converted (T i ω)).holevo ≤ Real.log (1 + (d : ℝ) * (κ * c) ^ 2) ∧
      2 * Real.log d - B ≤
        ((converted (T i ω)).tensor (converted (T i ω))).holevo ∧
      2 * Real.log d - B - 2 * Real.log (1 + (d : ℝ) * (κ * c) ^ 2) ≤
        ((converted (T i ω)).tensor (converted (T i ω))).holevo -
          2 * (converted (T i ω)).holevo) l := by
  have hcert := FiniteRealization.eventually_exists_kraus_certificate
    μ T l limitNorm hκ hc hlimit hconvergence
  have ht : 0 ≤ κ * c := mul_nonneg (by linarith) hc.le
  apply hcert.mono
  rintro i ⟨ω, hω⟩
  obtain ⟨ρ, hρ⟩ := hjoint i ω
  exact ⟨ω, converted_bounds_of_certificate (T i ω) ht hω ρ hρ⟩

end Nonadditivity.FiniteChannelRealization
