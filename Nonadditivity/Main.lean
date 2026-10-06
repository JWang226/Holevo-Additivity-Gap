/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Entropy
import Nonadditivity.Holevo
import Nonadditivity.Net
import Nonadditivity.Purity
import Nonadditivity.Probability
import Nonadditivity.Linearization
import Nonadditivity.Quantitative
import Nonadditivity.Asymptotics
import Nonadditivity.Dimensions

/-!
# Connecting the checked entropy and numerical parts

This original component module connects density-matrix purity to entropy
and records the numerical gap implications. The subsequently added
`Qualitative` module proves actual finite-channel realization from explicit
limiting-norm and convergence hypotheses; its Bell and conversion steps are
proved internally. The later `ExactQualitative` and `HaarPrescribedBound`
modules prove the unconditional channel endpoints and prescribed finite
dimensions. Broader manuscript claims retain the scope recorded in
`docs/FORMALIZATION_STATUS.md`.
-/

noncomputable section

namespace Nonadditivity.Main

open Scalar Entropy

/-- Equation (single-entropy) for a concrete finite density matrix from the
block purity certificate. No entropy inequality is assumed. -/
theorem block_entropy_of_purity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) {K κ : ℝ} (n : ℕ) (hK : 0 < K) (hκ : 0 < κ)
    (hpurity : ρ.purity ≤ κ ^ 2 * (1 + 9 / K) ^ n / K ^ n) :
    (n : ℝ) * (log2 K - aK K) - 2 * log2 κ ≤ ρ.vonNeumann / Real.log 2 := by
  have hb : 0 < 1 + 9 / K := by positivity
  have hlog := Real.log_le_log ρ.purity_pos hpurity
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have hrenyi := ρ.vonNeumann_ge_neg_log_purity
  apply (le_div_iff₀ log_two_pos).mpr
  simp only [aK, log2]
  have hid : ((n : ℝ) *
      (Real.log K / Real.log 2 - Real.log (1 + 9 / K) / Real.log 2) -
      2 * (Real.log κ / Real.log 2)) * Real.log 2 =
      (n : ℝ) * (Real.log K - Real.log (1 + 9 / K)) - 2 * Real.log κ := by
    field_simp
  rw [hid]
  linarith

/-- The minimum entropy bound follows for any nonempty output family with
the uniform purity certificate, using the actual infimum definition. -/
theorem minimum_block_entropy_of_purity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (outputs : Set (DensityMatrix ι)) (hne : outputs.Nonempty)
    {K κ : ℝ} (n : ℕ) (hK : 0 < K) (hκ : 0 < κ)
    (hpurity : ∀ ρ ∈ outputs, ρ.purity ≤ κ ^ 2 * (1 + 9 / K) ^ n / K ^ n) :
    (n : ℝ) * (log2 K - aK K) - 2 * log2 κ ≤
      sInf ((fun ρ : DensityMatrix ι => ρ.vonNeumann / Real.log 2) '' outputs) := by
  apply le_csInf (hne.image _)
  rintro _ ⟨ρ, hρ, rfl⟩
  exact block_entropy_of_purity ρ n hK hκ (hpurity ρ hρ)

/-- The exact numerical statements of the main theorem, provided that its
two Holevo bounds have been established for the constructed channel. -/
theorem quantitative_gap_of_bounds {K χ₁ χ₂ C : ℝ} (n : ℕ)
    (hχ₁ : χ₁ ≤ (n : ℝ) * aK K + 2 * log2 (((n : ℝ) + 1) / ((n : ℝ) - 1)))
    (hχ₂ : (n : ℝ) * (log2 K / K) ≤ χ₂)
    (hC : χ₂ / 2 ≤ C) :
    (n : ℝ) * deltaK K - 4 * log2 (((n : ℝ) + 1) / ((n : ℝ) - 1)) ≤
        χ₂ - 2 * χ₁ ∧
      (n : ℝ) * deltaK K / 2 - 2 * log2 (((n : ℝ) + 1) / ((n : ℝ) - 1)) ≤
        C - χ₁ := by
  constructor
  · have h := Scalar.holevo_gap hχ₁ hχ₂
    nlinarith
  · exact Scalar.capacity_gap hχ₁ hχ₂ hC

end Nonadditivity.Main
