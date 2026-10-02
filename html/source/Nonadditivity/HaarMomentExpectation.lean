/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMomentTail
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # From probability moments to expected operator norms

These are actual Bochner-integral inequalities. In particular, the power form
of Jensen's inequality permits Haar tensor replacement to be iterated before
taking a single root. No random-matrix estimate is assumed in this file.
-/

noncomputable section

namespace Nonadditivity.HaarMomentExpectation

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Jensen for the natural power of a nonnegative random variable. -/
theorem integral_pow_le {f : Ω → ℝ} (p : ℕ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hf : Integrable f μ)
    (hfp : Integrable (fun ω => f ω ^ p) μ) :
    (∫ ω, f ω ∂μ) ^ p ≤ ∫ ω, f ω ^ p ∂μ := by
  exact (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn
    isClosed_Ici hf0 hf hfp

/-- A moment bound controls the first moment by its positive real root. -/
theorem integral_le_rpow_of_moment_le {f : Ω → ℝ} {p : ℕ} (hp : 0 < p)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hf : Integrable f μ)
    (hfp : Integrable (fun ω => f ω ^ p) μ) {B : ℝ}
    (hB : (∫ ω, f ω ^ p ∂μ) ≤ B) :
    (∫ ω, f ω ∂μ) ≤ B ^ (1 / (p : ℝ)) := by
  have hi0 : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae hf0
  have hpow := (integral_pow_le p hf0 hf hfp).trans hB
  have hroot := Real.rpow_le_rpow (pow_nonneg hi0 p) hpow
    (show 0 ≤ (p : ℝ)⁻¹ by positivity)
  simpa only [one_div, Real.pow_rpow_inv_natCast hi0 hp.ne'] using hroot

/-- Separate a deterministic norm factor from a moment multiplier. -/
theorem integral_le_mul_rpow_of_moment_le {f : Ω → ℝ} {p : ℕ} (hp : 0 < p)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hf : Integrable f μ)
    (hfp : Integrable (fun ω => f ω ^ p) μ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hB : (∫ ω, f ω ^ p ∂μ) ≤ C * R ^ p) :
    (∫ ω, f ω ∂μ) ≤ R * C ^ (1 / (p : ℝ)) := by
  have h := integral_le_rpow_of_moment_le hp hf0 hf hfp hB
  rw [Real.mul_rpow hC (pow_nonneg hR p), one_div,
    Real.pow_rpow_inv_natCast hR hp.ne', mul_comm] at h
  simpa only [one_div] using h

/-- The power form specialized to the norm of an arbitrary normed-space-valued
random variable; its first moment is the integral of the norm. -/
theorem integral_norm_pow_le {E : Type*} [NormedAddCommGroup E]
    {X : Ω → E} (p : ℕ) (hX : Integrable (fun ω => ‖X ω‖) μ)
    (hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ) :
    (∫ ω, ‖X ω‖ ∂μ) ^ p ≤ ∫ ω, ‖X ω‖ ^ p ∂μ :=
  integral_pow_le p (Filter.Eventually.of_forall (fun ω => norm_nonneg (X ω))) hX hXp

/-- Moment-to-expectation conversion for an actual operator or matrix norm. -/
theorem integral_norm_le_rpow_of_moment_le {E : Type*} [NormedAddCommGroup E]
    {X : Ω → E} {p : ℕ} (hp : 0 < p)
    (hX : Integrable (fun ω => ‖X ω‖) μ)
    (hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ) {B : ℝ}
    (hB : (∫ ω, ‖X ω‖ ^ p ∂μ) ≤ B) :
    (∫ ω, ‖X ω‖ ∂μ) ≤ B ^ (1 / (p : ℝ)) :=
  integral_le_rpow_of_moment_le hp
    (Filter.Eventually.of_forall (fun ω => norm_nonneg (X ω))) hX hXp hB

/-- Averaging a root only decreases it relative to the root of the average. -/
theorem integral_rpow_le {f : Ω → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hf : Integrable f μ)
    (hfq : Integrable (fun ω => (f ω) ^ q) μ) :
    (∫ ω, (f ω) ^ q ∂μ) ≤ (∫ ω, f ω ∂μ) ^ q := by
  exact (Real.concaveOn_rpow hq0 hq1).le_map_integral
    (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici hf0 hf hfq

/-- A trace-moment estimate for genuine Hermitian matrices yields an expected
operator-norm estimate, including the actual finite matrix dimension. -/
theorem integral_norm_le_of_normalized_trace_moment_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : Ω → Matrix ι ι ℂ} (hX : ∀ ω, (X ω).IsHermitian)
    {p : ℕ} (hp : 0 < p)
    (hXn : Integrable (fun ω => ‖X ω‖) μ)
    (hXp : Integrable (fun ω => ‖X ω‖ ^ (2 * p)) μ)
    (hXt : Integrable (fun ω => (X ω ^ (2 * p)).trace.re) μ)
    {B : ℝ}
    (hB : (∫ ω, (X ω ^ (2 * p)).trace.re / (Fintype.card ι : ℝ) ∂μ) ≤ B) :
    (∫ ω, ‖X ω‖ ∂μ) ≤ ((Fintype.card ι : ℝ) * B) ^ (1 / ((2 * p : ℕ) : ℝ)) := by
  have hc : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hm : (∫ ω, ‖X ω‖ ^ (2 * p) ∂μ) ≤
      ∫ ω, (X ω ^ (2 * p)).trace.re ∂μ := by
    exact integral_mono hXp hXt (fun ω =>
      HaarMomentTail.norm_pow_le_trace_even (X ω) (hX ω) p)
  have ht : (∫ ω, (X ω ^ (2 * p)).trace.re ∂μ) ≤
      (Fintype.card ι : ℝ) * B := by
    rw [integral_div] at hB
    exact (div_le_iff₀ hc).mp hB |>.trans_eq (mul_comm _ _)
  exact integral_norm_le_rpow_of_moment_le (by omega) hXn hXp (hm.trans ht)

end Nonadditivity.HaarMomentExpectation
