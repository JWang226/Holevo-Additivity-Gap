/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPrescribedBound
import Nonadditivity.ProbabilityQuantitative

/-! # Explicit favorable-event probability at the prescribed Haar dimension -/

noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open MeasureTheory StructuredHaarConsequences StructuredHaarModel
  StructuredLinearization PolynomialReduction
open scoped Matrix Matrix.Norms.L2Operator

/-- The manuscript's probability fraction for each admissible linearized test
polynomial. The expectation estimate is discharged by the full Haar proof. -/
theorem prescribed_polynomial_favorable_probability {K n : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (H : Polynomial (StructuredLinearization.G n))
    (hlinear : ∀ w ∈ H.support, w = 1 ∨ ∃ x : Fin n × Fin 2,
      w = ProductPolynomialReduction.generator x ∨
        w = (ProductPolynomialReduction.generator x)⁻¹)
    (hherm : ∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
      (π : StructuredLinearization.G n →* unitary (Matrix ν ν ℂ)),
        (H.finiteEval π).IsHermitian)
    (hL : Real.log (2 * (Fintype.card H.Index : ℝ)) ≤
      2 * (K : ℝ)^(2*n) * Real.log (1 + 2*(n : ℝ)))
    (hpos : 0 < ‖H.regularEval‖) :
    Quantitative.tolerance (Real.log K) n /
        (2 * (1 + Quantitative.tolerance (Real.log K) n)) ≤
      (HaarModel.sampleMeasure 2 n (sampleSize K n)).real
        {ω | ‖H.finiteEval (sampleRepresentation n (sampleSize K n) ω)‖ ≤
          (1 + Quantitative.tolerance (Real.log K) n) * ‖H.regularEval‖} := by
  have hnpos : (0 : ℝ) < n := by
    have hn64 := (Quantitative.threshold_consequences hK hn).2.1
    linarith
  have hL0 : 0 ≤ Real.log (2 * (Fintype.card H.Index : ℝ)) := by
    have hc : (1 : ℝ) ≤ Fintype.card H.Index := by
      exact_mod_cast Fintype.card_pos (α := H.Index)
    exact Real.log_nonneg (by linarith)
  have hlog := (Quantitative.quantitative_certificate hK hn hL0 hL).2.2.2
  have hε : 0 < Quantitative.tolerance (Real.log K) n := by
    unfold Quantitative.tolerance
    positivity
  have he := (explicitHaarExpectation hK hn) H hlinear hherm
  have hfactor : Real.exp (Quantitative.haarLogMultiplier (Real.log K) n
      (Real.log (2 * (Fintype.card H.Index : ℝ)))) ≤
        1 + Quantitative.tolerance (Real.log K) n / 2 := by
    have h := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log (by linarith :
      0 < 1 + Quantitative.tolerance (Real.log K) n / 2)] at h
    exact h.le
  apply Probability.favorable_realization_probability
    (integrable_polynomial_norm n (sampleSize K n) H)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hε hpos
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hfactor hpos.le])

end Nonadditivity.HaarPrescribedDimension
