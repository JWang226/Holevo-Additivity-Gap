/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarExpectationFromMoment
import Nonadditivity.HaarOnePairAssembly

/-! # Prescribed channel dimensions from the precise remaining path estimate

The premise below is deliberately explicit. It is discharged only when the
actual grouped path-length bound has been proved; no expectation estimate is
postulated as an axiom.
-/
noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open HaarOnePairAssembly HaarIteratedMoments StructuredHaarConsequences

theorem explicitHaarExpectation_of_lengthBounds {K n : ℕ}
    (hK : 2≤K) (hn : Quantitative.n₀ K≤n)
    (hpaths : OnePairLengthBounds (sampleSize K n)
      (Quantitative.momentParameter (Real.log K) n)) :
    ExplicitHaarExpectation K n := by
  have hKreal : (2:ℝ)≤K := by exact_mod_cast hK
  have hlogK := Real.log_le_log (by norm_num : (0:ℝ)<2) hKreal
  have hh : (2:ℝ)/3≤Real.log (K:ℝ) := by linarith [Real.log_two_gt_d9]
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn2 : (2:ℝ)≤n := by linarith
  have hp := (Quantitative.moment_parameter_bounds hh hn2).2.1
  have hD := HaarMomentConstants.prescribed_dimension_strong hh hn2
  have he : sampleSize K n+1=Quantitative.dimensionChoice (Real.log K) n :=
    sampleSize_add_one K n
  rw [←he,Nat.cast_add,Nat.cast_one] at hD
  exact explicitHaarExpectation_of_onePairTraceBound hK hn
    (onePairTraceBound_of_lengthBounds hp hD hpaths)

/-- All the original dimension and channel conclusions follow from the
literal path-length estimate at the prescribed moment order. -/
theorem exists_prescribed_channel_of_lengthBounds {K n : ℕ}
    (hK : 2≤K) (hn : Quantitative.n₀ K≤n)
    (hpaths : OnePairLengthBounds (sampleSize K n)
      (Quantitative.momentParameter (Real.log K) n)) :
    ∃ T : ActualConsequences.FiniteQuantumChannel,
      Fintype.card T.Input = 2*(localDimension K n)^n*K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧
      T.chi ≤ (n:ℝ)*Scalar.aK K+2*Scalar.log2 (kappa n) ∧
      (n:ℝ)*Scalar.log2 K/(K:ℝ)≤T.chiTwo ∧
      (n:ℝ)*Scalar.deltaK K-4*Scalar.log2 (kappa n)≤T.gap := by
  letI : NeZero K := ⟨by omega⟩
  exact exists_explicit_finite_channel hK hn (explicitHaarExpectation_of_lengthBounds hK hn hpaths)

end Nonadditivity.HaarPrescribedDimension
