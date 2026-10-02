/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/
import Nonadditivity.HaarPrescribedDimension

/-! Expected statement only. The intentional `sorry` below is not a solution
proof and is excluded from the proof library and its axiom audit. -/
noncomputable section
namespace Nonadditivity.HaarPrescribedDimension
open StructuredHaarConsequences

theorem exists_prescribed_channel_with_lower_bound {K n : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    ∃ T : ActualConsequences.FiniteQuantumChannel,
      Fintype.card T.Input = 2 * (localDimension K n)^n * K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧
      2 * (n : ℝ) / (K : ℝ) ≤ T.chi ∧
      T.chi ≤ (n : ℝ) * Scalar.aK K + 2 * Scalar.log2 (kappa n) ∧
      (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo ∧
      (n : ℝ) * Scalar.deltaK K - 4 * Scalar.log2 (kappa n) ≤ T.gap := by
  sorry

end Nonadditivity.HaarPrescribedDimension
