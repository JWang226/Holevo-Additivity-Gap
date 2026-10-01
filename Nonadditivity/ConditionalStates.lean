/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.StateEnsembles

/-! # Normalizing subnormalized positive states

Zero-probability branches are handled explicitly. This is the matrix
decomposition needed when a classical input register is measured.
-/

noncomputable section

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem positive_trace_real (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (A.trace.re : ℂ) = A.trace := by
  exact (Complex.eq_re_of_ofReal_le hA.trace_nonneg).symm

omit [DecidableEq ι] [Nonempty ι] in
theorem positive_trace_re_nonneg (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1

/-- Conditional state of a positive matrix, with an arbitrary fixed state on
the zero-probability branch. -/
def normalizePositive (A : Matrix ι ι ℂ) (hA : A.PosSemidef) : DensityMatrix ι :=
  if h : A.trace.re = 0 then maximallyMixed ι else
    { matrix := (((A.trace.re)⁻¹ : ℝ) : ℂ) • A
      positive := hA.smul (by exact_mod_cast inv_nonneg.mpr (positive_trace_re_nonneg A hA))
      normalized := by
        rw [Matrix.trace_smul, smul_eq_mul, ← positive_trace_real A hA]
        simp only [Complex.ofReal_re, ← Complex.ofReal_mul, inv_mul_cancel₀ h,
          Complex.ofReal_one] }

/-- Renormalization exactly recovers the original positive matrix, including
the zero-trace case. -/
theorem trace_smul_normalizePositive (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (A.trace.re : ℂ) • (normalizePositive A hA).matrix = A := by
  by_cases h : A.trace.re = 0
  · have hz : A.trace = 0 := by rw [← positive_trace_real A hA, h]; simp
    have hzero := hA.trace_eq_zero_iff.mp hz
    simp [hzero]
  · simp only [normalizePositive, dif_neg h, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ h, Complex.ofReal_one, one_smul]

end Nonadditivity.Entropy
