/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Trace

namespace Nonadditivity.ComplexRealTrace

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Matrix.Norms.L2Operator

set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restricting a complex matrix operator to real scalars doubles the real
part of its complex trace. -/
theorem trace_restrict (A : Matrix ι ι ℂ) :
    ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).restrictScalars ℝ).toLinearMap.trace ℝ
      (EuclideanSpace ℂ ι) = 2 * A.trace.re := by
  let b := (EuclideanSpace.basisFun ι ℂ).toBasis
  let c := Complex.basisOneI.smulTower' b
  rw [LinearMap.trace_eq_matrix_trace ℝ c]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
    LinearMap.toMatrix_apply, c, Module.Basis.smulTower'_repr,
    Module.Basis.smulTower'_apply]
  simp only [Fin.sum_univ_two, Complex.coe_basisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.coe_restrictScalars,
    LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hb (i : ι) : b.repr (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (b i)) i = A i i := by
    simp [b, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, Matrix.mulVec, dotProduct]
  simp only [hb, Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  simp only [Finset.sum_add_distrib, Complex.re_sum]
  ring

/-- The same identity for the square, used by Gaussian quadratic variance bounds. -/
theorem trace_square_restrict (A : Matrix ι ι ℂ) :
    ((((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A).restrictScalars ℝ).toLinearMap *
      (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A).restrictScalars ℝ).toLinearMap).trace ℝ
        (EuclideanSpace ℂ ι) = 2 * (A * A).trace.re := by
  have heq :
      (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A).restrictScalars ℝ).toLinearMap *
        (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A).restrictScalars ℝ).toLinearMap =
      (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A * A)).restrictScalars ℝ).toLinearMap := by
    rw [map_mul]
    rfl
  rw [heq, trace_restrict]

end
end Nonadditivity.ComplexRealTrace
