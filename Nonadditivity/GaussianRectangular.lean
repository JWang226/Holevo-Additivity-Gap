/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianQuadratic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Concrete rectangular Gaussian Stinespring samples

The law is the real standard Gaussian measure on the complex coordinate space.
The normalization gives independent complex entries with squared magnitude
expectation `1 / (card B * card Env)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace Nonadditivity.GaussianRectangular

variable (B Env D : Type*) [Fintype B] [Fintype Env] [Fintype D]

/-- The real Gaussian sampling space, displayed as a complex Euclidean coordinate array. -/
abbrev Sample := EuclideanSpace ℂ ((B × Env) × D)

/-- Each real and imaginary coordinate has this standard-deviation multiplier. -/
def samplingScale : ℝ := (Real.sqrt (2 * Fintype.card B * Fintype.card Env))⁻¹

/-- A concrete rectangular random matrix, ready for normalization to an isometry. -/
def sampleMatrix (z : Sample B Env D) : Matrix (B × Env) D ℂ :=
  fun r d => (samplingScale B Env : ℂ) * z (r, d)

/-- The exact Gaussian measure used for the construction. -/
def sampleMeasure : Measure (Sample B Env D) := stdGaussian (Sample B Env D)

instance sampleProbability : IsProbabilityMeasure (sampleMeasure B Env D) := by
  unfold sampleMeasure
  infer_instance

variable {B Env D}

/-- Coefficients of the fixed-input pullback of `A ⊗ I` to the rectangular entries. -/
def pullbackMatrix [DecidableEq Env]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) :
    Matrix ((B × Env) × D) ((B × Env) × D) ℂ :=
  fun p q => star (x p.2) * A p.1.1 q.1.1 * (if p.1.2 = q.1.2 then 1 else 0) * x q.2

/-- The concrete quadratic coefficient matrix including the Gaussian scale. -/
def quadraticMatrix [DecidableEq Env]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) :
    Matrix ((B × Env) × D) ((B × Env) × D) ℂ :=
  (samplingScale B Env ^ 2 : ℝ) • pullbackMatrix A x

/-- The same coefficient matrix acting on the underlying real Gaussian space. -/
def quadraticOperator [DecidableEq B] [DecidableEq Env] [DecidableEq D]
    (A : Matrix B B ℂ) (x : EuclideanSpace ℂ D) :
    Sample B Env D →L[ℝ] Sample B Env D := (Matrix.toEuclideanCLM (n := ((B × Env) × D)) (𝕜 := ℂ) (quadraticMatrix A x)).restrictScalars ℝ

end Nonadditivity.GaussianRectangular
