/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianNormalization
import Nonadditivity.QuadraticNet

/-! Actual Gaussian channel construction from finitely many quadratic tests. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.GaussianNetRealization
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker InnerProductSpace
open GaussianNormalization FiniteRealization Channels
variable {D B E : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

def quadratic (A : Matrix D D ℂ) (x : EuclideanSpace ℂ D) : ℝ :=
  (⟪(Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) A x,x⟫_ℂ).re

theorem quadratic_sub_one (A : Matrix D D ℂ) (x : EuclideanSpace ℂ D) (hx : ‖x‖=1) :
    quadratic (A-1) x = quadratic A x - 1 := by
  unfold quadratic
  rw [map_sub,map_one]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,inner_sub_left,
    inner_self_eq_norm_sq_to_K,hx]
  norm_num

theorem rawAdjoint_hermitian (G : Matrix (B×E) D ℂ) (A : Matrix B B ℂ) (hA : A.IsHermitian) :
    (rawAdjoint G A).IsHermitian := by
  apply Matrix.isHermitian_conjTranspose_mul_mul G
  change (A ⊗ₖ (1:Matrix E E ℂ)).conjTranspose = _
  simp [Matrix.conjTranspose_kronecker,hA.eq]

theorem near_isometry_of_tests (G : Matrix (B×E) D ℂ)
    (inputs : Finset (EuclideanSpace ℂ D))
    (hunit : ∀x∈inputs,‖x‖=1) (hnet : UnitSphereNet inputs (1/4))
    (htests : ∀x∈inputs,|quadratic (gram G) x - 1|≤1/4) : ‖gram G-1‖≤1/2 := by
  have h := QuadraticNet.matrix_norm_le_of_unitSphereNet (gram G-1)
    ((gram_hermitian G).sub Matrix.isHermitian_one)
    (show (0:ℝ)≤1/4 by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤1/4)
    hunit hnet (by
      intro x hx
      change |quadratic (gram G-1) x|≤1/4
      rw [quadratic_sub_one _ _ (hunit x hx)]
      exact htests x hx)
  norm_num at h ⊢
  exact h

/-- Both finite nets and every loss factor are discharged for the actual normalized channel. -/
theorem channel_certificate_of_tests (G : Matrix (B×E) D ℂ)
    (inputs : Finset (EuclideanSpace ℂ D)) (outputs : Finset (ObservableSpace B))
    (hunit : ∀x∈inputs,‖x‖=1) (hinput : UnitSphereNet inputs (1/4))
    (houtput : UnitSphereNet outputs (1/2)) (t : ℝ) (ht : 0≤t)
    (hgram : ∀x∈inputs,|quadratic (gram G) x - 1|≤1/4)
    (hraw : ∀a∈outputs,∀x∈inputs,|quadratic (rawAdjoint G (observableMatrix a)) x|≤t) :
    ∃T : KrausChannel D B E, ∀A : Matrix B B ℂ, A.IsHermitian → A.trace=0 →
      ‖T.adjointMap A‖≤(8*t)*AdjointPurity.hsLength A := by
  have hclose := near_isometry_of_tests G inputs hunit hinput hgram
  let T := channel G hclose
  refine ⟨T,matrix_certificate_of_observable_bound T (8*t) ?_⟩
  have htests : ∀a∈outputs,‖adjointOnObservables T a‖≤4*t := by
    intro a ha
    have hq := QuadraticNet.matrix_norm_le_of_unitSphereNet
      (rawAdjoint G (observableMatrix a))
      (rawAdjoint_hermitian G _ (observableMatrix_isHermitian a))
      (show (0:ℝ)≤1/4 by norm_num) (by norm_num) ht hunit hinput (hraw a ha)
    have hrawnorm : ‖rawAdjoint G (observableMatrix a)‖≤2*t := by
      norm_num at hq
      linarith
    change ‖(channel G hclose).adjointMap (observableMatrix a)‖≤4*t
    exact (channel_adjoint_norm_le G hclose (observableMatrix a)).trans (by linarith)
  intro a
  have h := norm_apply_le_of_unitSphereNet (adjointOnObservables T)
    (show (0:ℝ)≤1/2 by norm_num) (by norm_num) (show 0≤4*t by positivity)
    houtput htests a
  convert h using 1
  ring

end Nonadditivity.GaussianNetRealization
