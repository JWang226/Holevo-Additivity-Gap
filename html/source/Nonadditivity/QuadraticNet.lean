/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ObservableDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Quadratic tests on a finite sphere net control the norm of an actual symmetric operator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.QuadraticNet
open scoped InnerProductSpace
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Quadratic forms have a dimension-independent Lipschitz bound on the unit sphere. -/
theorem quadratic_difference (T : F →L[ℝ] F) (x y : F) :
    |⟪T x,x⟫_ℝ-⟪T y,y⟫_ℝ| ≤ ‖T‖*‖x-y‖*(‖x‖+‖y‖) := by
  have heq : ⟪T x,x⟫_ℝ-⟪T y,y⟫_ℝ = ⟪T (x-y),x⟫_ℝ+⟪T y,x-y⟫_ℝ := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [heq]
  calc
    |⟪T (x-y),x⟫_ℝ+⟪T y,x-y⟫_ℝ| ≤ |⟪T (x-y),x⟫_ℝ|+|⟪T y,x-y⟫_ℝ| := abs_add_le _ _
    _ ≤ (‖T‖*‖x-y‖)*‖x‖+(‖T‖*‖y‖)*‖x-y‖ := by
      apply add_le_add
      · exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _))
      · exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _))
    _ = _ := by ring

theorem norm_le_of_unit_quadratic (T : F →L[ℝ] F) (hT : T.IsSymmetric)
    {C : ℝ} (hC : 0≤C) (hquad : ∀x:F, ‖x‖=1 → |⟪T x,x⟫_ℝ|≤C) : ‖T‖≤C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx:x=0
  · simpa [hx] using hC
  · have hxnorm : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖=1 := by simp [norm_smul,hxnorm]
    have h := hquad (‖x‖⁻¹ • x) hu
    have hr := T.rayleigh_smul x (inv_ne_zero hxnorm)
    rw [←hr]
    simpa only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real,hu,one_pow,div_one] using h

/-- The actual quadratic net loss is `1/(1-2δ)`. -/
theorem norm_le_of_unitSphereNet (T : F →L[ℝ] F) (hT : T.IsSymmetric)
    {tests : Finset F} {δ C : ℝ} (hδ : 0≤δ) (hδhalf : δ<1/2) (hC : 0≤C)
    (hunit : ∀y∈tests, ‖y‖=1) (hnet : UnitSphereNet tests δ)
    (htests : ∀y∈tests, |⟪T y,y⟫_ℝ|≤C) : ‖T‖≤C/(1-2*δ) := by
  have hbound : ‖T‖≤C+2*δ*‖T‖ := by
    apply norm_le_of_unit_quadratic T hT (by positivity)
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hnet x hx
    have hdist : ‖x-y‖≤δ := by simpa only [dist_eq_norm] using hxy
    have hd := quadratic_difference T x y
    rw [hx,hunit y hy] at hd
    have hq : |⟪T x,x⟫_ℝ|≤|⟪T x,x⟫_ℝ-⟪T y,y⟫_ℝ|+|⟪T y,y⟫_ℝ| :=
      calc
        |⟪T x,x⟫_ℝ| = |(⟪T x,x⟫_ℝ-⟪T y,y⟫_ℝ)+⟪T y,y⟫_ℝ| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hm := mul_le_mul_of_nonneg_left hdist (norm_nonneg T)
    linarith [htests y hy]
  exact (le_div_iff₀ (by linarith)).mpr (by nlinarith)

/-- Actual finite sphere nets, with the proved volume cardinality estimate. -/
theorem exists_net {δ : ℝ} (hδ : 0<δ) (hδtwo : δ<2) [FiniteDimensional ℝ F] :
    ∃tests : Finset F, (∀x∈tests,‖x‖=1) ∧ UnitSphereNet tests δ ∧
      (tests.card:ℝ) ≤ (1+2/δ)^Module.finrank ℝ F := by
  classical
  obtain ⟨tests,_,hunit,_,_,hnet,hcard⟩ :=
    QuantitativeNet.exists_symmetric_unitSphereNet_containing (∅:Finset F) hδ hδtwo
      (by simp) (by simp) (by simp)
  exact ⟨tests,hunit,hnet,hcard⟩

/-- A quarter-net of the complex input sphere has at most `9^(2D)` tests. -/
theorem exists_complex_input_net (D : Type*) [Fintype D] :
    ∃tests : Finset (EuclideanSpace ℂ D), (∀x∈tests,‖x‖=1) ∧
      UnitSphereNet tests (1/4) ∧ tests.card ≤ 9^(2*Fintype.card D) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ D) = 2*Fintype.card D := by
    rw [←Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ D)]
    simp
  obtain ⟨tests,hunit,hnet,hcard⟩ := exists_net (F := EuclideanSpace ℂ D)
    (show (0:ℝ)<1/4 by norm_num) (by norm_num)
  refine ⟨tests,hunit,hnet,?_⟩
  rw [hdim] at hcard
  norm_num at hcard
  exact_mod_cast hcard

/-- A half-net of traceless Hermitian HS-unit observables has at most `5^(K²)` tests. -/
theorem exists_observable_net (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B] :
    ∃tests : Finset (FiniteRealization.ObservableSpace B), (∀x∈tests,‖x‖=1) ∧
      UnitSphereNet tests (1/2) ∧ tests.card ≤ 5^(Fintype.card B)^2 := by
  obtain ⟨tests,hunit,hnet,hcard⟩ := exists_net (F := FiniteRealization.ObservableSpace B)
    (show (0:ℝ)<1/2 by norm_num) (by norm_num)
  refine ⟨tests,hunit,hnet,?_⟩
  rw [ObservableDimension.observableSpace_finrank] at hcard
  norm_num at hcard
  have hsmall : tests.card ≤ 5^(Fintype.card B^2-1) := by exact_mod_cast hcard
  exact hsmall.trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

open scoped Matrix.Norms.L2Operator

/-- Complex Hermitian matrix version, with the Euclidean operator norm and literal quadratic form. -/
theorem matrix_norm_le_of_unitSphereNet {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℂ) (hA : A.IsHermitian)
    {tests : Finset (EuclideanSpace ℂ D)} {δ C : ℝ}
    (hδ : 0≤δ) (hδhalf : δ<1/2) (hC : 0≤C)
    (hunit : ∀x∈tests,‖x‖=1) (hnet : UnitSphereNet tests δ)
    (htests : ∀x∈tests, |(⟪(Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) A x,x⟫_ℂ).re|≤C) :
    ‖A‖≤C/(1-2*δ) := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ D) := InnerProductSpace.rclikeToReal ℂ _
  let T := ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) A).restrictScalars ℝ
  have hT : T.IsSymmetric := (Matrix.isHermitian_iff_isSymmetric.mp hA).restrictScalars
  have h := norm_le_of_unitSphereNet T hT hδ hδhalf hC hunit hnet (by
    intro x hx
    simpa only [T,ContinuousLinearMap.coe_restrictScalars,real_inner_eq_re_inner]
      using htests x hx)
  exact h

end Nonadditivity.QuadraticNet
