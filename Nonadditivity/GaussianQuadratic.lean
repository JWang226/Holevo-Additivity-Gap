/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
The adapted portions are released under the Apache License 2.0.

The eigenbasis coordinate calculations in this file adapt proof patterns from
SLT/HansonWright.lean by Yuanhe Zhang, Jason D. Lee, and Fanghui Liu,
released under Apache 2.0 (2026), commit d0f506f0a695018265dccb33bcb05e2f5ca1c876.
The Gaussian density calculation and the quadratic concentration proof below
are established directly against this project's pinned mathlib.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace

/-! # Exact Gaussian quadratic integrals and concentration

This file derives the Gaussian quadratic MGF directly from the Gaussian density,
then diagonalizes a symmetric quadratic form. No concentration inequality is
assumed as a hypothesis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace Nonadditivity.GaussianQuadratic

/-- Exact one-dimensional Gaussian square-exponential integral. -/
theorem integral_exp_sq (a : ℝ) (ha : a < 1 / 2) :
    (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) =
      (sqrt (1 - 2 * a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hpoint (x : ℝ) :
      (sqrt (2 * π))⁻¹ * exp (-x ^ 2 / 2) * exp (a * x ^ 2) =
        (sqrt (2 * π))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_gaussian]
  have hb : 0 < 1 - 2 * a := by linarith
  have heq : π / (1 / 2 - a) = (2 * π) / (1 - 2 * a) := by field_simp
  rw [heq, sqrt_div (by positivity), ← mul_div_assoc,
    inv_mul_cancel₀ (ne_of_gt (sqrt_pos.2 (by positivity : 0 < 2 * π))), one_div]

/-- The quadratic Gaussian integral is integrable precisely in the subcritical range. -/
theorem integrable_exp_sq (a : ℝ) (ha : a < 1 / 2) :
    Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_sq a ha]
  exact inv_ne_zero (ne_of_gt (sqrt_pos.2 (by linarith)))

/-- A convenient elementary logarithm remainder estimate. -/
theorem neg_log_one_sub_le {u : ℝ} (hu : u ≤ 1 / 2) :
    -log (1 - u) ≤ u + 2 * u ^ 2 := by
  have hp : 0 < 1 - u := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.2 hp)
  rw [log_inv] at h
  have hrem : (1 - u)⁻¹ - 1 ≤ u + 2 * u ^ 2 := by
    apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 - 2 * u)]
  exact h.trans hrem

/-- Centered scalar square-exponential bound, uniform over both signs. -/
theorem integral_exp_centered_sq_le {a : ℝ} (ha : |a| ≤ 1 / 4) :
    (∫ x : ℝ, exp (a * (x ^ 2 - 1)) ∂gaussianReal 0 1) ≤ exp (4 * a ^ 2) := by
  have ha' : a < 1 / 2 := by have := le_abs_self a; linarith
  have hp : 0 < 1 - 2 * a := by linarith
  have hpoint (x : ℝ) : exp (a * (x ^ 2 - 1)) = exp (-a) * exp (a * x ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_exp_sq a ha']
  have hsqrt : (sqrt (1 - 2 * a))⁻¹ = exp (- log (1 - 2 * a) / 2) := by
    rw [neg_div, exp_neg, ← log_sqrt hp.le, exp_log (sqrt_pos.2 hp)]
  rw [hsqrt, ← exp_add]
  apply exp_le_exp.mpr
  have hlog := neg_log_one_sub_le (u := 2 * a) (by have := le_abs_self a; linarith)
  nlinarith



section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A real symmetric quadratic form in its orthonormal eigenbasis. -/
theorem quadratic_eq_eigen_sum (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (x : E) :
    inner ℝ (T x) x = ∑ i : Fin (Module.finrank ℝ E),
      hT.eigenvalues rfl i * ((hT.eigenvectorBasis rfl).repr x i) ^ 2 := by
  let b := hT.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  calc
    inner ℝ (T x) x = inner ℝ (b.repr (T x)) (b.repr x) := by
      rw [b.repr.inner_map_map]
    _ = _ := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hcoord : b.repr (T x) i = hT.eigenvalues rfl i * b.repr x i := by
        simpa [b] using hT.eigenvectorBasis_apply_self_apply
          (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) x i
      rw [hcoord]
      change (b.repr x i) * (hT.eigenvalues rfl i * b.repr x i) = _
      change _ = hT.eigenvalues rfl i * (b.repr x i) ^ 2
      ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Coordinates of eigenvector synthesis are the coefficients used. -/
theorem basis_repr_sum (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (z : Fin (Module.finrank ℝ E) → ℝ) (i : Fin (Module.finrank ℝ E)) :
    b.repr (∑ j, z j • b j) i = z i := by
  simp only [OrthonormalBasis.repr_apply_apply, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [b.inner_eq_zero hji.symm]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Exact centered quadratic Gaussian MGF as a finite product. -/
theorem integral_exp_centered_quadratic_eq
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (s : ℝ) :
    (∫ x : E, exp (s * (inner ℝ (T x) x - ∑ i, hT.eigenvalues rfl i))
      ∂stdGaussian E) =
    ∏ i : Fin (Module.finrank ℝ E),
      ∫ z : ℝ, exp ((s * hT.eigenvalues rfl i) * (z ^ 2 - 1))
        ∂gaussianReal 0 1 := by
  let b := hT.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map ((continuous_finset_sum _ fun i _ =>
      (continuous_apply i).smul continuous_const).aemeasurable) (by fun_prop)]
  have hpoint (z : Fin (Module.finrank ℝ E) → ℝ) :
      exp (s * (inner ℝ (T (∑ i, z i • b i)) (∑ i, z i • b i) -
        ∑ i, hT.eigenvalues rfl i)) =
      ∏ i, exp ((s * hT.eigenvalues rfl i) * (z i ^ 2 - 1)) := by
    rw [← Real.exp_sum]
    congr 1
    change s * (inner ℝ (T.toLinearMap (∑ i, z i • b i)) (∑ i, z i • b i) - _) = _
    rw [quadratic_eq_eigen_sum T.toLinearMap hT]
    simp only [show hT.eigenvectorBasis rfl = b from rfl, basis_repr_sum]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint]
  exact integral_fintype_prod_eq_prod (fun i z => exp ((s * hT.eigenvalues rfl i) * (z ^ 2 - 1)))

/-- The Gaussian quadratic MGF bound from spectral diagonalization and scalar integration. -/
theorem integral_exp_centered_quadratic_le
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (s : ℝ)
    (hs : ∀ i : Fin (Module.finrank ℝ E), |s * hT.eigenvalues rfl i| ≤ 1 / 4) :
    (∫ x : E, exp (s * (inner ℝ (T x) x - ∑ i, hT.eigenvalues rfl i))
      ∂stdGaussian E) ≤
      exp (4 * s ^ 2 * ∑ i, (hT.eigenvalues rfl i) ^ 2) := by
  rw [integral_exp_centered_quadratic_eq T hT s]
  calc
    _ ≤ ∏ i : Fin (Module.finrank ℝ E), exp (4 * (s * hT.eigenvalues rfl i) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun _ => exp_nonneg _)
      · intro i _
        exact integral_exp_centered_sq_le (hs i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Integrability accompanies the Gaussian MGF bound, rather than being assumed. -/
theorem integrable_exp_centered_quadratic
    (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (s : ℝ)
    (hs : ∀ i : Fin (Module.finrank ℝ E), |s * hT.eigenvalues rfl i| ≤ 1 / 4) :
    Integrable (fun x : E => exp (s * (inner ℝ (T x) x - ∑ i, hT.eigenvalues rfl i)))
      (stdGaussian E) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_centered_quadratic_eq T hT s]
  apply ne_of_gt
  apply Finset.prod_pos
  intro i _
  have hint : Integrable (fun z : ℝ =>
      exp ((s * hT.eigenvalues rfl i) * (z ^ 2 - 1))) (gaussianReal 0 1) := by
    have hsmall : s * hT.eigenvalues rfl i < 1 / 2 :=
      lt_of_le_of_lt ((le_abs_self _).trans (hs i)) (by norm_num)
    have hpt (z : ℝ) : exp ((s * hT.eigenvalues rfl i) * (z ^ 2 - 1)) =
        exp (-(s * hT.eigenvalues rfl i)) * exp ((s * hT.eigenvalues rfl i) * z ^ 2) := by
      rw [← exp_add]
      congr 1
      ring
    simp_rw [hpt]
    exact (integrable_exp_sq _ hsmall).const_mul _
  exact mgf_pos hint

omit [MeasurableSpace E] [BorelSpace E] in
/-- The squared spectral coefficients are the trace of the square. -/
theorem trace_sq_eq_sum_eigenvalues_sq (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) :
    (T.toLinearMap * T.toLinearMap).trace ℝ E =
      ∑ i : Fin (Module.finrank ℝ E), (hT.eigenvalues rfl i) ^ 2 := by
  let b := hT.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (T.toLinearMap (T.toLinearMap (b i))) = _
  have heig : T.toLinearMap (b i) = (hT.eigenvalues rfl i) • b i :=
    hT.apply_eigenvectorBasis rfl i
  rw [heig, map_smul, heig, inner_smul_right, inner_smul_right]
  simp [b.norm_eq_one, pow_two]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every spectral coefficient is bounded by the actual operator norm. -/
theorem abs_eigenvalue_le_norm (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (i : Fin (Module.finrank ℝ E)) :
    |hT.eigenvalues rfl i| ≤ ‖T‖ := by
  let b := hT.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have h := T.le_opNorm (b i)
  have heig : T (b i) = (hT.eigenvalues rfl i) • b i :=
    hT.apply_eigenvectorBasis rfl i
  simpa only [heig, norm_smul, Real.norm_eq_abs, b.norm_eq_one, mul_one] using h

/-- A basis-free, centered Gaussian quadratic MGF estimate. -/
theorem integral_exp_trace_centered_le (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (s : ℝ) (hs : |s| * ‖T‖ ≤ 1 / 4) :
    (∫ x : E, exp (s * (inner ℝ (T x) x - T.toLinearMap.trace ℝ E))
      ∂stdGaussian E) ≤ exp (4 * s ^ 2 * (T.toLinearMap * T.toLinearMap).trace ℝ E) := by
  rw [hT.trace_eq_sum_eigenvalues rfl, trace_sq_eq_sum_eigenvalues_sq T hT]
  apply integral_exp_centered_quadratic_le T hT s
  intro i
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_eigenvalue_le_norm T hT i) (abs_nonneg s)).trans hs

/-- Integrability of the centered MGF under the same explicit norm condition. -/
theorem integrable_exp_trace_centered (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (s : ℝ) (hs : |s| * ‖T‖ ≤ 1 / 4) :
    Integrable (fun x : E => exp (s * (inner ℝ (T x) x - T.toLinearMap.trace ℝ E)))
      (stdGaussian E) := by
  rw [hT.trace_eq_sum_eigenvalues rfl]
  apply integrable_exp_centered_quadratic T hT s
  intro i
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_eigenvalue_le_norm T hT i) (abs_nonneg s)).trans hs

/-- Explicit Gaussian upper-tail bound. The exponent parameter is free for optimization. -/
theorem measure_quadratic_ge_le (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (s t : ℝ)
    (hs : 0 ≤ s) (hsmall : s * ‖T‖ ≤ 1 / 4) :
    (stdGaussian E).real {x | t ≤ inner ℝ (T x) x - T.toLinearMap.trace ℝ E} ≤
      exp (-s * t + 4 * s ^ 2 * (T.toLinearMap * T.toLinearMap).trace ℝ E) := by
  have hsmall' : |s| * ‖T‖ ≤ 1 / 4 := by simpa [abs_of_nonneg hs] using hsmall
  calc
    _ ≤ exp (-s * t) * (∫ x : E,
        exp (s * (inner ℝ (T x) x - T.toLinearMap.trace ℝ E)) ∂stdGaussian E) :=
      measure_ge_le_exp_mul_mgf t hs (integrable_exp_trace_centered T hT s hsmall')
    _ ≤ exp (-s * t) * exp (4 * s ^ 2 * (T.toLinearMap * T.toLinearMap).trace ℝ E) :=
      mul_le_mul_of_nonneg_left (integral_exp_trace_centered_le T hT s hsmall') (exp_nonneg _)
    _ = _ := (exp_add _ _).symm

/-- Explicit Gaussian lower-tail bound. -/
theorem measure_quadratic_le_le (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (s t : ℝ)
    (hs : 0 ≤ s) (hsmall : s * ‖T‖ ≤ 1 / 4) :
    (stdGaussian E).real {x | inner ℝ (T x) x - T.toLinearMap.trace ℝ E ≤ -t} ≤
      exp (-s * t + 4 * s ^ 2 * (T.toLinearMap * T.toLinearMap).trace ℝ E) := by
  have hsmall' : |-s| * ‖T‖ ≤ 1 / 4 := by simpa [abs_neg, abs_of_nonneg hs] using hsmall
  calc
    _ ≤ exp (-(-s) * (-t)) * (∫ x : E,
        exp ((-s) * (inner ℝ (T x) x - T.toLinearMap.trace ℝ E)) ∂stdGaussian E) :=
      measure_le_le_exp_mul_mgf (-t) (neg_nonpos.mpr hs)
        (integrable_exp_trace_centered T hT (-s) hsmall')
    _ ≤ exp (-(-s) * (-t)) * exp (4 * (-s) ^ 2 * (T.toLinearMap * T.toLinearMap).trace ℝ E) :=
      mul_le_mul_of_nonneg_left (integral_exp_trace_centered_le T hT (-s) hsmall') (exp_nonneg _)
    _ = _ := by rw [← exp_add]; congr 1; ring

/-- Two-sided concentration for a concrete Gaussian quadratic form. -/
theorem measure_abs_quadratic_ge_le (T : E →L[ℝ] E)
    (hT : T.toLinearMap.IsSymmetric) (s t : ℝ)
    (hs : 0 ≤ s) (hsmall : s * ‖T‖ ≤ 1 / 4) :
    (stdGaussian E).real {x | t ≤ |inner ℝ (T x) x - T.toLinearMap.trace ℝ E|} ≤
      2 * exp (-s * t + 4 * s ^ 2 * (T.toLinearMap * T.toLinearMap).trace ℝ E) := by
  have heq : {x : E | t ≤ |inner ℝ (T x) x - T.toLinearMap.trace ℝ E|} =
      {x | t ≤ inner ℝ (T x) x - T.toLinearMap.trace ℝ E} ∪
      {x | inner ℝ (T x) x - T.toLinearMap.trace ℝ E ≤ -t} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs, le_neg]
  rw [heq]
  have hu := measure_quadratic_ge_le T hT s t hs hsmall
  have hl := measure_quadratic_le_le T hT s t hs hsmall
  exact (measureReal_union_le _ _).trans (by linarith)

/-- A finite collection of quadratic tests is simultaneously passed by an
actual Gaussian sample whenever their explicit Gaussian tail bounds sum to less than one. -/
theorem exists_simultaneous_quadratic_bounds {J : Type*} [Fintype J]
    (T : J → E →L[ℝ] E) (hT : ∀ j, (T j).toLinearMap.IsSymmetric)
    (s t : J → ℝ) (hs : ∀ j, 0 ≤ s j)
    (hsmall : ∀ j, s j * ‖T j‖ ≤ 1 / 4)
    (hbudget : (∑ j, 2 * exp (-s j * t j +
      4 * s j ^ 2 * ((T j).toLinearMap * (T j).toLinearMap).trace ℝ E)) < 1) :
    ∃ x : E, ∀ j, |inner ℝ (T j x) x - (T j).toLinearMap.trace ℝ E| < t j := by
  classical
  by_contra hnone
  push_neg at hnone
  have hcover : (⋃ j, {x : E | t j ≤
      |inner ℝ (T j x) x - (T j).toLinearMap.trace ℝ E|}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := hnone x
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hsum := measureReal_iUnion_fintype_le (μ := stdGaussian E)
    (fun j => {x : E | t j ≤ |inner ℝ (T j x) x - (T j).toLinearMap.trace ℝ E|})
  rw [hcover, probReal_univ] at hsum
  have hbound : (∑ j, (stdGaussian E).real
      {x : E | t j ≤ |inner ℝ (T j x) x - (T j).toLinearMap.trace ℝ E|}) ≤
      ∑ j, 2 * exp (-s j * t j +
        4 * s j ^ 2 * ((T j).toLinearMap * (T j).toLinearMap).trace ℝ E) := by
    apply Finset.sum_le_sum
    intro j _
    exact measure_abs_quadratic_ge_le (T j) (hT j) (s j) (t j) (hs j) (hsmall j)
  exact (not_lt_of_ge (hsum.trans hbound)) hbudget

end FiniteDimensional

end Nonadditivity.GaussianQuadratic
