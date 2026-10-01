/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarAveraging
import Nonadditivity.HaarMixedMoments
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Permutation contraction tensors at arbitrary degree

The contraction tensors are genuine invariant vectors of the mixed tensor
representation of the compact unitary group.  When the tensor degree does not
exceed the local dimension their Gram matrix is strictly positive and hence
invertible.  No invariant-spanning or Weingarten integration theorem is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarInvariantTensor

open MeasureTheory HaarModel HaarAveraging
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder Kronecker

abbrev Tuple (N p : ℕ) := Fin p → Fin (N+1)
abbrev Pair (N p : ℕ) := Tuple N p × Tuple N p
abbrev Perm (p : ℕ) := Equiv.Perm (Fin p)

/-- The pure tensor power, indexed directly by coordinate tuples. -/
def power (p : ℕ) {N : ℕ} (A : HaarFourthMoments.Mat N) :
    Matrix (Tuple N p) (Tuple N p) ℂ := fun x y => ∏ r, A (x r) (y r)

theorem power_mul (p : ℕ) {N : ℕ} (A B : HaarFourthMoments.Mat N) :
    power p (A*B) = power p A * power p B := by
  ext x y
  simp only [power, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun r k => A (x r) k * B k (y r))

theorem power_conjTranspose (p : ℕ) {N : ℕ} (A : HaarFourthMoments.Mat N) :
    power p Aᴴ = (power p A)ᴴ := by
  ext x y
  simp [power]

theorem power_map_star (p : ℕ) {N : ℕ} (A : HaarFourthMoments.Mat N) :
    power p (A.map (starRingEnd ℂ)) = (power p A).map (starRingEnd ℂ) := by
  ext x y
  simp [power]

/-- The columns are the permutation contraction tensors. -/
def contractions (N p : ℕ) : Matrix (Pair N p) (Perm p) ℂ :=
  fun xy σ => if xy.1 = xy.2 ∘ σ then 1 else 0

/-- Coordinate formula for the mixed tensor representation. -/
def mixed (N p : ℕ) (U : LocalUnitary N) : Matrix (Pair N p) (Pair N p) ℂ :=
  fun xy ab => (∏ r, (U : HaarFourthMoments.Mat N) (xy.1 r) (ab.1 r)) *
    (∏ r, star ((U : HaarFourthMoments.Mat N) (xy.2 r) (ab.2 r)))

lemma prod_delta {ι α : Type*} [Fintype ι] [DecidableEq α] (f g : ι → α) :
    (∏ a, (if f a = g a then (1:ℂ) else 0)) = if f=g then 1 else 0 := by
  classical
  by_cases h : f=g
  · subst g; simp
  · rw [if_neg h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

theorem power_one (N p : ℕ) : power p (1 : HaarFourthMoments.Mat N) = 1 := by
  ext x y
  simpa only [power, Matrix.one_apply] using prod_delta x y

theorem mixed_eq_kronecker (N p : ℕ) (U : LocalUnitary N) :
    mixed N p U = power p (U : HaarFourthMoments.Mat N) ⊗ₖ
      (power p (U : HaarFourthMoments.Mat N)).map (starRingEnd ℂ) := by
  ext xy ab
  simp [mixed, power, map_prod]

theorem mixed_mul (N p : ℕ) (U V : LocalUnitary N) :
    mixed N p (U*V) = mixed N p U * mixed N p V := by
  simp only [mixed_eq_kronecker]
  change power p ((U : HaarFourthMoments.Mat N) * (V : HaarFourthMoments.Mat N)) ⊗ₖ
      (power p ((U : HaarFourthMoments.Mat N) * (V : HaarFourthMoments.Mat N))).map
        (starRingEnd ℂ) = _
  rw [power_mul, Matrix.map_mul, Matrix.mul_kronecker_mul]

theorem mixed_inv (N p : ℕ) (U : LocalUnitary N) :
    mixed N p U⁻¹ = (mixed N p U)ᴴ := by
  simp only [mixed_eq_kronecker]
  change power p (U : HaarFourthMoments.Mat N)ᴴ ⊗ₖ
    (power p (U : HaarFourthMoments.Mat N)ᴴ).map (starRingEnd ℂ) = _
  rw [power_conjTranspose, Matrix.conjTranspose_kronecker]
  congr 1

theorem mixed_average_sq (N p : ℕ) :
    average (mixed N p) * average (mixed N p) = average (mixed N p) := by
  exact average_sq _ (by
    apply continuous_matrix
    intro xy ab
    exact (continuous_finset_prod _ fun r _ => HaarMoments.continuous_entry _ _).mul
      (continuous_finset_prod _ fun r _ => (HaarMoments.continuous_entry _ _).star))
    (mixed_mul N p)

theorem mixed_average_hermitian (N p : ℕ) : (average (mixed N p)).IsHermitian :=
  average_conjTranspose _ (mixed_inv N p)

lemma sum_row_products {N : ℕ} (U : LocalUnitary N) (i j : Fin (N+1)) :
    ∑ k, (U : HaarFourthMoments.Mat N) i k *
      star ((U : HaarFourthMoments.Mat N) j k) = if i=j then 1 else 0 := by
  have hu : (U : HaarFourthMoments.Mat N) *
      (U : HaarFourthMoments.Mat N)ᴴ = 1 :=
    (Unitary.mem_iff.mp U.property).2
  have h := congrFun (congrFun hu i) j
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.one_apply] using h

/-- Every contraction column is fixed by every actual unitary. -/
theorem mixed_mul_contractions (N p : ℕ) (U : LocalUnitary N) :
    mixed N p U * contractions N p = contractions N p := by
  classical
  ext xy σ
  simp only [Matrix.mul_apply, mixed, contractions, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he (b : Tuple N p) :
      (∏ r, (U : HaarFourthMoments.Mat N) (xy.1 r) (b (σ r))) =
      ∏ r, (U : HaarFourthMoments.Mat N) (xy.1 (σ.symm r)) (b r) := by
    simpa using (Equiv.prod_comp σ (fun r =>
      (U : HaarFourthMoments.Mat N) (xy.1 (σ.symm r)) (b r)))
  simp_rw [Function.comp_apply, he, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun r k => (U : HaarFourthMoments.Mat N)
    (xy.1 (σ.symm r)) k * star ((U : HaarFourthMoments.Mat N) (xy.2 r) k))]
  simp_rw [sum_row_products]
  rw [prod_delta]
  congr 1
  apply propext
  constructor
  · intro h
    funext r
    simpa using congrFun h (σ r)
  · intro h
    funext r
    simpa using congrFun h (σ.symm r)

theorem continuous_mixed (N p : ℕ) : Continuous (mixed N p) := by
  apply continuous_matrix
  intro xy ab
  exact (continuous_finset_prod _ fun r _ => HaarMoments.continuous_entry _ _).mul
    (continuous_finset_prod _ fun r _ => (HaarMoments.continuous_entry _ _).star)

/-- Haar integration really fixes the contraction tensors, at every degree. -/
theorem average_mul_contractions (N p : ℕ) :
    average (mixed N p) * contractions N p = contractions N p := by
  ext xy σ
  simp only [Matrix.mul_apply, average]
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum _ (fun ab _ =>
    (integrable_entry (continuous_mixed N p) xy ab).mul_const _)]
  change (∫ U, (mixed N p U * contractions N p) xy σ ∂haar N) = _
  simp_rw [mixed_mul_contractions]
  simp

/-- Equal coordinate multiplicities are exactly equality up to permutation. -/
theorem exists_perm_of_multiplicity_eq {N p : ℕ} (x y : Tuple N p)
    (h : ∀ r, HaarMixedMoments.multiplicity x r = HaarMixedMoments.multiplicity y r) :
    ∃ σ : Perm p, x = y ∘ σ := by
  classical
  have hc (r : Fin (N+1)) : Fintype.card {a // x a=r} = Fintype.card {a // y a=r} := by
    simpa [Fintype.card_subtype, HaarMixedMoments.multiplicity] using h r
  let e (r : Fin (N+1)) := Fintype.equivOfCardEq (hc r)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

/-- The coordinate realization of a matrix as a mixed tensor. -/
def vectorize {N p : ℕ} (T : Matrix (Tuple N p) (Tuple N p) ℂ) : Pair N p → ℂ :=
  fun xy => T xy.1 xy.2

theorem mixed_mulVec_vectorize {N p : ℕ} (U : LocalUnitary N)
    (T : Matrix (Tuple N p) (Tuple N p) ℂ) :
    mixed N p U *ᵥ vectorize T = vectorize
      (power p (U : HaarFourthMoments.Mat N) * T *
        (power p (U : HaarFourthMoments.Mat N))ᴴ) := by
  funext xy
  simp only [Matrix.mulVec, dotProduct, vectorize, mixed_eq_kronecker,
    Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change power p (U : HaarFourthMoments.Mat N) xy.1 b *
    star (power p (U : HaarFourthMoments.Mat N) xy.2 a) * T b a = _
  ring

theorem power_mul_star {N p : ℕ} (U : LocalUnitary N) :
    power p (U : HaarFourthMoments.Mat N) * (power p (U : HaarFourthMoments.Mat N))ᴴ = 1 := by
  rw [← power_conjTranspose, ← power_mul]
  have hu : (U : HaarFourthMoments.Mat N) * (U : HaarFourthMoments.Mat N)ᴴ = 1 :=
    (Unitary.mem_iff.mp U.property).2
  rw [hu, power_one]

theorem power_star_mul {N p : ℕ} (U : LocalUnitary N) :
    (power p (U : HaarFourthMoments.Mat N))ᴴ * power p (U : HaarFourthMoments.Mat N) = 1 := by
  rw [← power_conjTranspose, ← power_mul]
  have hu : (U : HaarFourthMoments.Mat N)ᴴ * (U : HaarFourthMoments.Mat N) = 1 :=
    (Unitary.mem_iff.mp U.property).1
  rw [hu, power_one]

theorem mixed_fixed_iff_commute {N p : ℕ} (U : LocalUnitary N)
    (T : Matrix (Tuple N p) (Tuple N p) ℂ) :
    mixed N p U *ᵥ vectorize T = vectorize T ↔
      power p (U : HaarFourthMoments.Mat N) * T = T * power p (U : HaarFourthMoments.Mat N) := by
  rw [mixed_mulVec_vectorize]
  constructor
  · intro h
    have hm : power p (U : HaarFourthMoments.Mat N) * T *
        (power p (U : HaarFourthMoments.Mat N))ᴴ = T := by
      ext x y
      exact congrFun h (x,y)
    have hr := congrArg (fun M => M * power p (U : HaarFourthMoments.Mat N)) hm
    simpa only [Matrix.mul_assoc, power_star_mul, Matrix.mul_one] using hr
  · intro h
    rw [h, Matrix.mul_assoc, power_mul_star, Matrix.mul_one]

/-- Phase invariance gives the row-support condition on every invariant tensor. -/
theorem invariant_eq_zero_of_multiplicity_ne {N p : ℕ} (v : Pair N p → ℂ)
    (hv : ∀ U : LocalUnitary N, mixed N p U *ᵥ v = v)
    (x y : Tuple N p) (r : Fin (N+1))
    (hr : HaarMixedMoments.multiplicity x r ≠ HaarMixedMoments.multiplicity y r) :
    v (x,y) = 0 := by
  have h := (average_mulVec_eq_iff _ (continuous_mixed N p) (mixed_mul N p) v).mpr hv
  have he (ab : Pair N p) : average (mixed N p) (x,y) ab = 0 := by
    exact HaarMixedMoments.integral_entryMonomial_eq_zero_of_row_mismatch
      x ab.1 y ab.2 r hr
  have hxy := congrFun h (x,y)
  simp only [Matrix.mulVec, dotProduct, he, zero_mul, Finset.sum_const_zero] at hxy
  exact hxy.symm

/-- Rows indexed by distinct coordinates contain an identity submatrix. -/
theorem contractions_injective_row {N p : ℕ} (e : Fin p ↪ Fin (N+1)) (σ τ : Perm p) :
    contractions N p (e ∘ σ, e) τ = if σ=τ then 1 else 0 := by
  unfold contractions
  congr 1
  apply propext
  constructor
  · intro h
    apply Equiv.ext
    intro r
    exact e.injective (congrFun h r)
  · intro h
    subst τ
    rfl

theorem contractions_row_mulVec {N p : ℕ} (e : Fin p ↪ Fin (N+1))
    (c : Perm p → ℂ) (σ : Perm p) :
    (contractions N p *ᵥ c) (e ∘ σ, e) = c σ := by
  simp [Matrix.mulVec, dotProduct, contractions_injective_row]

/-- Every coordinate tensor is a matrix image of a fixed distinct-coordinate tensor.
This works with a possibly singular matrix and needs no density argument. -/
theorem exists_power_column {N p : ℕ} (e : Fin p ↪ Fin (N+1)) (y : Tuple N p) :
    ∃ A : HaarFourthMoments.Mat N, ∀ x : Tuple N p,
      power p A x e = if x=y then 1 else 0 := by
  classical
  let A : HaarFourthMoments.Mat N := fun a b =>
    ∑ r : Fin p, if b=e r then (if a=y r then 1 else 0) else 0
  have ha (a : Fin (N+1)) (r : Fin p) : A a (e r) = if a=y r then 1 else 0 := by
    simp [A, e.injective.eq_iff]
  refine ⟨A, fun x => ?_⟩
  simp only [power, ha]
  exact prod_delta x y

/-- A map commuting with every matrix tensor power is determined by its value
on one tensor of distinct coordinate vectors. -/
theorem eq_zero_of_commute_power_of_column_zero {N p : ℕ}
    (e : Fin p ↪ Fin (N+1)) (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ A : HaarFourthMoments.Mat N, power p A * T = T * power p A)
    (he : ∀ x, T x e = 0) : T = 0 := by
  ext x y
  obtain ⟨A, hA⟩ := exists_power_column e y
  have h := congrFun (congrFun (hT A) x) e
  simpa [Matrix.mul_apply, he, hA] using h.symm

/-- The contraction map is injective throughout the stable range. -/
theorem contractions_mulVec_injective {N p : ℕ} (hp : p ≤ N+1) :
    Function.Injective (contractions N p).mulVec := by
  let e : Fin p ↪ Fin (N+1) := ⟨Fin.castLE hp, Fin.castLE_injective hp⟩
  intro v w h
  funext σ
  have hv := congrFun h (e ∘ σ, e)
  simpa [Matrix.mulVec, dotProduct, contractions_injective_row] using hv

/-- The permutation Gram matrix, before any combinatorial simplification. -/
def gram (N p : ℕ) : Matrix (Perm p) (Perm p) ℂ :=
  (contractions N p)ᴴ * contractions N p

theorem gram_posDef {N p : ℕ} (hp : p ≤ N+1) : (gram N p).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (contractions_mulVec_injective hp)

theorem gram_isUnit {N p : ℕ} (hp : p ≤ N+1) : IsUnit (gram N p) :=
  (gram_posDef hp).isUnit

theorem gram_det_isUnit {N p : ℕ} (hp : p ≤ N+1) : IsUnit (gram N p).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (gram_isUnit hp)

/-- The inverse Gram coefficients exist in every required high-moment range. -/
def weingarten (N p : ℕ) : Matrix (Perm p) (Perm p) ℂ := (gram N p)⁻¹

theorem weingarten_mul_gram {N p : ℕ} (hp : p ≤ N+1) :
    weingarten N p * gram N p = 1 :=
  Matrix.nonsing_inv_mul _ (gram_det_isUnit hp)

theorem gram_mul_weingarten {N p : ℕ} (hp : p ≤ N+1) :
    gram N p * weingarten N p = 1 :=
  Matrix.mul_nonsing_inv _ (gram_det_isUnit hp)

end Nonadditivity.HaarInvariantTensor
