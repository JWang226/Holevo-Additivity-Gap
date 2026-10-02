/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularRestriction
import Nonadditivity.RegularCoefficientEnergy

/-! # Matrix coefficient regular norms under group embeddings

Coset energy decomposition and extension by zero prove complete norm preservation:
the coefficient space can be any complex normed space and the coefficients any
bounded linear operators. The final theorem specializes to the literal finite
matrix coefficient polynomial from `RegularCoefficientEnergy`.
-/

noncomputable section

namespace Nonadditivity.MatrixRegularRestriction

open scoped BigOperators ENNReal
open Nonadditivity.RegularRestriction (RightCosets rightCosetEquiv)
open Nonadditivity.RegularCoefficientEnergy (VectorHilbert)

set_option maxHeartbeats 800000

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem norm_sq {α : Type*} (f : VectorHilbert α E) :
    ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f

/-- Restriction to one right coset, identified with the subgroup. -/
def cosetSlice (H : Subgroup G) (q : RightCosets H) (f : VectorHilbert G E) : VectorHilbert H E :=
  ⟨fun h => f (rightCosetEquiv H (q, h)), by
    apply memℓp_gen
    exact (f.property.summable (by norm_num)).comp_injective (by
      intro a b heq
      exact (Prod.mk.inj (rightCosetEquiv H |>.injective heq)).2)⟩

omit [NormedSpace ℂ E] in
@[simp] theorem cosetSlice_apply (H : Subgroup G) (q : RightCosets H)
    (f : VectorHilbert G E) (h : H) : cosetSlice H q f h = f ((h : G) * q.out) := rfl

omit [NormedSpace ℂ E] in
/-- The square norm splits exactly as the sum of the square norms on right cosets. -/
theorem coset_energy (H : Subgroup G) (f : VectorHilbert G E) :
    ‖f‖ ^ 2 = ∑' q : RightCosets H, ‖cosetSlice H q f‖ ^ 2 := by
  rw [norm_sq, ← (rightCosetEquiv H).tsum_eq (fun x => ‖f x‖ ^ 2)]
  have hs : Summable (fun p : RightCosets H × H => ‖f (rightCosetEquiv H p)‖ ^ 2) :=
    (rightCosetEquiv H).summable_iff (f := fun x => ‖f x‖ ^ 2) |>.mpr
      (by simpa using f.property.summable (by norm_num))
  rw [hs.tsum_prod]
  apply tsum_congr
  intro q
  exact (norm_sq (cosetSlice H q f)).symm

omit [NormedSpace ℂ E] in
theorem summable_coset_energy (H : Subgroup G) (f : VectorHilbert G E) :
    Summable (fun q : RightCosets H => ‖cosetSlice H q f‖ ^ 2) := by
  have hs : Summable (fun p : RightCosets H × H => ‖f (rightCosetEquiv H p)‖ ^ 2) :=
    (rightCosetEquiv H).summable_iff (f := fun x => ‖f x‖ ^ 2) |>.mpr
      (by simpa using f.property.summable (by norm_num))
  convert hs.prod using 1
  funext q
  exact norm_sq (cosetSlice H q f)

/-- The vector-valued regular shift. -/
def leftRegular {α : Type*} [Group α] (g : α) :
    VectorHilbert α E →L[ℂ] VectorHilbert α E :=
  (RegularCoefficientEnergy.reindexIsometry (E := E) (Equiv.mulLeft g⁻¹)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem leftRegular_apply {α : Type*} [Group α] (g : α)
    (f : VectorHilbert α E) (h : α) : leftRegular g f h = f (g⁻¹ * h) := rfl

/-- A finite polynomial with arbitrary bounded operator coefficients. -/
def coefficientPolynomial {α : Type*} [Group α] {I : Type*} [Fintype I]
    (w : I → α) (a : I → E →L[ℂ] E) : VectorHilbert α E →L[ℂ] VectorHilbert α E :=
  ∑ i, (RegularCoefficientEnergy.liftOperator (a i)).comp (leftRegular (w i))

@[simp] theorem coefficientPolynomial_apply {α : Type*} [Group α] {I : Type*} [Fintype I]
    (w : I → α) (a : I → E →L[ℂ] E) (f : VectorHilbert α E) (x : α) :
    coefficientPolynomial w a f x = ∑ i, a i (f ((w i)⁻¹ * x)) := by
  simp only [coefficientPolynomial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply]

/-- The restricted operator acts identically on every right coset. -/
theorem cosetSlice_coefficientPolynomial (H : Subgroup G) {I : Type*} [Fintype I]
    (w : I → H) (a : I → E →L[ℂ] E) (q : RightCosets H) (f : VectorHilbert G E) :
    cosetSlice H q (coefficientPolynomial (fun i => (w i : G)) a f) =
      coefficientPolynomial w a (cosetSlice H q f) := by
  ext h
  simp [mul_assoc]

/-- The ambient regular norm cannot exceed the subgroup regular norm. -/
theorem coefficientPolynomial_subgroup_norm_le (H : Subgroup G) {I : Type*} [Fintype I]
    (w : I → H) (a : I → E →L[ℂ] E) :
    ‖coefficientPolynomial (fun i => (w i : G)) a‖ ≤ ‖coefficientPolynomial w a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [coset_energy H, mul_pow, coset_energy H,
    ← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro q
    rw [cosetSlice_coefficientPolynomial]
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        ((coefficientPolynomial w a).le_opNorm (cosetSlice H q f))
  · exact summable_coset_energy H _
  · exact (summable_coset_energy H f).mul_left _

/-- Extension by zero through an injection is an actual square-summable function. -/
def extendZero {α β : Type*} (j : α → β) (hj : Function.Injective j)
    (f : VectorHilbert α E) : VectorHilbert β E :=
  ⟨Function.extend j f 0, by
    apply memℓp_gen
    have hs := (summable_extend_zero hj).mpr (f.property.summable (by norm_num))
    convert hs using 1
    funext y
    simpa [Function.comp_def] using
      Function.apply_extend (g := (⇑f)) (fun z : E => ‖z‖ ^ (2 : ℝ≥0∞).toReal) j (0 : β → E) y⟩

omit [NormedSpace ℂ E] in
@[simp] theorem extendZero_apply_image {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : VectorHilbert α E) (x : α) :
    extendZero j hj f (j x) = f x := hj.extend_apply _ _ _

omit [NormedSpace ℂ E] in
theorem extendZero_apply_outside {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : VectorHilbert α E) (x : β) (hx : x ∉ Set.range j) :
    extendZero j hj f x = 0 := Function.extend_apply' _ _ _ hx

omit [NormedSpace ℂ E] in
/-- Extension by zero preserves the Hilbert norm exactly. -/
theorem extendZero_norm {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : VectorHilbert α E) : ‖extendZero j hj f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq, norm_sq]
  have heq : (fun y => ‖extendZero j hj f y‖ ^ 2) =
      Function.extend j (fun x => ‖f x‖ ^ 2) 0 := by
    funext y
    simpa [extendZero, Function.comp_def] using
      Function.apply_extend (g := (⇑f)) (fun z : E => ‖z‖ ^ (2 : ℕ)) j (0 : β → E) y
  rw [heq, tsum_extend_zero hj]

/-- Extension by zero intertwines a finite polynomial along any group embedding. -/
theorem extendZero_coefficientPolynomial {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {I : Type*} [Fintype I]
    (w : I → H) (a : I → E →L[ℂ] E) (f : VectorHilbert H E) :
    coefficientPolynomial (fun i => φ (w i)) a (extendZero φ hφ f) =
      extendZero φ hφ (coefficientPolynomial w a f) := by
  classical
  ext g
  by_cases hg : g ∈ Set.range φ
  · obtain ⟨h, rfl⟩ := hg
    rw [extendZero_apply_image]
    simp only [coefficientPolynomial_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← map_inv, ← map_mul, extendZero_apply_image]
  · rw [extendZero_apply_outside _ _ _ _ hg, coefficientPolynomial_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hm : (φ (w i))⁻¹ * g ∉ Set.range φ := by
      rintro ⟨h, hh⟩
      apply hg
      refine ⟨w i * h, ?_⟩
      rw [map_mul, hh]
      simp
    rw [extendZero_apply_outside _ _ _ _ hm, map_zero]

/-- The regular polynomial on an embedded group has at least the original norm. -/
theorem coefficientPolynomial_norm_le_of_injective {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {I : Type*} [Fintype I] (w : I → H) (a : I → E →L[ℂ] E) :
    ‖coefficientPolynomial w a‖ ≤ ‖coefficientPolynomial (fun i => φ (w i)) a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have hb := (coefficientPolynomial (fun i => φ (w i)) a).le_opNorm (extendZero φ hφ f)
  rw [extendZero_coefficientPolynomial, extendZero_norm, extendZero_norm] at hb
  exact hb

/-- An injective group homomorphism preserves every finite regular polynomial norm.
The proof uses actual square-summable right coset fibers and extension by zero. -/
theorem coefficientPolynomial_injective_norm_eq {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {I : Type*} [Fintype I] (w : I → H) (a : I → E →L[ℂ] E) :
    ‖coefficientPolynomial (fun i => φ (w i)) a‖ = ‖coefficientPolynomial w a‖ := by
  let e : H ≃* φ.range := MonoidHom.ofInjective hφ
  apply le_antisymm
  · calc
      ‖coefficientPolynomial (fun i => φ (w i)) a‖ =
          ‖coefficientPolynomial (fun i => (e (w i) : G)) a‖ := rfl
      _ ≤ ‖coefficientPolynomial (fun i => e (w i)) a‖ :=
        coefficientPolynomial_subgroup_norm_le φ.range _ a
      _ ≤ ‖coefficientPolynomial w a‖ := by
        simpa using coefficientPolynomial_norm_le_of_injective e.symm.toMonoidHom
          e.symm.injective (fun i => e (w i)) a
  · exact coefficientPolynomial_norm_le_of_injective φ hφ w a

/-- Group isomorphisms preserve every operator-coefficient polynomial norm. -/
theorem coefficientPolynomial_equiv_norm_eq {H : Type*} [Group H] (e : H ≃* G)
    {I : Type*} [Fintype I] (w : I → H) (a : I → E →L[ℂ] E) :
    ‖coefficientPolynomial (fun i => e (w i)) a‖ = ‖coefficientPolynomial w a‖ :=
  coefficientPolynomial_injective_norm_eq e.toMonoidHom e.injective w a

section Matrix

variable [DecidableEq G] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq G] in
/-- The generic coefficient polynomial specializes to the literal matrix polynomial. -/
theorem matrixPolynomial_eq (S : Finset G) (c : G → Matrix ι ι ℂ) :
    RegularCoefficientEnergy.regularPolynomial S c =
      coefficientPolynomial (fun w : S => w.val)
        (fun w => RegularCoefficientEnergy.coefficientOperator (c w.val)) := by
  simp only [RegularCoefficientEnergy.regularPolynomial, coefficientPolynomial]
  rw [← Finset.sum_coe_sort S (fun w =>
    (RegularCoefficientEnergy.liftOperator (RegularCoefficientEnergy.coefficientOperator (c w))).comp
      (RegularCoefficientEnergy.leftRegular w))]
  rfl

/-- Injective support reindexing keeps each matrix coefficient at its original word. -/
theorem matrixPolynomial_image_eq {H : Type*} [Group H] [DecidableEq H]
    (φ : H →* G) (hφ : Function.Injective φ) (S : Finset H) (c : H → Matrix ι ι ℂ) :
    RegularCoefficientEnergy.regularPolynomial (S.image φ) (Function.extend φ c 0) =
      coefficientPolynomial (fun w : S => φ w.val)
        (fun w => RegularCoefficientEnergy.coefficientOperator (c w.val)) := by
  simp only [RegularCoefficientEnergy.regularPolynomial, coefficientPolynomial]
  rw [Finset.sum_image hφ.injOn]
  simp only [hφ.extend_apply]
  rw [← Finset.sum_coe_sort S (fun w =>
    (RegularCoefficientEnergy.liftOperator (RegularCoefficientEnergy.coefficientOperator (c w))).comp
      (RegularCoefficientEnergy.leftRegular (φ w)))]
  rfl

/-- Complete norm preservation for the concrete matrix coefficient regular polynomial.
There is no bound on the matrix dimension and no analytic comparison hypothesis. -/
theorem matrixPolynomial_injective_norm_eq {H : Type*} [Group H] [DecidableEq H]
    (φ : H →* G) (hφ : Function.Injective φ) (S : Finset H) (c : H → Matrix ι ι ℂ) :
    ‖RegularCoefficientEnergy.regularPolynomial (S.image φ) (Function.extend φ c 0)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial S c‖ := by
  rw [matrixPolynomial_image_eq φ hφ S c, matrixPolynomial_eq S c]
  exact coefficientPolynomial_injective_norm_eq φ hφ _ _

end Matrix

end Nonadditivity.MatrixRegularRestriction
