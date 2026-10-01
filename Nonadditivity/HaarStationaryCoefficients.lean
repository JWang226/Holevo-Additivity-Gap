/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingRenewal
import Nonadditivity.NoncommutativeCSPaths

/-! # Actual coefficient bounds for stationary killed-return operators

Coefficients may act on any complete complex Hilbert space, including already
free tensor factors. Translation invariance is proved for regular polynomials
and preserved by the killed-return recurrence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarNonbacktracking
open scoped BigOperators ENNReal InnerProduct
open RegularCoefficientEnergy NoncommutativeCS

variable {G E J : Type*} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype J]

def rightShift (g : G) : H G E →L[ℂ] H G E :=
  (reindexIsometry (E := E) (Equiv.mulRight g)).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq G] [CompleteSpace E] in
@[simp] theorem rightShift_apply (g h : G) (x : H G E) :
    rightShift g x h = x (h*g) := rfl

def IsStationary (T : H G E →L[ℂ] H G E) : Prop :=
  ∀ g : G, T ∘L rightShift g = rightShift g ∘L T

omit [DecidableEq G] [CompleteSpace E] in
theorem stationary_regularPolynomial (w : J → G) (A : J → E →L[ℂ] E) :
    IsStationary (MatrixRegularRestriction.coefficientPolynomial w A) := by
  intro g
  ext x h
  simp only [ContinuousLinearMap.comp_apply,
    MatrixRegularRestriction.coefficientPolynomial_apply, rightShift_apply, mul_assoc]

omit [DecidableEq G] [CompleteSpace E] in
theorem stationary_lift (B : E →L[ℂ] E) : IsStationary (liftOperator (G := G) B) := by
  intro g
  ext x h
  rfl

omit [DecidableEq G] [CompleteSpace E] in
theorem IsStationary.sub {A B : H G E →L[ℂ] H G E}
    (hA : IsStationary A) (hB : IsStationary B) : IsStationary (A-B) := by
  intro g
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hA g, hB g]

omit [DecidableEq G] [CompleteSpace E] in
theorem IsStationary.mul {A B : H G E →L[ℂ] H G E}
    (hA : IsStationary A) (hB : IsStationary B) : IsStationary (A*B) := by
  intro g
  change (A ∘L B) ∘L rightShift g = rightShift g ∘L (A ∘L B)
  rw [ContinuousLinearMap.comp_assoc, hB g, ← ContinuousLinearMap.comp_assoc,
    hA g, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
theorem IsStationary.kill {T : H G E →L[ℂ] H G E} (hT : IsStationary T) :
    IsStationary (kill T) := hT.sub (stationary_lift _)

omit [CompleteSpace E] in
theorem IsStationary.killed {A T : H G E →L[ℂ] H G E}
    (hA : IsStationary A) (hT : IsStationary T) (r : ℕ) :
    IsStationary (killed A T r) := by
  induction r with
  | zero => exact hT
  | succ r ih => exact (hA.mul ih).kill

/-- The actual coefficient in the column at the group identity. -/
def wordCoefficient (T : H G E →L[ℂ] H G E) (g : G) : E →L[ℂ] E :=
  (atVacuum ∘L rightShift g) ∘L T ∘L vacuum

omit [CompleteSpace E] in
@[simp] theorem wordCoefficient_apply (T : H G E →L[ℂ] H G E) (g : G) (x : E) :
    wordCoefficient T g x = T (vacuum x) g := by
  simp [wordCoefficient]

omit [CompleteSpace E] in
theorem rightShift_vacuum (g : G) (x : E) :
    rightShift g (vacuum x) = lp.single 2 g⁻¹ x := by
  ext h
  simp only [rightShift_apply, vacuum_apply, lp.single_apply, Pi.single_apply]
  have he : h*g=1 ↔ h=g⁻¹ := mul_eq_one_iff_eq_inv
  simp only [he]

omit [CompleteSpace E] in
theorem stationary_coefficient_at_one {T : H G E →L[ℂ] H G E}
    (hT : IsStationary T) (g : G) (x : E) :
    T (lp.single 2 g⁻¹ x) 1 = wordCoefficient T g x := by
  rw [← rightShift_vacuum]
  have h := congrArg (fun F : H G E →L[ℂ] H G E => F (vacuum x) 1) (hT g)
  simpa only [ContinuousLinearMap.comp_apply, rightShift_apply, one_mul,
    wordCoefficient_apply] using h

/-- A vector with distinct, prescribed group coordinates. -/
def packet (w : J → G) (x : DirectSum J E) : H G E :=
  ∑ j, lp.single 2 (w j) (x j)

omit [Group G] [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem packet_norm (w : J → G) (hw : Function.Injective w) (x : DirectSum J E) :
    ‖packet w x‖ = ‖x‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs := lp.norm_sum_single (p := 2) (by norm_num)
    (Function.extend w (fun j => x j) 0) (Finset.univ.image w)
  simpa only [packet, ENNReal.toReal_ofNat, Real.rpow_two,
    Finset.sum_image hw.injOn, hw.extend_apply, PiLp.norm_sq_eq_of_L2] using hs

/-- A row of genuine coefficients is a compression of the stationary operator.
Injectivity is only the literal distinctness of the selected group words. -/
theorem stationary_coefficient_row_norm_le {T : H G E →L[ℂ] H G E}
    (hT : IsStationary T) (w : J → G) (hw : Function.Injective w) :
    ‖row (fun j => wordCoefficient T (w j))‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he : row (fun j => wordCoefficient T (w j)) x =
      T (packet (fun j => (w j)⁻¹) x) 1 := by
    simp only [row_apply, packet, map_sum, lp.coeFn_sum, Finset.sum_apply,
      stationary_coefficient_at_one hT]
  rw [he]
  calc
    _ ≤ ‖T (packet (fun j => (w j)⁻¹) x)‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖T‖ * ‖packet (fun j => (w j)⁻¹) x‖ := T.le_opNorm _
    _ = _ := by rw [packet_norm _ (fun i j h => hw (inv_injective h))]

/-- Sharp column bound for the actual non-returning coefficients. -/
theorem killed_coefficient_column_norm_le (A T : H G E →L[ℂ] H G E)
    (r : ℕ) (w : J → G) (hw : Function.Injective w) :
    ‖column (fun j => wordCoefficient (killed A T r) (w j))‖ ≤ ‖A‖^r * ‖T‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow]
  have hb := killed_coefficient_energy_le A T r (Finset.univ.image w) x
  simpa only [column_apply, wordCoefficient_apply, Finset.sum_image hw.injOn] using hb

/-- Each middle coefficient has no loss in the time parameter. -/
theorem killed_wordCoefficient_norm_le (A T : H G E →L[ℂ] H G E)
    (r : ℕ) (g : G) :
    ‖wordCoefficient (killed A T r) g‖ ≤ ‖A‖^r * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [wordCoefficient_apply]
  exact (lp.norm_apply_le_norm (by norm_num) (killed A T r (vacuum x)) g).trans
    (killed_vacuum_norm_le A T r x)

/-- Row bounds have only the proved linear time loss, uniformly over coefficient
Hilbert spaces and all selected subsets of group words. -/
theorem killed_coefficient_row_norm_le {A T : H G E →L[ℂ] H G E}
    (hA : IsStationary A) (hT : IsStationary T)
    (r : ℕ) (w : J → G) (hw : Function.Injective w) :
    ‖row (fun j => wordCoefficient (killed A T r) (w j))‖ ≤
      (r+1:ℕ) * ‖A‖^r * ‖T‖ :=
  (stationary_coefficient_row_norm_le (hA.killed hT r) w hw).trans (killed_norm_le A T r)

end Nonadditivity.HaarNonbacktracking
