/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoefficientRows
import Nonadditivity.CollinsYounTensor

/-! # Killed-return operators and the first-return decomposition

The non-returning operators are defined by removing the vacuum coefficient at
each step. Their vacuum columns are literal powers of a killed operator, and
both the sharp column-energy estimate and the linear-in-length full operator
norm estimate follow. Everything is valid for arbitrary Hilbert coefficients.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarNonbacktracking

open scoped BigOperators ENNReal InnerProduct
open RegularCoefficientEnergy (VectorHilbert liftOperator)

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Group G] [DecidableEq G]

abbrev H (G E : Type*) [NormedAddCommGroup E] := VectorHilbert G E

def vacuum : E →L[ℂ] H G E :=
  LinearMap.mkContinuous
    { toFun := fun x : E => (lp.single 2 (1 : G) x : H G E)
      map_add' := by intros; ext g; simp [lp.single_apply, Pi.single_apply]
      map_smul' := by intros; ext g; simp [lp.single_apply, Pi.single_apply] }
    1 (fun x => by simp [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)])

omit [CompleteSpace E] in
@[simp] theorem vacuum_apply (x : E) : vacuum (G := G) x = lp.single 2 (1 : G) x := rfl

def atVacuum : H G E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => x 1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x 1)

omit [CompleteSpace E] [DecidableEq G] in
@[simp] theorem atVacuum_apply (x : H G E) : atVacuum x = x (1 : G) := rfl

/-- The actual matrix coefficient of an operator at the vacuum. -/
def coefficient (T : H G E →L[ℂ] H G E) : E →L[ℂ] E := atVacuum ∘L T ∘L vacuum

omit [CompleteSpace E] in
@[simp] theorem coefficient_apply (T : H G E →L[ℂ] H G E) (x : E) :
    coefficient T x = T (lp.single 2 (1 : G) x) 1 := rfl

def kill (T : H G E →L[ℂ] H G E) : H G E →L[ℂ] H G E :=
  T - liftOperator (coefficient T)

/-- Removing the vacuum coefficient is exactly coordinate killing on each
vacuum column, even though it remains a translation-invariant correction. -/
theorem kill_vacuum (T : H G E →L[ℂ] H G E) (x : E) :
    kill T (vacuum (G := G) x) =
      CollinsYounTensor.mask (fun g : G => g ≠ 1) (T (vacuum x)) := by
  ext g
  simp only [kill, ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    vacuum_apply, RegularCoefficientEnergy.liftOperator_single, coefficient_apply,
    CollinsYounTensor.mask_apply, lp.single_apply, Pi.single_apply]
  by_cases h : g = 1 <;> simp [h]

def killed (A T : H G E →L[ℂ] H G E) : ℕ → H G E →L[ℂ] H G E
  | 0 => T
  | n + 1 => kill (A * killed A T n)

/-- The finite first-return coefficient at each time. -/
def returnCoefficient (A T : H G E →L[ℂ] H G E) (n : ℕ) : E →L[ℂ] E :=
  coefficient (A * killed A T n)

theorem killed_vacuum_norm_le (A T : H G E →L[ℂ] H G E) (n : ℕ) (x : E) :
    ‖killed A T n (vacuum x)‖ ≤ ‖A‖ ^ n * ‖T‖ * ‖x‖ := by
  induction n with
  | zero => simpa [killed, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using T.le_opNorm (vacuum x)
  | succ n ih =>
      rw [killed, kill_vacuum]
      calc
        _ ≤ ‖(A * killed A T n) (vacuum x)‖ := CollinsYounTensor.mask_norm_le _ _
        _ ≤ ‖A‖ * ‖killed A T n (vacuum x)‖ := A.le_opNorm _
        _ ≤ ‖A‖ * (‖A‖ ^ n * ‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg A)
        _ = _ := by rw [pow_succ]; ring

/-- The return correction has the sharp energy norm, without the linear factor
that occurs in the full non-returning operator norm. -/
theorem returnCoefficient_norm_le (A T : H G E →L[ℂ] H G E) (n : ℕ) :
    ‖returnCoefficient A T n‖ ≤ ‖A‖ ^ (n + 1) * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    _ ≤ ‖(A * killed A T n) (vacuum x)‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖A‖ * ‖killed A T n (vacuum x)‖ := A.le_opNorm _
    _ ≤ ‖A‖ * (‖A‖ ^ n * ‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (killed_vacuum_norm_le A T n x) (norm_nonneg A)
    _ = _ := by rw [pow_succ]; ring

omit [CompleteSpace E] [Group G] [DecidableEq G] in
theorem lift_norm_le (B : E →L[ℂ] E) : ‖liftOperator (G := G) B‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (RegularCoefficientEnergy.liftFunction_norm_le B)

/-- The Bordenave--Collins linear loss for non-returning pieces follows from
the actual killed-return recurrence. -/
theorem killed_norm_le (A T : H G E →L[ℂ] H G E) (n : ℕ) :
    ‖killed A T n‖ ≤ (n + 1 : ℕ) * ‖A‖ ^ n * ‖T‖ := by
  induction n with
  | zero => simp [killed]
  | succ n ih =>
      calc
        _ ≤ ‖A * killed A T n‖ + ‖liftOperator (returnCoefficient A T n)‖ := by
          change ‖A * killed A T n - liftOperator (returnCoefficient A T n)‖ ≤ _
          exact norm_sub_le (A * killed A T n) (liftOperator (returnCoefficient A T n))
        _ ≤ ‖A‖ * ‖killed A T n‖ + ‖returnCoefficient A T n‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le A (killed A T n)) (lift_norm_le _)
        _ ≤ ‖A‖ * ((n + 1 : ℕ) * ‖A‖ ^ n * ‖T‖) + ‖A‖ ^ (n + 1) * ‖T‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg A)) (returnCoefficient_norm_le A T n)
        _ = _ := by push_cast; rw [pow_succ]; ring

/-- The first-return remainder is a literal sum of propagated return coefficients. -/
def firstReturnSum (A T : H G E →L[ℂ] H G E) : ℕ → H G E →L[ℂ] H G E
  | 0 => 0
  | n + 1 => A * firstReturnSum A T n + liftOperator (returnCoefficient A T n)

omit [CompleteSpace E] in
/-- Every ordinary walk is either non-returning or has a first return.
This algebraic identity is proved for the actual operators. -/
theorem first_return_decomposition (A T : H G E →L[ℂ] H G E) (n : ℕ) :
    A ^ n * T = killed A T n + firstReturnSum A T n := by
  induction n with
  | zero => simp [killed, firstReturnSum]
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, mul_add, killed, firstReturnSum, kill, returnCoefficient]
      abel

end Nonadditivity.HaarNonbacktracking
