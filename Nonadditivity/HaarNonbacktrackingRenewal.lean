/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktracking
import Nonadditivity.HaarWordExpansion

/-! # Exact finite return-time sums and matrix-word non-returning pieces -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarNonbacktracking

open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator
open HaarWordExpansion RegularCoefficientEnergy

section Operator
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Group G] [DecidableEq G]

theorem killed_vacuum_eq (A T : H G E →L[ℂ] H G E) (n : ℕ) (x : E) :
    killed A T n (vacuum x) =
      (((CollinsYounTensor.mask (E := E) (fun g : G => g ≠ 1) * A) ^ n :
        H G E →L[ℂ] H G E)) (T (vacuum x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [killed, kill_vacuum, ContinuousLinearMap.mul_apply, ih, pow_succ']
      rfl

omit [CompleteSpace E] in
/-- Exact expansion by the time of the first return to the removed vertex. -/
theorem firstReturnSum_eq_sum (A T : H G E →L[ℂ] H G E) (n : ℕ) :
    firstReturnSum A T n = ∑ j ∈ Finset.range n,
      A ^ (n - 1 - j) * liftOperator (returnCoefficient A T j) := by
  induction n with
  | zero => simp [firstReturnSum]
  | succ n ih =>
      rw [firstReturnSum, ih, Finset.mul_sum, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have he : n - j = (n - 1 - j) + 1 := by omega
      rw [he, pow_succ', mul_assoc]

omit [CompleteSpace E] in
/-- A finite first-return identity for actual powers of the operator. -/
theorem first_return_sum_decomposition (A T : H G E →L[ℂ] H G E) (n : ℕ) :
    A ^ n * T = killed A T n + ∑ j ∈ Finset.range n,
      A ^ (n - 1 - j) * liftOperator (returnCoefficient A T j) := by
  rw [first_return_decomposition, firstReturnSum_eq_sum]

/-- Every finite subset of coefficient coordinates has the sharp column energy. -/
theorem killed_coefficient_energy_le (A T : H G E →L[ℂ] H G E) (n : ℕ)
    (s : Finset G) (x : E) :
    ∑ g ∈ s, ‖killed A T n (vacuum x) g‖ ^ 2 ≤
      (‖A‖ ^ n * ‖T‖) ^ 2 * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖killed A T n (vacuum x)‖ ^ 2 := by
      simpa using lp.sum_rpow_le_norm_rpow (by norm_num)
        (killed A T n (vacuum x)) s
    _ ≤ _ := by
      simpa only [mul_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (killed_vacuum_norm_le A T n x) 2

end Operator

section Polynomial

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

/-- The actual finite matrix-coefficient non-returning polynomial recurrence. -/
def killedPolynomial {R : Type*} [Ring R] (A T : MonoidAlgebra R G) : ℕ → MonoidAlgebra R G
  | 0 => T
  | n + 1 => A * killedPolynomial A T n -
      MonoidAlgebra.single 1 ((A * killedPolynomial A T n) 1)

theorem regularEval_single_one (B : Matrix ι ι ℂ) :
    regularEval (G := G) (MonoidAlgebra.single 1 B) = liftOperator (coefficientOperator B) := by
  rw [regularEval_single]
  ext x g i
  simp [RegularFactorization.term, RegularFactorization.rectLift_apply,
    RegularCoefficientEnergy.coefficientOperator]

theorem coefficient_regularEval (f : MatrixPolynomial G ι) :
    coefficient (regularEval f) = coefficientOperator (f 1) := by
  apply ContinuousLinearMap.ext
  intro x
  exact regularEval_vacuum f x

/-- Finite word coefficients agree exactly with the killed-operator recurrence. -/
theorem regularEval_killedPolynomial (A T : MatrixPolynomial G ι) (n : ℕ) :
    regularEval (killedPolynomial A T n) = killed (regularEval A) (regularEval T) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [killedPolynomial, map_sub, regularEval_single_one, ← coefficient_regularEval,
        map_mul, ih]
      rfl

/-- The literal non-returning matrix polynomial has the linear norm loss. -/
theorem killedPolynomial_norm_le (A T : MatrixPolynomial G ι) (n : ℕ) :
    ‖regularEval (killedPolynomial A T n)‖ ≤
      (n + 1 : ℕ) * ‖regularEval A‖ ^ n * ‖regularEval T‖ := by
  rw [regularEval_killedPolynomial]
  exact killed_norm_le _ _ _

theorem regularEval_vacuum_at (f : MatrixPolynomial G ι) (x : CoefficientSpace ι) (g : G) :
    regularEval f (vacuum x) g = coefficientOperator (f g) x := by
  rw [regularEval_eq_regularPolynomial, vacuum_apply, regularPolynomial_single_one]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  by_cases h : g ∈ f.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h, coefficientOperator]

/-- The whole family of literal non-returning coefficients has sharp energy,
without the linear loss in the full polynomial norm. -/
theorem killedPolynomial_coefficient_energy_le (A T : MatrixPolynomial G ι) (n : ℕ)
    (s : Finset G) (x : CoefficientSpace ι) :
    ∑ g ∈ s, ‖coefficientOperator (killedPolynomial A T n g) x‖ ^ 2 ≤
      (‖regularEval A‖ ^ n * ‖regularEval T‖) ^ 2 * ‖x‖ ^ 2 := by
  have h := killed_coefficient_energy_le (regularEval A) (regularEval T) n s x
  simpa only [← regularEval_killedPolynomial, regularEval_vacuum_at] using h

omit [DecidableEq G] in
@[simp] theorem killedPolynomial_succ_one (A T : MatrixPolynomial G ι) (n : ℕ) :
    killedPolynomial A T (n + 1) 1 = 0 := by
  change (A * killedPolynomial A T n) 1 -
    (MonoidAlgebra.single 1 ((A * killedPolynomial A T n) 1)) 1 = 0
  simp

end Polynomial

end Nonadditivity.HaarNonbacktracking
