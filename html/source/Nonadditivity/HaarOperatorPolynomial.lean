/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingLastReturn

/-! # Non-returning polynomials with arbitrary Hilbert-space coefficients

The coefficient ring is the bounded operators on any complete complex Hilbert
space. The regular evaluation, exact last-return identities, coefficient energy,
and full non-returning norm loss therefore remain available during tensor
replacement, when the coefficients include other free regular factors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarOperatorPolynomial

open scoped BigOperators ENNReal
open HaarNonbacktracking RegularCoefficientEnergy

variable {G E : Type*} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Polynomial (G E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  MonoidAlgebra (E →L[ℂ] E) G

def coefficientHom : (E →L[ℂ] E) →+* (H G E →L[ℂ] H G E) where
  toFun := liftOperator
  map_zero' := by ext x g; rfl
  map_one' := by ext x g; rfl
  map_add' A B := by ext x g; rfl
  map_mul' A B := by ext x g; rfl

def wordHom : G →* (H G E →L[ℂ] H G E) where
  toFun := MatrixRegularRestriction.leftRegular
  map_one' := by ext x g; simp
  map_mul' a b := by ext x g; simp [mul_assoc]

def regular : Polynomial G E →+* (H G E →L[ℂ] H G E) :=
  MonoidAlgebra.liftNCRingHom coefficientHom wordHom (by
    intro A g
    change coefficientHom A * wordHom g = wordHom g * coefficientHom A
    ext x h
    rfl)

omit [DecidableEq G] [CompleteSpace E] in
@[simp] theorem regular_single (g : G) (A : E →L[ℂ] E) :
    regular (MonoidAlgebra.single g A) =
      liftOperator A * MatrixRegularRestriction.leftRegular g := by
  rw [regular, MonoidAlgebra.liftNCRingHom_single]
  rfl

omit [DecidableEq G] [CompleteSpace E] in
@[simp] theorem regular_single_one (A : E →L[ℂ] E) :
    regular (MonoidAlgebra.single (1 : G) A) = liftOperator A := by
  rw [regular, MonoidAlgebra.liftNCRingHom_single, map_one, mul_one]
  rfl

omit [DecidableEq G] [CompleteSpace E] in
theorem regular_eq_sum (f : Polynomial G E) :
    regular f = ∑ g ∈ f.support, liftOperator (f g) * MatrixRegularRestriction.leftRegular g := by
  conv_lhs => rw [← MonoidAlgebra.sum_single f]
  change regular (∑ g ∈ f.support, MonoidAlgebra.single g (f g)) = _
  simp only [map_sum, regular_single]

omit [DecidableEq G] [CompleteSpace E] in
@[simp] theorem regular_apply (f : Polynomial G E) (x : H G E) (h : G) :
    regular f x h = ∑ g ∈ f.support, f g (x (g⁻¹ * h)) := by
  rw [regular_eq_sum]
  simp only [ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  rfl

/-- Vacuum coefficients are the literal operator coefficients of the finite sum. -/
theorem regular_vacuum (f : Polynomial G E) (x : E) (g : G) :
    regular f (vacuum x) g = f g x := by
  rw [regular_apply]
  have he (a : G) : a⁻¹ * g = 1 ↔ g = a := by
    rw [inv_mul_eq_one]
    exact eq_comm
  simp only [vacuum_apply, lp.single_apply, Pi.single_apply, he]
  by_cases hg : g ∈ f.support
  · simpa only [apply_ite, map_zero] using
      Finset.sum_ite_eq_of_mem f.support g (fun a => f a x) hg
  · have hz : f g = 0 := Finsupp.notMem_support_iff.mp hg
    simp only [apply_ite, map_zero, hz, ContinuousLinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hga : g ≠ a := by intro heq; exact hg (heq.symm ▸ ha)
    simp [hga]

theorem coefficient_regular (f : Polynomial G E) : coefficient (regular f) = f 1 := by
  ext x
  exact regular_vacuum f x 1

/-- Algebraic and operator non-returning recurrences agree exactly. -/
theorem regular_killed (A T : Polynomial G E) (n : ℕ) :
    regular (killedPolynomial A T n) = killed (regular A) (regular T) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [killedPolynomial, map_sub, regular_single_one, ← coefficient_regular, map_mul, ih]
      rfl

/-- Full non-returning operators incur only the stated linear length factor. -/
theorem killed_norm (A T : Polynomial G E) (n : ℕ) :
    ‖regular (killedPolynomial A T n)‖ ≤
      (n + 1 : ℕ) * ‖regular A‖ ^ n * ‖regular T‖ := by
  rw [regular_killed]
  exact killed_norm_le _ _ _

/-- Non-returning columns have no length loss, in arbitrary coefficient dimension. -/
theorem killed_energy (A T : Polynomial G E) (n : ℕ) (s : Finset G) (x : E) :
    ∑ g ∈ s, ‖killedPolynomial A T n g x‖ ^ 2 ≤
      (‖regular A‖ ^ n * ‖regular T‖) ^ 2 * ‖x‖ ^ 2 := by
  have h := killed_coefficient_energy_le (regular A) (regular T) n s x
  simpa only [← regular_killed, regular_vacuum] using h

/-- Every coefficient is a compression of the regular polynomial. -/
theorem coefficient_norm_le (f : Polynomial G E) (g : G) : ‖f g‖ ≤ ‖regular f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [← regular_vacuum f x g]
  calc
    _ ≤ ‖regular f (vacuum x)‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖regular f‖ * ‖vacuum (G := G) x‖ := (regular f).le_opNorm _
    _ = _ := by rw [vacuum_apply, lp.norm_single (by norm_num)]

omit [DecidableEq G] in
/-- Evaluation at a single regular word is contractive in its coefficient. -/
theorem single_norm_le (g : G) (B : E →L[ℂ] E) :
    ‖regular (MonoidAlgebra.single g B)‖ ≤ ‖B‖ := by
  rw [regular_single]
  calc
    _ ≤ ‖liftOperator (G := G) B‖ * ‖MatrixRegularRestriction.leftRegular g‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖ * 1 := mul_le_mul (lift_norm_le B)
      (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

/-- The distinguished-first-step non-returning polynomial used in BC 3.2. -/
def firstStep (A : Polynomial G E) (a : G) (n : ℕ) : Polynomial G E :=
  killedPolynomial A (MonoidAlgebra.single a (A a)) n

/-- The first-step non-returning factor of total length `n+1` has exactly
that linear length loss, uniformly in the coefficient Hilbert space. -/
theorem firstStep_norm_le (A : Polynomial G E) (a : G) (n : ℕ) :
    ‖regular (firstStep A a n)‖ ≤ (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) := by
  have hs := (single_norm_le a (A a)).trans (coefficient_norm_le A a)
  calc
    _ ≤ (n + 1 : ℕ) * ‖regular A‖ ^ n *
        ‖regular (MonoidAlgebra.single a (A a))‖ := killed_norm _ _ _
    _ ≤ (n + 1 : ℕ) * ‖regular A‖ ^ n * ‖regular A‖ :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- The vacuum-column energy of a distinguished-first-step factor has no
linear length loss. -/
theorem firstStep_energy_le (A : Polynomial G E) (a : G) (n : ℕ)
    (s : Finset G) (x : E) :
    ∑ g ∈ s, ‖firstStep A a n g x‖ ^ 2 ≤ ‖regular A‖ ^ (2 * (n + 1)) * ‖x‖ ^ 2 := by
  have hs := (single_norm_le a (A a)).trans (coefficient_norm_le A a)
  calc
    _ ≤ (‖regular A‖ ^ n * ‖regular (MonoidAlgebra.single a (A a))‖) ^ 2 * ‖x‖ ^ 2 :=
      killed_energy _ _ _ _ _
    _ ≤ (‖regular A‖ ^ n * ‖regular A‖) ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hs (by positivity)) 2)
        (sq_nonneg _)
    _ = _ := by rw [← pow_succ, ← pow_mul, Nat.mul_comm (n + 1) 2]

/-- Individual non-returning first-step coefficients have the sharp power bound. -/
theorem firstStep_coefficient_norm_le (A : Polynomial G E) (a : G) (n : ℕ) (g : G) :
    ‖firstStep A a n g‖ ≤ ‖regular A‖ ^ (n + 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := firstStep_energy_le A a n {g} x
  simpa only [Finset.sum_singleton, mul_pow, ← pow_mul, Nat.mul_comm] using h

end Nonadditivity.HaarOperatorPolynomial
