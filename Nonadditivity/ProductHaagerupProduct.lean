/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductHaagerupIndex
import Nonadditivity.RegularFubini

/-! # Product free-group Haagerup inequality with operator coefficients

The construction uses actual square-summable functions on a product group.
Currying intertwines the bounded regular polynomials exactly.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.ProductHaagerupProduct
open scoped BigOperators InnerProductSpace
open RegularCoefficientEnergy (VectorHilbert liftOperator)
open ProductHaagerupBall (BallWords)

variable {α E : Type*} [DecidableEq α] [Fintype α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def polynomial {q j : ℕ} (B : WordIndex α q j → E →L[ℂ] E) :
    VectorHilbert (GroupIndex α j) E →L[ℂ] VectorHilbert (GroupIndex α j) E :=
  ∑ w, (liftOperator (B w)).comp (MatrixRegularRestriction.leftRegular (wordValue w))

def energy {q j : ℕ} (B : WordIndex α q j → E →L[ℂ] E) : ℝ := ∑ w, ‖B w‖ ^ 2

omit [DecidableEq α] [CompleteSpace E] in
@[simp] theorem polynomial_zero {q j : ℕ} :
    polynomial (0 : WordIndex α q j → E →L[ℂ] E) = 0 := by
  ext f x
  simp [polynomial]

omit [DecidableEq α] [CompleteSpace E] in
/-- Fubini intertwines the product polynomial with a first-coordinate
polynomial whose coefficients are the remaining product polynomials. -/
theorem curry_polynomial {q j : ℕ} (B : WordIndex α q (j+1) → E →L[ℂ] E)
    (f : VectorHilbert (GroupIndex α (j+1)) E) :
    RegularFubini.curry (polynomial B f) =
      ProductHaagerupBall.polynomial (fun w => polynomial (fun v => B (w,v)))
        (RegularFubini.curry f) := by
  ext x y
  simp only [polynomial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    RegularFubini.curry_apply, lp.coeFn_sum, Finset.sum_apply,
    RegularCoefficientEnergy.liftOperator_apply, MatrixRegularRestriction.leftRegular_apply,
    ProductHaagerupBall.polynomial, ProductHaagerupHomogeneous.polynomial]
  change (∑ w : BallWords α q × WordIndex α q j,
    B w (f ((FreeGroup.mk w.1.2.1)⁻¹ * x, (wordValue w.2)⁻¹ * y))) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma]

omit [DecidableEq α] [CompleteSpace E] in
/-- The intertwining is an equality of the actual operator norms. -/
theorem polynomial_norm_succ {q j : ℕ} (B : WordIndex α q (j+1) → E →L[ℂ] E) :
    ‖polynomial B‖ =
      ‖ProductHaagerupBall.polynomial (fun w => polynomial (fun v => B (w,v)))‖ := by
  let T := ProductHaagerupBall.polynomial (fun w => polynomial (fun v => B (w,v)))
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (polynomial B) (norm_nonneg T)
    intro f
    rw [← RegularFubini.curry_norm, curry_polynomial]
    exact (T.le_opNorm _).trans_eq (by rw [RegularFubini.curry_norm])
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (polynomial B))
    intro f
    have hh := curry_polynomial B (RegularFubini.uncurry f)
    have he : RegularFubini.curry (RegularFubini.uncurry f) = f := by ext x y; rfl
    rw [he] at hh
    rw [← hh, RegularFubini.curry_norm]
    exact ((polynomial B).le_opNorm _).trans_eq (by
      have hn := RegularFubini.curry_norm (RegularFubini.uncurry f)
      rw [he] at hn
      rw [← hn])

/-- The product rapid-decay bound with the exact polynomial radius growth
needed by the growing-moment argument. -/
theorem polynomial_norm_sq_le {q j : ℕ} (B : WordIndex α q j → E →L[ℂ] E)
    (hred : ∀ w, ¬ reduced w → B w = 0) :
    ‖polynomial B‖ ^ 2 ≤ ((q+1 : ℕ) : ℝ)^(3*j) * energy B := by
  induction j with
  | zero =>
    letI : Unique (WordIndex α q 0) := inferInstanceAs (Unique PUnit)
    letI : Unique (GroupIndex α 0) := inferInstanceAs (Unique PUnit)
    have hn : ‖polynomial B‖ ≤ ‖B PUnit.unit‖ := by
      apply ContinuousLinearMap.opNorm_le_bound (polynomial B) (norm_nonneg (B PUnit.unit))
      intro f
      have he : polynomial B f = liftOperator (B PUnit.unit) f := by
        ext x
        cases x
        simp [polynomial, wordValue, MatrixRegularRestriction.leftRegular_apply]
        rfl
      rw [he]
      exact RegularCoefficientEnergy.liftFunction_norm_le _ _
    simpa [energy] using pow_le_pow_left₀ (norm_nonneg (polynomial B)) hn 2
  | succ j ih =>
    rw [polynomial_norm_succ]
    have hout : ∀ w : BallWords α q, ¬ FreeGroup.IsReduced w.2.1 →
        polynomial (fun v => B (w,v)) = 0 := by
      intro w hw
      have hz : (fun v => B (w,v)) = 0 := by
        funext v
        exact hred (w,v) (fun h => hw h.1)
      rw [hz, polynomial_zero]
    apply (ProductHaagerupBall.polynomial_norm_sq_le _ hout).trans
    have hi (w : BallWords α q) : ‖polynomial (fun v => B (w,v))‖^2 ≤
        ((q+1 : ℕ) : ℝ)^(3*j) * energy (fun v => B (w,v)) :=
      ih _ (fun v hv => hred (w,v) (fun h => hv h.2))
    unfold ProductHaagerupBall.energy
    calc
      _ ≤ ((q+1 : ℕ) : ℝ)^3 *
          ∑ w : BallWords α q, ((q+1 : ℕ) : ℝ)^(3*j) * energy (fun v => B (w,v)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun w _ => hi w)) (by positivity)
      _ = _ := by
        rw [← Finset.mul_sum]
        have he : (∑ w : BallWords α q, energy (fun v => B (w,v))) = energy B := by
          exact (Fintype.sum_prod_type
            (fun w : BallWords α q × WordIndex α q j => ‖B w‖ ^ 2)).symm
        rw [he, ← mul_assoc, ← pow_add]
        congr 1
        congr 1
        omega


/-- Coordinate-radius bound for any finitely supported actual regular
polynomial, with arbitrary bounded Hilbert-space operator coefficients. -/
theorem finite_polynomial_norm_sq_le {q j : ℕ}
    (S : Finset (GroupIndex α j)) (B : GroupIndex α j → E →L[ℂ] E)
    (hS : ∀ g ∈ S, RadiusLe q g) :
    ‖∑ g ∈ S, (liftOperator (B g)).comp (MatrixRegularRestriction.leftRegular g)‖ ^ 2 ≤
      ((q+1 : ℕ) : ℝ)^(3*j) * ∑ g ∈ S, ‖B g‖ ^ 2 := by
  classical
  let a : WordIndex α q j → E →L[ℂ] E := fun w =>
    if reduced w ∧ wordValue w ∈ S then B (wordValue w) else 0
  have hpoly : polynomial a =
      ∑ g ∈ S, (liftOperator (B g)).comp (MatrixRegularRestriction.leftRegular g) := by
    rw [← sum_reduced_wordIndex S hS (fun g =>
      (liftOperator (B g)).comp (MatrixRegularRestriction.leftRegular g))]
    unfold polynomial
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : reduced w ∧ wordValue w ∈ S
    · simp [a, h]
    · simp only [a, if_neg h]
      ext f x
      simp
  have he : energy a = ∑ g ∈ S, ‖B g‖ ^ 2 := by
    rw [← sum_reduced_wordIndex S hS (fun g => ‖B g‖ ^ 2)]
    unfold energy
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : reduced w ∧ wordValue w ∈ S <;> simp [a, h]
  have hb := polynomial_norm_sq_le a (fun w hw => by simp [a, hw])
  rwa [hpoly, he] at hb

end Nonadditivity.ProductHaagerupProduct
