/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarBranchCoefficients

/-! # Constrained sums of actual non-returning coefficients

A schedule records when a chain label is first seen, retained, and last seen.
Its evaluation is the literal finite path sum, including crossing pairs.
Every operator bound is derived from the original regular operator.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarNonbacktracking
open scoped BigOperators InnerProduct
open NoncommutativeCS

/-- Register operations with concrete first-letter and endpoint word data. -/
inductive BranchPlan (G J : Type*) : ℕ → ℕ → Type _
  | identity (n : ℕ) : BranchPlan G J n n
  | openReg {n : ℕ} (p : Fin (n+1)) (g : G) (r : ℕ)
      (w : J → G) (hw : Function.Injective w) : BranchPlan G J n (n+1)
  | closeReg {n : ℕ} (p : Fin (n+1)) (g : G) (r : ℕ)
      (w : J → G) (hw : Function.Injective w) : BranchPlan G J (n+1) n
  | middle (n : ℕ) (g : G) (r : ℕ) (w : (Fin n → J) → G) : BranchPlan G J n n
  | singleton (n : ℕ) (g : G) (r : ℕ) (w : J → G)
      (hw : Function.Injective w) : BranchPlan G J n n
  | comp {l m n : ℕ} (Q : BranchPlan G J m n) (P : BranchPlan G J l m) :
      BranchPlan G J l n

namespace BranchPlan
variable {G J : Type*} {m n : ℕ}

def order {m n : ℕ} : BranchPlan G J m n → ℕ
  | .identity _ => 0
  | .openReg _ _ r _ _ => r+1
  | .closeReg _ _ r _ _ => r+1
  | .middle _ _ r _ => r+1
  | .singleton _ _ r _ _ => r+1
  | .comp Q P => Q.order + P.order

def marked {m n : ℕ} : BranchPlan G J m n → ℕ
  | .identity _ => 0
  | .openReg _ _ _ _ _ => 1
  | .closeReg _ _ _ _ _ => 1
  | .middle _ _ _ _ => 0
  | .singleton _ _ _ _ _ => 1
  | .comp Q P => Q.marked + P.marked

def singletons {m n : ℕ} : BranchPlan G J m n → ℕ
  | .identity _ => 0
  | .openReg _ _ _ _ _ => 0
  | .closeReg _ _ _ _ _ => 0
  | .middle _ _ _ _ => 0
  | .singleton _ _ _ _ _ => 1
  | .comp Q P => Q.singletons + P.singletons

def timeWeight {m n : ℕ} : BranchPlan G J m n → ℕ
  | .identity _ => 1
  | .openReg _ _ r _ _ => r+1
  | .closeReg _ _ r _ _ => r+1
  | .middle _ _ _ _ => 1
  | .singleton _ _ r _ _ => r+1
  | .comp Q P => Q.timeWeight * P.timeWeight

/-- Only marked first/last visits incur time factors. -/
theorem timeWeight_le (P : BranchPlan G J m n) (L : ℕ) (hL : P.order ≤ L) :
    P.timeWeight ≤ L^P.marked := by
  induction P with
  | identity => simp [timeWeight, marked]
  | openReg p g r w hw => simpa [timeWeight, marked] using hL
  | closeReg p g r w hw => simpa [timeWeight, marked] using hL
  | middle => simp [timeWeight, marked]
  | singleton n g r w hw => simpa [timeWeight, marked] using hL
  | comp Q P hQ hP =>
    have hq : Q.order ≤ L := by change Q.order + P.order ≤ L at hL; omega
    have hp : P.order ≤ L := by change Q.order + P.order ≤ L at hL; omega
    simpa only [timeWeight, marked, pow_add] using Nat.mul_le_mul (hQ hq) (hP hp)

variable {E : Type*} [Group G] [DecidableEq G] [Fintype J] [DecidableEq J]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def realize {m n : ℕ} (A : H G E →L[ℂ] H G E) :
    BranchPlan G J m n → Contraction ℂ E J m n
  | .identity n => .identity n
  | .openReg p g r w _ => .openReg p (fun j => wordCoefficient (branch A g r) (w j))
  | .closeReg p g r w _ => .closeReg p (fun j => wordCoefficient (branch A g r) (w j))
  | .middle n g r w => .diagonalReg n (fun s => wordCoefficient (branch A g r) (w s))
  | .singleton n g r w _ => .diagonalReg n (fun _ => ∑ j, wordCoefficient (branch A g r) (w j))
  | .comp Q P => (realize A Q).comp (realize A P)

omit [DecidableEq J] in
theorem cost_le {A : H G E →L[ℂ] H G E} (hA : IsStationary A)
    (P : BranchPlan G J m n) :
    (P.realize A).cost ≤ (P.timeWeight:ℝ) * ‖A‖^P.order *
      (Real.sqrt (Fintype.card J:ℝ))^P.singletons := by
  induction P with
  | identity n => simp [realize, Contraction.cost, timeWeight, order, singletons]
  | openReg p g r w hw =>
    simp only [realize, Contraction.cost, timeWeight, order, singletons, pow_zero, mul_one]
    rw [← HaarCoefficientBounds.column_norm_sq,
      Real.sqrt_sq (norm_nonneg (column (fun j => wordCoefficient (branch A g r) (w j))))]
    apply (branch_column_norm_le A g r w hw).trans
    have hp : (1:ℝ) ≤ (r+1:ℕ) := by exact_mod_cast (Nat.succ_pos r)
    nlinarith [pow_nonneg (norm_nonneg A) (r+1)]
  | closeReg p g r w hw =>
    simp only [realize, Contraction.cost, timeWeight, order, singletons, pow_zero, mul_one]
    rw [← HaarCoefficientBounds.row_norm_sq,
      Real.sqrt_sq (norm_nonneg (row (fun j => wordCoefficient (branch A g r) (w j))))]
    exact branch_row_norm_le hA g r w hw
  | middle n g r w =>
    simp only [realize, Contraction.cost, timeWeight, order, singletons, pow_zero,
      Nat.cast_one, one_mul, mul_one]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro s
    exact branch_word_norm_le A g r (w s)
  | singleton n g r w hw =>
    simp only [realize, Contraction.cost, timeWeight, order, singletons, pow_one]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro s
    apply (branch_singleton_norm_le A g r w hw).trans
    have hp : (1:ℝ) ≤ (r+1:ℕ) := by exact_mod_cast (Nat.succ_pos r)
    have hb : 0 ≤ Real.sqrt (Fintype.card J:ℝ) * ‖A‖^(r+1) := by positivity
    nlinarith
  | comp Q P hQ hP =>
    apply (mul_le_mul hQ hP (Contraction.cost_nonneg _) (by positivity)).trans_eq
    simp only [timeWeight, order, singletons, Nat.cast_mul, pow_add]
    ring

/-- Bound for the fully expanded constrained sum of actual branch coefficients.
The only premise on the operator is its proved translation invariance. -/
theorem pathSum_norm_le {A : H G E →L[ℂ] H G E} (hA : IsStationary A)
    (P : BranchPlan G J m n) (s : Fin n → J) (t : Fin m → J)
    (L : ℕ) (hL : P.order ≤ L) :
    ‖(P.realize A).pathSum s t‖ ≤ (L:ℝ)^P.marked * ‖A‖^P.order *
      (Real.sqrt (Fintype.card J:ℝ))^P.singletons := by
  apply ((P.realize A).pathSum_norm_le s t).trans ((cost_le hA P).trans _)
  have hw : (P.timeWeight:ℝ) ≤ (L:ℝ)^P.marked := by exact_mod_cast timeWeight_le P L hL
  gcongr

/-- Instantiation with a genuine finite regular polynomial; no stationarity
or coefficient-norm certificate is left as a hypothesis. -/
theorem regular_pathSum_norm_le {I : Type*} [Fintype I]
    (v : I → G) (a : I → E →L[ℂ] E) (P : BranchPlan G J m n)
    (s : Fin n → J) (t : Fin m → J) (L : ℕ) (hL : P.order ≤ L) :
    ‖(P.realize (MatrixRegularRestriction.coefficientPolynomial v a)).pathSum s t‖ ≤
      (L:ℝ)^P.marked * ‖MatrixRegularRestriction.coefficientPolynomial v a‖^P.order *
        (Real.sqrt (Fintype.card J:ℝ))^P.singletons :=
  pathSum_norm_le (stationary_regularPolynomial v a) P s t L hL

end BranchPlan
end Nonadditivity.HaarNonbacktracking
