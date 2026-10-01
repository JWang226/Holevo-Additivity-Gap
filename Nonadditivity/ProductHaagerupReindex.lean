/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductHaagerupProduct

/-! # The product Haagerup bound in the manuscript's `Fin j → FreeGroup α` convention -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.ProductHaagerupReindex
open scoped BigOperators
open ProductHaagerupProduct
open RegularCoefficientEnergy (VectorHilbert liftOperator)

universe u
/-- Parenthesizing the actual finite product of free groups. -/
def groupEquiv (α : Type u) : (j : ℕ) → (Fin j → FreeGroup α) ≃* GroupIndex α j
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ i => Fin.elim0 i
      left_inv := by intro f; funext i; exact Fin.elim0 i
      right_inv := by intro g; cases g; rfl
      map_mul' := by intros; rfl }
  | j+1 =>
    { toFun := fun f => (f 0, groupEquiv α j (fun i => f i.succ))
      invFun := fun g => Fin.cons g.1 ((groupEquiv α j).symm g.2)
      left_inv := by
        intro f
        funext i
        refine Fin.cases rfl (fun k => ?_) i
        simp
      right_inv := by
        intro g
        apply Prod.ext
        · rfl
        · exact (groupEquiv α j).apply_symm_apply g.2
      map_mul' := by
        intro f g
        apply Prod.ext
        · rfl
        · exact (groupEquiv α j).map_mul _ _ }

theorem radius_groupEquiv {α : Type*} [DecidableEq α] (q j : ℕ)
    (g : Fin j → FreeGroup α) :
    RadiusLe q (groupEquiv α j g) ↔ ∀ i, FreeGroup.norm (g i) ≤ q := by
  induction j with
  | zero => simp [RadiusLe]
  | succ j ih =>
    change (FreeGroup.norm (g 0) ≤ q ∧
      RadiusLe q (groupEquiv α j (fun i => g i.succ))) ↔ _
    rw [ih, Fin.forall_fin_succ]

variable {α E : Type*} [DecidableEq α] [Fintype α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The exact radius-cubed product bound for the actual product regular
representation used elsewhere in the formalization. -/
theorem finite_polynomial_norm_sq_le {q j : ℕ}
    (S : Finset (Fin j → FreeGroup α)) (B : (Fin j → FreeGroup α) → E →L[ℂ] E)
    (hS : ∀ g ∈ S, ∀ i, FreeGroup.norm (g i) ≤ q) :
    ‖∑ g ∈ S, (liftOperator (B g)).comp (MatrixRegularRestriction.leftRegular g)‖ ^ 2 ≤
      ((q+1 : ℕ) : ℝ)^(3*j) * ∑ g ∈ S, ‖B g‖ ^ 2 := by
  classical
  let e := groupEquiv α j
  have hrad : ∀ g ∈ S.image e, RadiusLe q g := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    exact (radius_groupEquiv q j h).mpr (hS h hh)
  have hb := ProductHaagerupProduct.finite_polynomial_norm_sq_le
    (S.image e) (fun g => B (e.symm g)) hrad
  simp only [Finset.sum_image e.injective.injOn, e.symm_apply_apply] at hb
  have hn :
      ‖∑ g ∈ S, (liftOperator (B g)).comp (MatrixRegularRestriction.leftRegular (e g))‖ =
      ‖∑ g ∈ S, (liftOperator (B g)).comp (MatrixRegularRestriction.leftRegular g)‖ := by
    have h := MatrixRegularRestriction.coefficientPolynomial_equiv_norm_eq e
      (fun g : S => g.val) (fun g => B g.val)
    rw [← Finset.sum_coe_sort S (fun g => (liftOperator (B g)).comp
      (MatrixRegularRestriction.leftRegular (e g))),
      ← Finset.sum_coe_sort S (fun g => (liftOperator (B g)).comp
      (MatrixRegularRestriction.leftRegular g))]
    exact h
  rwa [hn] at hb

end Nonadditivity.ProductHaagerupReindex
