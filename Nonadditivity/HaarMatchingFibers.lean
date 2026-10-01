/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Counting bijections that preserve actual entry labels

A label-preserving bijection restricts to a bijection of each pair of fibers.
This gives the exact factorial counting bound used after the values of a Haar
matching have been fixed on its disagreement support.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace Nonadditivity.HaarMatchingFibers
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A B E : Type*}

/-- Literal bijections of the occurrence sets preserving their entry labels. -/
def LabelEquiv (x : A → E) (y : B → E) := {σ : A ≃ B // ∀ a, y (σ a) = x a}

instance [Fintype A] [Fintype B] (x : A → E) (y : B → E) : Fintype (LabelEquiv x y) :=
  by
    classical
    exact inferInstanceAs (Fintype {σ : A ≃ B // ∀ a, y (σ a) = x a})

/-- A label-preserving matching induces an actual equivalence on each fiber. -/
def fiberEquiv (x : A → E) (y : B → E) (σ : LabelEquiv x y) (e : E) :
    {a : A // x a = e} ≃ {b : B // y b = e} where
  toFun a := ⟨σ.val a.val, (σ.property a.val).trans a.property⟩
  invFun b := ⟨σ.val.symm b.val, (σ.property (σ.val.symm b.val)).symm.trans
    (by rw [σ.val.apply_symm_apply]; exact b.property)⟩
  left_inv a := by apply Subtype.ext; exact σ.val.symm_apply_apply _
  right_inv b := by apply Subtype.ext; exact σ.val.apply_symm_apply _

/-- All fiber restrictions together determine the entire matching. -/
theorem fiberEquiv_injective (x : A → E) (y : B → E) :
    Function.Injective (fun σ : LabelEquiv x y => fiberEquiv x y σ) := by
  intro σ τ h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have he := congrFun h (x a)
  have hv := congrArg (fun f : {a' : A // x a' = x a} ≃ {b : B // y b = x a} =>
    (f ⟨a,rfl⟩).val) he
  exact hv

/-- Even for unequal fiber sizes, the number of bijections is at most the
factorial of the source size: an incompatible fiber contributes zero. -/
theorem card_equiv_le_factorial [Fintype A] [Fintype B] :
    Fintype.card (A ≃ B) ≤ (Fintype.card A).factorial := by
  classical
  by_cases h : Nonempty (A ≃ B)
  · obtain ⟨e⟩ := h
    exact le_of_eq (Fintype.card_equiv e)
  · letI : IsEmpty (A ≃ B) := not_nonempty_iff.mp h
    simp

/-- The sharp fiber-factorial bound, with no premise asserting compatible
fiber cardinalities or existence of a matching. -/
theorem card_labelEquiv_le [Fintype A] [Fintype B] [Fintype E]
    (x : A → E) (y : B → E) :
    Fintype.card (LabelEquiv x y) ≤
      ∏ e : E, (Fintype.card {a : A // x a = e}).factorial := by
  classical
  calc
    _ ≤ Fintype.card (∀ e : E, {a : A // x a = e} ≃ {b : B // y b = e}) :=
      Fintype.card_le_of_injective (fun σ => fiberEquiv x y σ) (fiberEquiv_injective x y)
    _ = ∏ e : E, Fintype.card ({a : A // x a = e} ≃ {b : B // y b = e}) :=
      Fintype.card_pi
    _ ≤ _ := by
      have h (e : E) := card_equiv_le_factorial
        (A := {a : A // x a = e}) (B := {b : B // y b = e})
      simp only [← Nat.card_eq_fintype_card] at h ⊢
      exact Finset.prod_le_prod' (fun e _ => h e)


/-- Only fibers with total multiplicity at least four cost a nontrivial
factorial.  Matching uses at most half of the total occurrences in each fiber. -/
theorem prod_factorial_le_pow_half_high [Fintype E]
    (p : ℕ) (hp : 0 < p) (a t : E → ℕ)
    (ha : ∀ e, a e ≤ p) (hat : ∀ e, 2*a e ≤ t e) :
    (∏ e : E, (a e).factorial) ≤
      p ^ ((∑ e : E, if 4 ≤ t e then t e else 0)/2) := by
  classical
  let c : E → ℕ := fun e => if 4 ≤ t e then a e else 0
  have hfactor (e : E) : (a e).factorial ≤ p ^ c e := by
    by_cases h : 4 ≤ t e
    · simp only [c, if_pos h]
      exact (Nat.factorial_le_pow (a e)).trans (Nat.pow_le_pow_left (ha e) _)
    · have hsmall : a e ≤ 1 := by have := hat e; omega
      simp [c, h, Nat.factorial_eq_one.mpr hsmall]
  have hexp : (∑ e : E, c e) ≤ (∑ e : E, if 4 ≤ t e then t e else 0)/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e he
    by_cases h : 4 ≤ t e
    · simpa [c, h, mul_comm] using hat e
    · simp [c, h]
  calc
    _ ≤ ∏ e : E, p ^ c e := Finset.prod_le_prod' (fun e _ => hfactor e)
    _ = p ^ (∑ e : E, c e) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Nat.pow_le_pow_right hp hexp

end Nonadditivity.HaarMatchingFibers
