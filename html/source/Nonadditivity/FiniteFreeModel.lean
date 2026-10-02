/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PolynomialReduction
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Vector

/-! Finite quotients that exactly distinguish every word in a prescribed free-group ball. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.FiniteFreeModel
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

abbrev Ball (α : Type*) [DecidableEq α] (R : ℕ) := {w : FreeGroup α // FreeGroup.norm w ≤ R}

def encode (R : ℕ) (w : Ball α R) : Σ t : Fin (R+1), List.Vector (α×Bool) t.val :=
  ⟨⟨w.val.toWord.length,by have := w.property; change w.val.toWord.length ≤ R at this; omega⟩,
    ⟨w.val.toWord,rfl⟩⟩

theorem encode_injective (R : ℕ) : Function.Injective (encode (α := α) R) := by
  intro v w h
  have hwords := congrArg (fun x : Σ t : Fin (R+1), List.Vector (α×Bool) t.val => x.2.val) h
  exact Subtype.ext (FreeGroup.toWord_injective hwords)

instance ballFintype (R : ℕ) : Fintype (Ball α R) := Fintype.ofInjective (encode R) (encode_injective R)

def base (R : ℕ) : Ball α R := ⟨1,by simp⟩

/-- Left translation restricted to pairs that remain inside the finite ball. -/
def partialTranslation (R : ℕ) (a : α) :
    {w : Ball α R // FreeGroup.norm (FreeGroup.of a * w.val) ≤ R} ≃
    {w : Ball α R // FreeGroup.norm ((FreeGroup.of a)⁻¹ * w.val) ≤ R} where
  toFun w := ⟨⟨FreeGroup.of a * w.val.val,w.property⟩,by simpa only [inv_mul_cancel_left] using w.val.property⟩
  invFun w := ⟨⟨(FreeGroup.of a)⁻¹ * w.val.val,w.property⟩,by simpa only [mul_inv_cancel_left] using w.val.property⟩
  left_inv w := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; apply Subtype.ext; simp

/-- Complete the partial translation to a genuine finite permutation. -/
def generatorPerm (R : ℕ) (a : α) : Equiv.Perm (Ball α R) := (partialTranslation R a).extendSubtype

theorem generatorPerm_apply (R : ℕ) (a : α) (w : Ball α R)
    (h : FreeGroup.norm (FreeGroup.of a * w.val) ≤ R) :
    (generatorPerm R a w).val = FreeGroup.of a * w.val := by
  rw [generatorPerm,Equiv.extendSubtype_apply_of_mem _ w h]
  rfl

theorem generatorPerm_inv_apply (R : ℕ) (a : α) (w : Ball α R)
    (h : FreeGroup.norm ((FreeGroup.of a)⁻¹ * w.val) ≤ R) :
    ((generatorPerm R a)⁻¹ w).val = (FreeGroup.of a)⁻¹ * w.val := by
  let v : Ball α R := ⟨(FreeGroup.of a)⁻¹*w.val,h⟩
  have hv : generatorPerm R a v = w := by
    apply Subtype.ext
    rw [generatorPerm_apply]
    · simp [v]
    · simpa [v] using w.property
  have heq : (generatorPerm R a)⁻¹ w = v := by
    rw [←hv]
    exact (generatorPerm R a).symm_apply_apply v
  exact congrArg Subtype.val heq

/-- A homomorphism into a genuine finite group, with no approximation premise. -/
def model (R : ℕ) : FreeGroup α →* Equiv.Perm (Ball α R) := FreeGroup.lift (generatorPerm R)

theorem mk_cons_true (a : α) (l : List (α×Bool)) :
    FreeGroup.mk ((a,true)::l) = FreeGroup.of a * FreeGroup.mk l := by
  rw [FreeGroup.of,FreeGroup.mul_mk]
  rfl

theorem mk_cons_false (a : α) (l : List (α×Bool)) :
    FreeGroup.mk ((a,false)::l) = (FreeGroup.of a)⁻¹ * FreeGroup.mk l := by
  rw [FreeGroup.of,FreeGroup.inv_mk,FreeGroup.mul_mk]
  rfl

/-- Every word of length at most `R` acts correctly on the distinguished identity. -/
theorem model_mk_base (R : ℕ) (l : List (α×Bool)) (hl : l.length ≤ R) :
    ((model R (FreeGroup.mk l)) (base R)).val = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hl' : l.length ≤ R := by simp only [List.length_cons] at hl; omega
    specialize ih hl'
    rcases x with ⟨a,b⟩
    cases b with
    | false =>
      rw [mk_cons_false,map_mul,map_inv]
      change ((generatorPerm R a)⁻¹ ((model R (FreeGroup.mk l)) (base R))).val = _
      rw [generatorPerm_inv_apply]
      · rw [ih]
      · rw [ih,←mk_cons_false]
        exact FreeGroup.norm_mk_le.trans hl
    | true =>
      rw [mk_cons_true,map_mul]
      change (generatorPerm R a ((model R (FreeGroup.mk l)) (base R))).val = _
      rw [generatorPerm_apply]
      · rw [ih]
      · rw [ih,←mk_cons_true]
        exact FreeGroup.norm_mk_le.trans hl

theorem model_base (R : ℕ) (w : FreeGroup α) (hw : FreeGroup.norm w ≤ R) :
    ((model R w) (base R)).val = w := by
  simpa only [FreeGroup.mk_toWord] using model_mk_base R w.toWord hw

/-- The constructed finite model detects every nontrivial element in the chosen ball. -/
theorem model_eq_one_iff (R : ℕ) (w : FreeGroup α) (hw : FreeGroup.norm w ≤ R) :
    model R w = 1 ↔ w = 1 := by
  constructor
  · intro h
    have hb := model_base R w hw
    rw [h] at hb
    exact hb.symm
  · rintro rfl; exact map_one _

theorem model_ne_one (R : ℕ) (w : FreeGroup α) (hw : FreeGroup.norm w ≤ R) (h : w≠1) :
    model R w ≠ 1 := (model_eq_one_iff R w hw).not.mpr h

/-- An explicit finite group separates any given nonidentity free-group element. -/
theorem exists_finite_separating_model (w : FreeGroup α) (hw : w≠1) :
    ∃(H : Type u) (_ : Fintype H) (_ : Group H) (π : FreeGroup α →* H), π w≠1 := by
  exact ⟨Equiv.Perm (Ball α (FreeGroup.norm w)),inferInstance,inferInstance,
    model (FreeGroup.norm w),model_ne_one _ _ le_rfl hw⟩

/-- Independent coordinate models give a finite quotient of the product free group. -/
def productModel (R n : ℕ) : (Fin n → FreeGroup α) →* (Fin n → Equiv.Perm (Ball α R)) where
  toFun w j := model R (w j)
  map_one' := by funext j; exact map_one _
  map_mul' v w := by funext j; exact map_mul _ _ _

theorem productModel_eq_one_iff (R n : ℕ) (w : Fin n → FreeGroup α)
    (hw : ∀j, FreeGroup.norm (w j) ≤ R) : productModel R n w = 1 ↔ w=1 := by
  constructor
  · intro h
    funext j
    apply (model_eq_one_iff R (w j) (hw j)).mp
    exact congrFun h j
  · rintro rfl; exact map_one _

end Nonadditivity.FiniteFreeModel
