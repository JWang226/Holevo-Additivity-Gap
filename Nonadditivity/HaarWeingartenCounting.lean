/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # Exact row counting for permutation Gram matrices

The sum of the numbers of tuples fixed by the permutations of `p` positions
is the rising factorial `D*(D+1)*...*(D+p-1)`. The proof inserts one position
using `Equiv.Perm.decomposeFin`, without an unproved cycle-count formula.
-/
noncomputable section
namespace Nonadditivity.HaarWeingartenCounting
open scoped BigOperators

/-- Colorings of the positions fixed by a permutation. -/
abbrev FixedTuple (D : ℕ) {p : ℕ} (σ : Equiv.Perm (Fin p)) :=
  {y : Fin p → Fin D // y ∘ σ = y}

lemma fixed_decompose_iff {D p : ℕ} (r : Fin (p+1)) (π : Equiv.Perm (Fin p))
    (y : Fin (p+1) → Fin D) :
    y ∘ Equiv.Perm.decomposeFin.symm (r,π)=y ↔
      y r=y 0 ∧ (fun i => y i.succ) ∘ π=(fun i => y i.succ) := by
  constructor
  · intro h
    have hzero : y r=y 0 := by
      simpa only [Function.comp_apply,Equiv.Perm.decomposeFin_symm_apply_zero] using congrFun h 0
    refine ⟨hzero,?_⟩
    funext i
    have hi := congrFun h i.succ
    simp only [Function.comp_apply,Equiv.Perm.decomposeFin_symm_apply_succ] at hi
    rw [Equiv.apply_swap_eq_self hzero.symm] at hi
    exact hi
  · rintro ⟨hzero,hπ⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Function.comp_apply,Equiv.Perm.decomposeFin_symm_apply_zero] using hzero
    · simp only [Function.comp_apply,Equiv.Perm.decomposeFin_symm_apply_succ]
      rw [Equiv.apply_swap_eq_self hzero.symm]
      exact congrFun hπ j

/-- An inserted fixed point has an independently chosen color. -/
def fixedZeroEquiv (D p : ℕ) (π : Equiv.Perm (Fin p)) :
    FixedTuple D (Equiv.Perm.decomposeFin.symm (0,π)) ≃ Fin D × FixedTuple D π where
  toFun y := ⟨y.val 0, ⟨fun i => y.val i.succ,(fixed_decompose_iff 0 π y.val).mp y.property |>.2⟩⟩
  invFun z := ⟨Fin.cons z.1 z.2.val,(fixed_decompose_iff 0 π _).mpr ⟨rfl,by simpa using z.2.property⟩⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv z := by
    rcases z with ⟨c,v⟩
    rfl

/-- Inserting a position into an existing cycle forces its color. -/
def fixedSuccEquiv (D p : ℕ) (r : Fin p) (π : Equiv.Perm (Fin p)) :
    FixedTuple D (Equiv.Perm.decomposeFin.symm (r.succ,π)) ≃ FixedTuple D π where
  toFun y := ⟨fun i => y.val i.succ,(fixed_decompose_iff r.succ π y.val).mp y.property |>.2⟩
  invFun v := ⟨Fin.cons (v.val r) v.val,
    (fixed_decompose_iff r.succ π _).mpr ⟨rfl,by simpa using v.property⟩⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    exact (fixed_decompose_iff r.succ π y.val).mp y.property |>.1
  right_inv v := rfl

@[simp] theorem card_fixed_zero (D p : ℕ) (π : Equiv.Perm (Fin p)) :
    Fintype.card (FixedTuple D (Equiv.Perm.decomposeFin.symm (0,π))) =
      D * Fintype.card (FixedTuple D π) := by
  rw [Fintype.card_congr (fixedZeroEquiv D p π),Fintype.card_prod,Fintype.card_fin]

@[simp] theorem card_fixed_succ (D p : ℕ) (r : Fin p) (π : Equiv.Perm (Fin p)) :
    Fintype.card (FixedTuple D (Equiv.Perm.decomposeFin.symm (r.succ,π))) =
      Fintype.card (FixedTuple D π) := Fintype.card_congr (fixedSuccEquiv D p r π)

/-- Exact total size of the permutation Gram row, in its integer form. -/
theorem sum_fixedTuple_card (D p : ℕ) :
    (∑ σ : Equiv.Perm (Fin p), Fintype.card (FixedTuple D σ)) = D.ascFactorial p := by
  induction p with
  | zero =>
    have hc (σ : Equiv.Perm (Fin 0)) : Fintype.card (FixedTuple D σ)=1 := by
      letI : Nonempty (FixedTuple D σ) := ⟨⟨Fin.elim0,by funext i; exact Fin.elim0 i⟩⟩
      exact Fintype.card_ofSubsingleton _
    simp [hc]
  | succ p ih =>
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
    simp only [Fintype.sum_prod_type]
    rw [Fin.sum_univ_succ]
    simp only [card_fixed_zero,card_fixed_succ,Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.mul_sum,ih,Nat.ascFactorial_succ,← Finset.mul_sum,ih]
    norm_num
    ring

end Nonadditivity.HaarWeingartenCounting
