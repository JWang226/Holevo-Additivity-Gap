/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductHaagerupCreation
import Mathlib.Data.Fintype.Vector

/-! # The finite cancellation decomposition for every reduced word -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.ProductHaagerupWords
open scoped BigOperators InnerProductSpace
open FreeCreation (Letter flip letter)
open RegularCoefficientEnergy (VectorHilbert liftOperator)
open CollinsYounTensor ProductHaagerupCreation

variable {α E : Type*} [DecidableEq α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The all-annihilation part of a word, in multiplication order. -/
def annihilateWord : List (Letter α) → WordHilbert α E →L[ℂ] WordHilbert α E
  | [] => ContinuousLinearMap.id ℂ _
  | s :: w => (creation (flip s)).adjoint.comp (annihilateWord w)

@[simp] theorem annihilateWord_nil : annihilateWord (E := E) ([] : List (Letter α)) =
    ContinuousLinearMap.id ℂ _ := rfl
@[simp] theorem annihilateWord_cons (s : Letter α) (w : List (Letter α)) :
    annihilateWord (E := E) (s :: w) = (creation (flip s)).adjoint.comp (annihilateWord w) := rfl

/-- Annihilation is the Hilbert adjoint of inverse-word creation. -/
theorem annihilateWord_eq_adjoint (w : List (Letter α)) :
    annihilateWord (E := E) w = (createWord (FreeGroup.invRev w)).adjoint := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [annihilateWord_cons, FreeGroup.invRev_cons, createWord_append,
      ContinuousLinearMap.adjoint_comp, ← ih]
    congr 1

/-- Sector `k` creates the first `k` letters and annihilates the rest. -/
def sector : List (Letter α) → ℕ → WordHilbert α E →L[ℂ] WordHilbert α E
  | w, 0 => annihilateWord w
  | [], _ + 1 => 0
  | s :: w, k + 1 => (creation s).comp (sector w k)

@[simp] theorem sector_zero (w : List (Letter α)) :
    sector (E := E) w 0 = annihilateWord w := by cases w <;> rfl
@[simp] theorem sector_nil_succ (k : ℕ) :
    sector (E := E) ([] : List (Letter α)) (k+1) = 0 := rfl
@[simp] theorem sector_cons_succ (s : Letter α) (w : List (Letter α)) (k : ℕ) :
    sector (E := E) (s :: w) (k+1) = (creation s).comp (sector w k) := rfl

/-- Every sector is the concrete creation/annihilation factorization at its split. -/
theorem sector_eq_take_drop (w : List (Letter α)) (k : ℕ) (hk : k ≤ w.length) :
    sector (E := E) w k = (createWord (w.take k)).comp (annihilateWord (w.drop k)) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    cases w with
    | nil => simp at hk
    | cons s w =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hk
      simp [ih w hk, ContinuousLinearMap.comp_assoc]

omit [DecidableEq α] in
private theorem reduced_boundary {s t : Letter α} {w : List (Letter α)}
    (h : FreeGroup.IsReduced (s :: t :: w)) : flip s ≠ t := by
  have hh := (FreeGroup.isReduced_cons_cons.mp h).1
  intro ht
  subst t
  have hb := hh (by rfl)
  rcases s with ⟨a,b⟩
  cases b <;> simp [FreeCreation.flip] at hb

/-- A reduced word of length `l` has exactly `l+1` cancellation sectors.
This is an identity of actual bounded operators, proved from the regular shifts. -/
theorem regular_word_decomposition (w : List (Letter α)) (hw : FreeGroup.IsReduced w) :
    leftRegular (E := E) (FreeGroup.mk w) =
      ∑ k ∈ Finset.range (w.length+1), sector w k := by
  induction w with
  | nil =>
    ext f x
    simp [sector, annihilateWord, ← FreeGroup.one_eq_mk]
  | cons s w ih =>
    have ht : FreeGroup.IsReduced w := by
      cases w with
      | nil => simp
      | cons t w => exact (FreeGroup.isReduced_cons_cons.mp hw).2
    have hg : FreeGroup.mk (s :: w) = letter s * FreeGroup.mk w := by
      rw [← List.singleton_append, ← FreeGroup.mul_mk]
      congr 1
      rcases s with ⟨a,b⟩
      cases b <;> rfl
    rw [hg, leftRegular_mul, leftRegular_letter_decomposition, ih ht,
      ContinuousLinearMap.add_comp]
    have hz : (creation (E := E) (flip s)).adjoint.comp
        (∑ k ∈ Finset.range (w.length+1), sector w k) =
        annihilateWord (s :: w) := by
      rw [Finset.sum_range_succ', ContinuousLinearMap.comp_add, sector_zero]
      have hzero : (creation (E := E) (flip s)).adjoint.comp
          (∑ k ∈ Finset.range w.length, sector w (k+1)) = 0 := by
        rw [ContinuousLinearMap.comp_finset_sum]
        apply Finset.sum_eq_zero
        intro k hk
        cases w with
        | nil => simp at hk
        | cons t w =>
          rw [sector_cons_succ, ← ContinuousLinearMap.comp_assoc,
            creation_adjoint_comp_zero (reduced_boundary hw), ContinuousLinearMap.zero_comp]
      rw [hzero, zero_add]
      rfl
    rw [hz]
    simp only [List.length_cons]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [sector_cons_succ, sector_zero, ← ContinuousLinearMap.comp_finset_sum]

end Nonadditivity.ProductHaagerupWords
