/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarOperatorCoefficient
import Nonadditivity.HaarNonbacktrackingFirstStep
import Nonadditivity.HaarPathProfiles

/-! # Actual reduced profile families and their coefficient factors

A profile family consists of finite reduced words with prescribed endpoints
and letter counts. Its map into the free group is proved injective, and the
row, column, individual, and singleton factors are bounded for the literal
ordinary or non-returning coefficients. No norm hypothesis on a profile family
is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarProfileCoefficient

open scoped BigOperators
open HaarPathProfiles HaarNonbacktracking HaarOperatorPolynomial NoncommutativeCS

/-- Words of exactly `k` letters with the indicated literal reduced-word profile. -/
def Words (d k : ℕ) (p : Profile (Color d)) :=
  {w : Fin k → Color d // FreeGroup.IsReduced (List.ofFn w) ∧
    (List.ofFn w).head? = some p.first ∧ (List.ofFn w).getLast? = some p.last ∧
    ∀ a, (List.ofFn w).count a = p.count a}

instance wordsFintype (d k : ℕ) (p : Profile (Color d)) : Fintype (Words d k p) :=
by
  classical
  unfold Words
  infer_instance

def word {d k : ℕ} {p : Profile (Color d)} (w : Words d k p) : FreeGroup (Fin d) :=
  FreeGroup.mk (List.ofFn w.val)

@[simp] theorem word_toWord {d k : ℕ} {p : Profile (Color d)} (w : Words d k p) :
    (word w).toWord = List.ofFn w.val := by
  exact FreeGroup.toWord_mk.trans (FreeGroup.isReduced_iff_reduce_eq.mp w.property.1)

theorem word_injective {d k : ℕ} {p : Profile (Color d)} :
    Function.Injective (word (d := d) (k := k) (p := p)) := by
  intro v w h
  apply Subtype.ext
  apply List.ofFn_injective
  simpa only [word_toWord] using congrArg FreeGroup.toWord h

theorem last_word {d k : ℕ} {p : Profile (Color d)} (w : Words d k p) :
    (word w).toWord.getLast? = some p.last := by
  rw [word_toWord]
  exact w.property.2.2.1

theorem word_ne_one {d k : ℕ} {p : Profile (Color d)} (w : Words d k p) :
    word w ≠ 1 := by
  intro h
  have hh := last_word w
  rw [h] at hh
  simp at hh

/-- A profile family has at most all words of its fixed length. -/
theorem card_words_le (d k : ℕ) (p : Profile (Color d)) :
    Fintype.card (Words d k p) ≤ (2 * d) ^ k := by
  have h := Fintype.card_le_of_injective (fun w : Words d k p => w.val)
    Subtype.val_injective
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool, Nat.mul_comm d 2] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d k : ℕ} (A : Polynomial (FreeGroup (Fin d)) E)
variable (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
variable (n : ℕ) (p : Profile (Color d))

/-- The coefficient family after a cut is the actual killed-return polynomial. -/
def returningCoefficients (w : Words d k p) : E →L[ℂ] E :=
  killedPolynomial A 1 (n + 1) (word w)

include hA

/-- Every word with the same profile has the same distinguished first step. -/
theorem returningCoefficients_eq_firstStep (w : Words d k p) :
    returningCoefficients A n p w = firstStep A (FreeCreation.letter p.last) n (word w) := by
  exact killedPolynomial_first_step A hA p.last (word w) (last_word w) n

/-- Interior blocks have the sharp power bound and incur no factor `n+1`. -/
theorem returning_coefficient_norm_le (w : Words d k p) :
    ‖returningCoefficients A n p w‖ ≤ ‖regular A‖ ^ (n + 1) := by
  rw [returningCoefficients_eq_firstStep A hA]
  exact firstStep_coefficient_norm_le _ _ _ _

/-- First/last visits of a repeated profile use row or column Gram factors. -/
theorem returning_endpoint_bounds :
    Real.sqrt ‖columnGram (returningCoefficients (k := k) A n p)‖ ≤
        (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) ∧
    Real.sqrt ‖rowGram (returningCoefficients (k := k) A n p)‖ ≤
        (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) := by
  have he : returningCoefficients (k := k) A n p =
      fun w => firstStep A (FreeCreation.letter p.last) n (word w) := by
    funext w
    exact returningCoefficients_eq_firstStep A hA n p w
  rw [he]
  exact firstStep_endpoint_bounds _ _ _ word word_injective

/-- A once-visited profile costs only the square root of its number of words. -/
theorem returning_singleton_bound :
    ‖∑ w : Words d k p, returningCoefficients A n p w‖ ≤
      Real.sqrt (((2 * d) ^ k : ℕ) : ℝ) * ((n + 1 : ℕ) * ‖regular A‖ ^ (n + 1)) := by
  have hc : (Fintype.card (Words d k p) : ℝ) ≤ (2 * d : ℝ) ^ k := by
    exact_mod_cast card_words_le d k p
  calc
    _ ≤ Real.sqrt (Fintype.card (Words d k p) : ℝ) *
        Real.sqrt ‖columnGram (returningCoefficients (k := k) A n p)‖ :=
      HaarCoefficientBounds.singleton_sum_norm_le _
    _ ≤ Real.sqrt ((2 * d : ℝ) ^ k) * ((n + 1 : ℕ) * ‖regular A‖ ^ (n + 1)) :=
      mul_le_mul (Real.sqrt_le_sqrt hc) (returning_endpoint_bounds A hA n p).1
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by norm_cast

omit hA

/-- Ordinary power coefficients, used by the initial block. -/
def ordinaryCoefficients (w : Words d k p) : E →L[ℂ] E := (A ^ (n + 1)) (word w)

theorem ordinary_coefficient_norm_le (w : Words d k p) :
    ‖ordinaryCoefficients A n p w‖ ≤ ‖regular A‖ ^ (n + 1) := by
  exact (coefficient_norm_le (A ^ (n + 1)) (word w)).trans (by
    rw [map_pow]
    exact norm_pow_le' _ (Nat.succ_pos _))

theorem ordinary_endpoint_bounds :
    Real.sqrt ‖columnGram (ordinaryCoefficients (k := k) A n p)‖ ≤ ‖regular A‖ ^ (n + 1) ∧
    Real.sqrt ‖rowGram (ordinaryCoefficients (k := k) A n p)‖ ≤ ‖regular A‖ ^ (n + 1) := by
  have hn : ‖regular (A ^ (n + 1))‖ ≤ ‖regular A‖ ^ (n + 1) := by
    rw [map_pow]
    exact norm_pow_le' _ (Nat.succ_pos _)
  constructor
  · exact (Real.sqrt_le_sqrt (coefficient_columnGram_le (A ^ (n + 1)) word word_injective)).trans
      (by rw [Real.sqrt_sq (norm_nonneg _)]; exact hn)
  · exact (Real.sqrt_le_sqrt (coefficient_rowGram_le (A ^ (n + 1)) word word_injective)).trans
      (by rw [Real.sqrt_sq (norm_nonneg _)]; exact hn)

end Nonadditivity.HaarProfileCoefficient
