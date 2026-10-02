/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileCoefficient

/-! # Both orientations of a fixed core-edge profile

A repeated core edge may be traversed in either direction. Inversion preserves
the injectivity of its word family, and the reversed traversal has a fixed
terminal letter determined by the original profile's first letter. Thus the
same sharp endpoint estimates apply without identifying the two orientations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarProfileCoefficient

open scoped BigOperators
open HaarPathProfiles HaarNonbacktracking HaarOperatorPolynomial NoncommutativeCS

variable {d k : ℕ} {p : Profile (Color d)}

def orientedWord (forward : Bool) (w : Words d k p) : FreeGroup (Fin d) :=
  if forward then word w else (word w)⁻¹

def terminalLetter (forward : Bool) (p : Profile (Color d)) : Color d :=
  if forward then p.last else FreeCreation.flip p.first

theorem last_inverse_word (w : Words d k p) :
    (word w)⁻¹.toWord.getLast? = some (FreeCreation.flip p.first) := by
  cases hw : List.ofFn w.val with
  | nil =>
      have hh := w.property.2.1
      simp [hw] at hh
  | cons a l =>
      have ha : a = p.first := by simpa [hw] using w.property.2.1
      simp [FreeGroup.toWord_inv, word_toWord, hw, FreeGroup.invRev, ha, FreeCreation.flip]

theorem orientedWord_injective (forward : Bool) :
    Function.Injective (orientedWord (d := d) (k := k) (p := p) forward) := by
  cases forward
  · exact fun _ _ h => word_injective (inv_injective h)
  · exact word_injective

theorem last_orientedWord (forward : Bool) (w : Words d k p) :
    (orientedWord forward w).toWord.getLast? = some (terminalLetter forward p) := by
  cases forward
  · exact last_inverse_word w
  · exact last_word w

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : Polynomial (FreeGroup (Fin d)) E)
variable (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
variable (n : ℕ) (forward : Bool) (p : Profile (Color d))

def orientedCoefficients (w : Words d k p) : E →L[ℂ] E :=
  killedPolynomial A 1 (n + 1) (orientedWord forward w)

include hA

theorem orientedCoefficients_eq_firstStep (w : Words d k p) :
    orientedCoefficients A n forward p w =
      firstStep A (FreeCreation.letter (terminalLetter forward p)) n (orientedWord forward w) := by
  exact killedPolynomial_first_step A hA _ _ (last_orientedWord forward w) n

theorem oriented_coefficient_norm_le (w : Words d k p) :
    ‖orientedCoefficients A n forward p w‖ ≤ ‖regular A‖ ^ (n + 1) := by
  rw [orientedCoefficients_eq_firstStep A hA]
  exact firstStep_coefficient_norm_le _ _ _ _

theorem oriented_endpoint_bounds :
    Real.sqrt ‖columnGram (orientedCoefficients (k := k) A n forward p)‖ ≤
        (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) ∧
    Real.sqrt ‖rowGram (orientedCoefficients (k := k) A n forward p)‖ ≤
        (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) := by
  have he : orientedCoefficients (k := k) A n forward p =
      fun w => firstStep A (FreeCreation.letter (terminalLetter forward p)) n
        (orientedWord forward w) := by
    funext w
    exact orientedCoefficients_eq_firstStep A hA n forward p w
  rw [he]
  exact firstStep_endpoint_bounds _ _ _ _ (orientedWord_injective forward)

theorem oriented_singleton_bound :
    ‖∑ w : Words d k p, orientedCoefficients A n forward p w‖ ≤
      Real.sqrt (((2 * d) ^ k : ℕ) : ℝ) * ((n + 1 : ℕ) * ‖regular A‖ ^ (n + 1)) := by
  have hc : (Fintype.card (Words d k p) : ℝ) ≤ (2 * d : ℝ) ^ k := by
    exact_mod_cast card_words_le d k p
  calc
    _ ≤ Real.sqrt (Fintype.card (Words d k p) : ℝ) *
        Real.sqrt ‖columnGram (orientedCoefficients (k := k) A n forward p)‖ :=
      HaarCoefficientBounds.singleton_sum_norm_le _
    _ ≤ Real.sqrt ((2 * d : ℝ) ^ k) * ((n + 1 : ℕ) * ‖regular A‖ ^ (n + 1)) :=
      mul_le_mul (Real.sqrt_le_sqrt hc) (oriented_endpoint_bounds A hA n forward p).1
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by norm_cast

end Nonadditivity.HaarProfileCoefficient
