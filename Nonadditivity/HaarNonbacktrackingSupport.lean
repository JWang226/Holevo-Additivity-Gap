/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingLastReturn
import Nonadditivity.FreeGroupCut

/-! # Non-returning paths stay in one component of the free Cayley tree -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarNonbacktracking

open scoped BigOperators

variable {α R : Type*} [DecidableEq α] [Ring R]

/-- A nearest-neighbor polynomial, with the constant coordinate removed at
every step, cannot move a supported word across the identity. -/
theorem killedPolynomial_eq_zero_of_last_ne
    (A : MonoidAlgebra R (FreeGroup α))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (u : FreeGroup α) (hu : u ≠ 1) (B : R) (n : ℕ) (g : FreeGroup α)
    (hg : g = 1 ∨ g.toWord.getLast? ≠ u.toWord.getLast?) :
    killedPolynomial A (MonoidAlgebra.single u B) n g = 0 := by
  induction n generalizing g with
  | zero =>
      have hgu : u ≠ g := by
        intro heq
        subst g
        rcases hg with hg | hg
        · exact hu hg
        · exact hg rfl
      simp [killedPolynomial, hgu]
  | succ n ih =>
      by_cases hg1 : g = 1
      · subst g
        change (A * killedPolynomial A (MonoidAlgebra.single u B) n) 1 -
          (MonoidAlgebra.single 1 ((A * killedPolynomial A (MonoidAlgebra.single u B) n) 1)) 1 = 0
        simp
      · have hglast := hg.resolve_left hg1
        change (A * killedPolynomial A (MonoidAlgebra.single u B) n) g -
          (MonoidAlgebra.single 1
            ((A * killedPolynomial A (MonoidAlgebra.single u B) n) 1)) g = 0
        rw [MonoidAlgebra.single_apply, if_neg (Ne.symm hg1), sub_zero,
          MonoidAlgebra.mul_apply_left]
        apply Finset.sum_eq_zero
        intro a ha
        have hzero : killedPolynomial A (MonoidAlgebra.single u B) n (a⁻¹ * g) = 0 := by
          apply ih
          by_cases hpre : a⁻¹ * g = 1
          · exact Or.inl hpre
          · right
            intro heq
            apply hglast
            have hstep := FreeGroupCut.getLast?_mul_of_length_le_one a (a⁻¹ * g)
              (hA a ha) hpre (by simpa using hg1)
            simpa using hstep.trans heq
        dsimp only
        rw [hzero, mul_zero]

/-- A reduced concatenation has no non-returning contribution from the far
side of its separating identity vertex. -/
theorem killedPolynomial_eq_zero_of_reduced_append
    (A : MonoidAlgebra R (FreeGroup α))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (g h : FreeGroup α) (hh : h ≠ 1)
    (hred : FreeGroup.IsReduced (g.toWord ++ h.toWord)) (B : R) (n : ℕ) :
    killedPolynomial A (MonoidAlgebra.single h⁻¹ B) n g = 0 := by
  apply killedPolynomial_eq_zero_of_last_ne A hA h⁻¹ (inv_ne_one.mpr hh) B n g
  exact Or.inr (FreeGroupCut.getLast?_ne_inv_of_reduced_append g h hh hred)

/-- The exact coefficient factorization for a reduced concatenation, with
the Cayley-tree separation fully proved from the linear support condition. -/
theorem coefficient_factorization_of_reduced_append
    (A : MonoidAlgebra R (FreeGroup α))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (n : ℕ) (g h : FreeGroup α) (hh : h ≠ 1)
    (hred : FreeGroup.IsReduced (g.toWord ++ h.toWord)) :
    (A ^ n) (g * h) = ∑ k ∈ Finset.range n,
      killedPolynomial A 1 k g * (A ^ (n - k)) h := by
  exact coefficient_factorization_at_cut A n g h
    (killedPolynomial_eq_zero_of_reduced_append A hA g h hh hred 1 n)

end Nonadditivity.HaarNonbacktracking
