/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingSupport
import Nonadditivity.FreeCreation

/-! # The first step of a non-returning free-group path -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarNonbacktracking

open scoped BigOperators

section Ring
variable {G R : Type*} [Group G] [DecidableEq G] [Ring R]

omit [DecidableEq G] in
@[simp] theorem killedPolynomial_zero (A : MonoidAlgebra R G) (n : ℕ) :
    killedPolynomial A 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [killedPolynomial, ih]

omit [DecidableEq G] in
theorem killedPolynomial_add (A T U : MonoidAlgebra R G) (n : ℕ) :
    killedPolynomial A (T + U) n = killedPolynomial A T n + killedPolynomial A U n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change removeConstant (A * killedPolynomial A (T + U) n) = _
      rw [ih, mul_add, removeConstant_add]
      rfl

omit [DecidableEq G] in
theorem killedPolynomial_sum {I : Type*} (A : MonoidAlgebra R G) (s : Finset I)
    (T : I → MonoidAlgebra R G) (n : ℕ) :
    killedPolynomial A (∑ i ∈ s, T i) n = ∑ i ∈ s, killedPolynomial A (T i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, killedPolynomial_add, ih]

/-- Expand a killed polynomial in its literal initial coefficients. -/
theorem killedPolynomial_sum_source (A T : MonoidAlgebra R G) (n : ℕ) :
    killedPolynomial A T n = ∑ u ∈ T.support,
      killedPolynomial A (MonoidAlgebra.single u (T u)) n := by
  calc
    _ = killedPolynomial A (∑ u ∈ T.support, MonoidAlgebra.single u (T u)) n := by
      congr 1
      exact T.sum_single.symm
    _ = _ := killedPolynomial_sum _ _ _ _

omit [DecidableEq G] in
/-- Move the first killed step into the initial condition. -/
theorem killedPolynomial_shift (A T : MonoidAlgebra R G) (n : ℕ) :
    killedPolynomial A T (n + 1) = killedPolynomial A (removeConstant (A * T)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change removeConstant (A * killedPolynomial A T (n + 1)) =
        removeConstant (A * killedPolynomial A (removeConstant (A * T)) n)
      rw [ih]

theorem removeConstant_apply (A : MonoidAlgebra R G) (g : G) :
    removeConstant A g = A g - if 1 = g then A 1 else 0 := by
  change A g - (MonoidAlgebra.single 1 (A 1)) g = _
  rw [MonoidAlgebra.single_apply]

theorem removeConstant_support (A : MonoidAlgebra R G) :
    (removeConstant A).support = A.support.erase 1 := by
  ext g
  by_cases hg : g = 1
  · subst g
    simp [Finsupp.mem_support_iff, removeConstant_apply]
  · simp [Finsupp.mem_support_iff, removeConstant_apply, hg, Ne.symm hg]

end Ring

variable {α R : Type*} [DecidableEq α] [Ring R]

/-- At a specified terminal letter, only the matching initial generator can
contribute to a path that never returns to the identity. -/
theorem killedPolynomial_first_step
    (A : MonoidAlgebra R (FreeGroup α))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (s : FreeCreation.Letter α) (g : FreeGroup α)
    (hg : g.toWord.getLast? = some s) (n : ℕ) :
    killedPolynomial A 1 (n + 1) g =
      killedPolynomial A
        (MonoidAlgebra.single (FreeCreation.letter s) (A (FreeCreation.letter s))) n g := by
  have hs1 : FreeCreation.letter s ≠ 1 := by
    intro hs
    have := congrArg FreeGroup.toWord hs
    simp at this
  rw [killedPolynomial_shift, mul_one, killedPolynomial_sum_source]
  change coefficientAddHom g (∑ u ∈ (removeConstant A).support,
    killedPolynomial A (MonoidAlgebra.single u (removeConstant A u)) n) = _
  rw [map_sum]
  simp only [coefficientAddHom_apply]
  have hscoef : A (FreeCreation.letter s) = removeConstant A (FreeCreation.letter s) := by
    simp [removeConstant_apply, Ne.symm hs1]
  rw [hscoef]
  apply Finset.sum_eq_single (FreeCreation.letter s)
  · intro u hu hus
    rw [removeConstant_support, Finset.mem_erase] at hu
    apply killedPolynomial_eq_zero_of_last_ne A hA u hu.1 _ n g
    right
    intro heq
    have hulast : u.toWord.getLast? = some s := heq.symm.trans hg
    have huword : u.toWord = [s] := by
      have hlen := hA u hu.2
      cases hword : u.toWord with
      | nil => simp [hword] at hulast
      | cons t w =>
          have hw : w = [] := by simpa [hword] using hlen
          subst w
          have ht : t = s := by simpa [hword] using hulast
          simp [ht]
    apply hus
    apply FreeGroup.toWord_injective
    simpa using huword
  · intro hs
    have hnot : FreeCreation.letter s ∉ A.support := by
      simpa [removeConstant_support, hs1] using hs
    have hz : A (FreeCreation.letter s) = 0 := Finsupp.notMem_support_iff.mp hnot
    rw [← hscoef, hz]
    simp

end Nonadditivity.HaarNonbacktracking
