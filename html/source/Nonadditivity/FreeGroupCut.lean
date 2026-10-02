/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.List.Chain

/-! # The identity is a cut vertex in a free Cayley graph -/

namespace Nonadditivity.FreeGroupCut

variable {α : Type*} [DecidableEq α]

/-- A single left step cannot change the final letter without passing through
the identity. This is the elementary tree-separation fact used in last-return
factorizations. -/
theorem getLast?_mul_of_length_le_one (a u : FreeGroup α)
    (ha : a.toWord.length ≤ 1) (hu : u ≠ 1) (hau : a * u ≠ 1) :
    (a * u).toWord.getLast? = u.toWord.getLast? := by
  cases he : a.toWord with
  | nil =>
      have : a = 1 := FreeGroup.toWord_eq_nil_iff.mp he
      simp [this]
  | cons s v =>
      have hv : v = [] := by simpa [he] using ha
      subst v
      cases huword : u.toWord with
      | nil => exact (hu (FreeGroup.toWord_eq_nil_iff.mp huword)).elim
      | cons t v =>
          have hred : FreeGroup.reduce (t :: v) = t :: v := by
            simpa [huword] using FreeGroup.reduce_toWord u
          rw [FreeGroup.toWord_mul, he, huword, List.singleton_append, FreeGroup.reduce.cons,
            hred]
          dsimp only
          split_ifs with hcancel
          · cases v with
            | nil =>
                exfalso
                apply hau
                apply FreeGroup.toWord_eq_nil_iff.mp
                rw [FreeGroup.toWord_mul, he, huword, List.singleton_append,
                  FreeGroup.reduce.cons, hred]
                simp [hcancel]
            | cons v vs => simp
          · simp

/-- The two sides of a reduced concatenation lie in distinct components of
the Cayley graph with the identity removed. -/
theorem getLast?_ne_inv_of_reduced_append (g h : FreeGroup α)
    (hh : h ≠ 1) (hred : FreeGroup.IsReduced (g.toWord ++ h.toWord)) :
    g.toWord.getLast? ≠ h⁻¹.toWord.getLast? := by
  cases hword : h.toWord with
  | nil => exact (hh (FreeGroup.toWord_eq_nil_iff.mp hword)).elim
  | cons s w =>
      have hlast : h⁻¹.toWord.getLast? = some (s.1, !s.2) := by
        simp [FreeGroup.toWord_inv, hword, FreeGroup.invRev]
      intro heq
      have hb := (List.isChain_append.mp hred).2.2 (s.1, !s.2)
        (by rw [heq, hlast]; rfl) s (by simp [hword]) rfl
      cases s.2 <;> simp at hb

end Nonadditivity.FreeGroupCut
