/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingFirstStep
import Nonadditivity.HaarTimeCompositions

/-! # Exact iterated last-return segmentation of reduced free-group words -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarNonbacktracking

open scoped BigOperators
open HaarTimeCompositions

section Words
variable {α : Type*} [DecidableEq α]

theorem mk_flatMap_toWord (gs : List (FreeGroup α)) :
    FreeGroup.mk (gs.flatMap FreeGroup.toWord) = gs.prod := by
  induction gs with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons g gs ih =>
      rw [List.flatMap_cons, ← FreeGroup.mul_mk, FreeGroup.mk_toWord, ih, List.prod_cons]

theorem toWord_prod_of_reduced (gs : List (FreeGroup α))
    (hred : FreeGroup.IsReduced (gs.flatMap FreeGroup.toWord)) :
    gs.prod.toWord = gs.flatMap FreeGroup.toWord := by
  rw [← mk_flatMap_toWord, FreeGroup.toWord_mk, hred.reduce_eq]

theorem prod_cons_ne_one_of_reduced (g : FreeGroup α) (gs : List (FreeGroup α))
    (hg : g ≠ 1) (hred : FreeGroup.IsReduced ((g :: gs).flatMap FreeGroup.toWord)) :
    (g :: gs).prod ≠ 1 := by
  intro h
  have he := toWord_prod_of_reduced (g :: gs) hred
  rw [h, FreeGroup.toWord_one, List.flatMap_cons] at he
  have : g.toWord = [] := (List.append_eq_nil_iff.mp he.symm).1
  exact hg (FreeGroup.toWord_eq_nil_iff.mp this)

end Words

section Ring
variable {G R : Type*} [Group G] [Ring R]

/-- At all but the final segment use non-returning coefficients; the final
segment is the ordinary coefficient. Factors retain their actual order. -/
def segmentedProduct (A : MonoidAlgebra R G) : G → List G → List ℕ → R
  | g, [], [n] => (A ^ n) g
  | g, h :: gs, n :: ns => killedPolynomial A 1 n g * segmentedProduct A h gs ns
  | _, _, _ => 0

@[simp] theorem segmentedProduct_single (A : MonoidAlgebra R G) (g : G) (n : ℕ) :
    segmentedProduct A g [] [n] = (A ^ n) g := rfl

@[simp] theorem segmentedProduct_cons (A : MonoidAlgebra R G) (g h : G)
    (gs : List G) (n : ℕ) (ns : List ℕ) :
    segmentedProduct A g (h :: gs) (n :: ns) =
      killedPolynomial A 1 n g * segmentedProduct A h gs ns := rfl

end Ring

variable {α R : Type*} [DecidableEq α] [Ring R]

/-- Both segment lengths may be taken strictly positive. The omitted
endpoints vanish because neither word is the identity. -/
theorem coefficient_factorization_positive
    (A : MonoidAlgebra R (FreeGroup α))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (n : ℕ) (g h : FreeGroup α) (hg : g ≠ 1) (hh : h ≠ 1)
    (hred : FreeGroup.IsReduced (g.toWord ++ h.toWord)) :
    (A ^ n) (g * h) = ∑ k ∈ Finset.range n,
      killedPolynomial A 1 (k + 1) g * (A ^ (n - (k + 1))) h := by
  rw [coefficient_factorization_of_reduced_append A hA n g h hh hred]
  let f : ℕ → R := fun k => killedPolynomial A 1 k g * (A ^ (n - k)) h
  change ∑ k ∈ Finset.range n, f k = ∑ k ∈ Finset.range n, f (k + 1)
  have hzero : f 0 = 0 := by
    simp [f, killedPolynomial, MonoidAlgebra.one_def, Ne.symm hg]
  have hn : f n = 0 := by
    simp [f, MonoidAlgebra.one_def, Ne.symm hh]
  have he := Finset.sum_range_succ' f n
  rw [Finset.sum_range_succ] at he
  simpa [hzero, hn] using he

/-- The full literal coefficient factorization over positive time
compositions. Every non-returning factor may subsequently be localized to
its terminal letter by `killedPolynomial_first_step`. -/
theorem coefficient_factorization_segments
    (A : MonoidAlgebra R (FreeGroup α))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (g : FreeGroup α) (gs : List (FreeGroup α))
    (hne : ∀ h ∈ g :: gs, h ≠ 1)
    (hred : FreeGroup.IsReduced ((g :: gs).flatMap FreeGroup.toWord)) (n : ℕ) :
    (A ^ n) (g :: gs).prod = ∑ t ∈ compositions gs.length n,
      segmentedProduct A g gs t := by
  induction gs generalizing g n with
  | nil =>
      by_cases hn : n = 0
      · subst n
        have hg := hne g (by simp)
        simp [MonoidAlgebra.one_def, Ne.symm hg]
      · simp [compositions, hn]
  | cons h gs ih =>
      have hg : g ≠ 1 := hne g (by simp)
      have hh : h ≠ 1 := hne h (by simp)
      have htred : FreeGroup.IsReduced ((h :: gs).flatMap FreeGroup.toWord) :=
        (List.isChain_append.mp hred).2.1
      have htword := toWord_prod_of_reduced (h :: gs) htred
      have hprefix : FreeGroup.IsReduced (g.toWord ++ (h :: gs).prod.toWord) := by
        simpa only [htword, List.flatMap_cons] using hred
      have htne := prod_cons_ne_one_of_reduced h gs hh htred
      rw [List.prod_cons, coefficient_factorization_positive A hA n g (h :: gs).prod
        hg htne hprefix, List.length_cons, sum_succ]
      apply Finset.sum_congr rfl
      intro k hk
      have htne' : ∀ w ∈ h :: gs, w ≠ 1 := fun w hw => hne w (by simp [hw])
      rw [ih h htne' htred (n - (k + 1)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rfl

end Nonadditivity.HaarNonbacktracking
