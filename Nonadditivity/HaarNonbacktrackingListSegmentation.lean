/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingSegmentation
import Nonadditivity.HaarTimeCompositionReverse

/-! # List form of the exact non-returning coefficient segmentation -/
noncomputable section
namespace Nonadditivity.HaarNonbacktracking
open scoped BigOperators
open HaarTimeCompositions

section Ring
variable {G R : Type*} [Group G] [Ring R]

/-- List form, with an explicit zero value for the empty segmentation. -/
def segmentedListProduct (A : MonoidAlgebra R G) (gs : List G) (t : List ℕ) : R :=
  match gs with
  | [] => 0
  | g :: gs => segmentedProduct A g gs t

@[simp] theorem segmentedListProduct_cons (A : MonoidAlgebra R G)
    (g : G) (gs : List G) (t : List ℕ) :
    segmentedListProduct A (g :: gs) t = segmentedProduct A g gs t := rfl

/-- Reversing every duration list is an exact reindexing of this sum. -/
theorem sum_segmentedListProduct_reverse (A : MonoidAlgebra R G)
    (gs : List G) (cuts q : ℕ) :
    ∑ t ∈ compositions cuts q, segmentedListProduct A gs t.reverse =
      ∑ t ∈ compositions cuts q, segmentedListProduct A gs t :=
  sum_reverse cuts q (segmentedListProduct A gs)

end Ring

variable {α R : Type*} [DecidableEq α] [Ring R]

/-- The exact segmentation identity without separately naming its first
nontrivial reduced word. -/
theorem coefficient_factorization_list
    (B : MonoidAlgebra R (FreeGroup α))
    (hB : ∀ a ∈ B.support, a.toWord.length ≤ 1)
    (gs : List (FreeGroup α)) (hgs : gs ≠ [])
    (hne : ∀ g ∈ gs, g ≠ 1)
    (hred : FreeGroup.IsReduced (gs.flatMap FreeGroup.toWord)) (q : ℕ) :
    (B^q) gs.prod = ∑ t ∈ compositions (gs.length-1) q, segmentedListProduct B gs t := by
  cases gs with
  | nil => exact (hgs rfl).elim
  | cons g gs =>
      simpa only [List.length_cons,Nat.add_sub_cancel,segmentedListProduct] using
        coefficient_factorization_segments B hB g gs hne hred q

/-- The same identity in reverse chronological duration coordinates. -/
theorem coefficient_factorization_list_reverse
    (B : MonoidAlgebra R (FreeGroup α))
    (hB : ∀ a ∈ B.support, a.toWord.length ≤ 1)
    (gs : List (FreeGroup α)) (hgs : gs ≠ [])
    (hne : ∀ g ∈ gs, g ≠ 1)
    (hred : FreeGroup.IsReduced (gs.flatMap FreeGroup.toWord)) (q : ℕ) :
    (B^q) gs.prod = ∑ t ∈ compositions (gs.length-1) q, segmentedListProduct B gs t.reverse := by
  rw [sum_segmentedListProduct_reverse]
  exact coefficient_factorization_list B hB gs hgs hne hred q

end Nonadditivity.HaarNonbacktracking
