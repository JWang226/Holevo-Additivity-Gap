/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileDecodedCoefficients
import Nonadditivity.HaarProfileCompositionBound
import Nonadditivity.NoncommutativeCSBlocks
import Nonadditivity.HaarNonbacktrackingSegmentation
import Nonadditivity.HaarTimeCompositionReverse

/-! # The actual register factors are the last-return segmented product

The skeleton scans occurrences from right to left. Its first block therefore
uses the ordinary polynomial, and each subsequent block uses the killed-return
polynomial. Reversing the scan durations recovers the exact ordered segmented
product, with no commutativity assumption on the operator coefficients.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarSkeletonSegmentation
open scoped BigOperators
open HaarOperatorPolynomial HaarProfileBlockCoefficients HaarNonbacktracking
  NoncommutativeCS HaarProfileCompositionBound HaarProfileDecodedCoefficients
  HaarProfilePatternBound HaarProfileAssignmentBound HaarProfilePadding
  HaarProfileCoefficient HaarPathProfiles HaarTimeCompositions

section Algebra
variable {G R : Type*} [Group G] [Ring R]

def pairCoefficient (A : MonoidAlgebra R G) (ordinary : Bool) (x : G × ℕ) : R :=
  if ordinary then (A ^ x.2) x.1 else killedPolynomial A 1 x.2 x.1

def reverseFactors (A : MonoidAlgebra R G) : Bool → List (G × ℕ) → List R
  | _, [] => []
  | ordinary, x :: xs => reverseFactors A false xs ++ [pairCoefficient A ordinary x]

theorem reverseFactors_snoc (A : MonoidAlgebra R G) (ordinary : Bool)
    (xs : List (G × ℕ)) (x : G × ℕ) :
    reverseFactors A ordinary (xs ++ [x]) =
      [pairCoefficient A (ordinary && xs.isEmpty) x] ++ reverseFactors A ordinary xs := by
  induction xs generalizing ordinary with
  | nil => simp [reverseFactors]
  | cons y ys ih => simp [reverseFactors, ih, List.append_assoc]

theorem reverseFactors_segmentedProduct (A : MonoidAlgebra R G)
    (g : G) (gs : List G) (ts : List ℕ) (ht : ts.length = (g :: gs).length) :
    (reverseFactors A true (((g :: gs).zip ts).reverse)).prod =
      segmentedProduct A g gs ts := by
  induction gs generalizing g ts with
  | nil =>
      cases ts with
      | nil => simp at ht
      | cons n ns =>
          have hn : ns = [] := List.length_eq_zero_iff.mp (by simpa using ht)
          subst ns
          simp [reverseFactors, pairCoefficient]
  | cons h hs ih =>
      cases ts with
      | nil => simp at ht
      | cons n ns =>
          have hn : ns.length = (h :: hs).length := by simpa using ht
          have hne : ((h :: hs).zip ns).reverse ≠ [] := by
            have hl : ((h :: hs).zip ns).reverse.length = (h :: hs).length := by
              simp [List.length_zip, hn]
            intro he
            simp [he] at hl
          simp only [List.zip_cons_cons, List.reverse_cons, reverseFactors_snoc]
          simp only [List.isEmpty_eq_false_iff.mpr hne, Bool.and_false,
            List.singleton_append, List.prod_cons, pairCoefficient, Bool.false_eq_true,
            if_false, ih h ns hn, segmentedProduct_cons]

theorem reverseFactors_mapIdx {X : Type*} (A : MonoidAlgebra R G)
    (xs : List X) (word : ℕ → X → G) (duration : ℕ → ℕ) (k : ℕ) :
    reverseFactors A (decide (k = 0))
        (xs.mapIdx (fun i x => (word (k + i) x, duration (k + i)))) =
      (xs.mapIdx (fun i x =>
        pairCoefficient A (decide (k + i = 0)) (word (k + i) x, duration (k + i)))).reverse := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapIdx_cons, Nat.add_zero, List.reverse_cons, reverseFactors]
      have hi := ih (k + 1)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, decide_false] using
        congrArg (fun l => l ++ [pairCoefficient A (decide (k = 0)) (word k x, duration k)]) hi

end Algebra

variable {I J E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d : ℕ}

/-- Decoded whole-block words in the chronological register-scan order. -/
def scanWords {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b)
    (decode : ℕ → List I → List J → FreeGroup (Fin d)) (σ : I → J) :
    List (FreeGroup (Fin d)) :=
  P.blocks.mapIdx (fun k labels => decode k labels (labels.map σ))

@[simp] theorem length_scanWords {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b)
    (decode : ℕ → List I → List J → FreeGroup (Fin d)) (σ : I → J) :
    (scanWords P decode σ).length = P.markedFlags.length := by
  simp [scanWords]

private theorem mapIdx_zip {X Y Z : Type*} (xs : List X)
    (f : ℕ → X → Y) (g : ℕ → X → Z) :
    (xs.mapIdx f).zip (xs.mapIdx g) = xs.mapIdx (fun i x => (f i x, g i x)) := by
  induction xs generalizing f g with
  | nil => rfl
  | cons x xs ih => simp only [List.mapIdx_cons, List.zip_cons_cons, ih]

private theorem mapIdx_duration_eq_times {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (duration : ℕ → ℕ) (k : ℕ) :
    P.blocks.mapIdx (fun j _ => duration (k + j)) = P.times duration k := by
  induction P generalizing k with
  | done => rfl
  | first i P ih =>
      simp only [EndpointSkeleton.blocks, EndpointSkeleton.times, List.mapIdx_cons, Nat.add_zero]
      congr 1
      convert ih (k + 1) using 1
      congr 1
      funext j x
      congr 1
      omega
  | last p P ih =>
      simp only [EndpointSkeleton.blocks, EndpointSkeleton.times, List.mapIdx_cons, Nat.add_zero]
      congr 1
      convert ih (k + 1) using 1
      congr 1
      funext j x
      congr 1
      omega
  | middle visits P ih =>
      simp only [EndpointSkeleton.blocks, EndpointSkeleton.times, List.mapIdx_cons, Nat.add_zero]
      congr 1
      convert ih (k + 1) using 1
      congr 1
      funext j x
      congr 1
      omega
  | singleton i P ih =>
      simp only [EndpointSkeleton.blocks, EndpointSkeleton.times, List.mapIdx_cons, Nat.add_zero]
      congr 1
      convert ih (k + 1) using 1
      congr 1
      funext j x
      congr 1
      omega

/-- The literal unpadded register product is exactly the last-return product
on the decoded blocks in their original left-to-right order. -/
theorem raw_blockFactors_segmentedProduct [Fintype J] [DecidableEq J]
    {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (B : Polynomial (FreeGroup (Fin d)) E)
    (duration : ℕ → ℕ)
    (decode : ℕ → List I → List J → FreeGroup (Fin d)) (σ : I → J)
    (g : FreeGroup (Fin d)) (gs : List (FreeGroup (Fin d)))
    (hgs : (scanWords P decode σ).reverse = g :: gs) :
    (P.blockFactors (fun k labels choices =>
      blockPolynomial B (decide (k = 0)) (duration k) (decode k labels choices)) 0 σ).prod =
      segmentedProduct B g gs (P.times duration 0).reverse := by
  rw [P.blockFactors_eq_reverse_mapIdx]
  simp only [Nat.zero_add]
  have hr := reverseFactors_mapIdx B P.blocks
    (fun k labels => decode k labels (labels.map σ)) duration 0
  simp only [Nat.zero_add, decide_true] at hr
  have he : (scanWords P decode σ).zip (P.times duration 0) =
      P.blocks.mapIdx (fun k labels => (decode k labels (labels.map σ), duration k)) := by
    rw [← mapIdx_duration_eq_times P duration 0]
    simpa only [scanWords, Nat.zero_add] using mapIdx_zip P.blocks
      (fun k labels => decode k labels (labels.map σ)) (fun k _ => duration k)
  have hlen : (P.times duration 0).reverse.length = (g :: gs).length := by
    rw [← hgs, List.length_reverse, List.length_reverse, length_scanWords]
    simp [times_eq_ofFn]
  have hz : ((g :: gs).zip (P.times duration 0).reverse).reverse =
      (scanWords P decode σ).zip (P.times duration 0) := by
    have heql : (scanWords P decode σ).length = (P.times duration 0).length := by
      simp [times_eq_ofFn]
    rw [← hgs]
    have hz := List.reverse_zipWith (f := Prod.mk) heql
    exact congrArg List.reverse hz.symm |>.trans (List.reverse_reverse _)
  have h := reverseFactors_segmentedProduct B g gs (P.times duration 0).reverse hlen
  rw [hz, he, hr] at h
  have hc : ∀ k labels,
      pairCoefficient B (decide (k = 0)) (decode k labels (labels.map σ), duration k) =
        blockPolynomial B (decide (k = 0)) (duration k) (decode k labels (labels.map σ)) := by
    intro k labels
    by_cases hk : k = 0 <;> simp [pairCoefficient, blockPolynomial, hk]
  simpa only [hc] using h

end Nonadditivity.HaarSkeletonSegmentation
