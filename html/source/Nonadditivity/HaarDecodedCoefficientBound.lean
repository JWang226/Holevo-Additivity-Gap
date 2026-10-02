/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarSkeletonSegmentation
import Nonadditivity.HaarNonbacktrackingListSegmentation

/-! # The literal coefficient sum over independent profile words

This final analytic bridge identifies the actual group-polynomial coefficient
with the compressed register expression and applies its proved norm estimate.
The remaining inputs concern only which reduced group words the blocks decode.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarDecodedCoefficientBound
open scoped BigOperators
open HaarOperatorPolynomial HaarProfileBlockCoefficients HaarNonbacktracking
  NoncommutativeCS HaarProfileCompositionBound HaarProfileDecodedCoefficients
  HaarProfilePatternBound HaarProfileAssignmentBound HaarProfilePadding
  HaarProfileCoefficient HaarPathProfiles HaarTimeCompositions HaarSkeletonSegmentation

variable {I E : Type*} [DecidableEq I] [Fintype I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d M : ℕ}

theorem blockFactors_segmentedListProduct
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hblocks : 1 ≤ P.markedFlags.length)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (σ : ∀ i, Words d (size i) (profile i))
    (hdecode : ∀ k i, decode k [i] [embedAssignment size profile hsize σ i] =
      orientedWord (forward k i) (σ i))
    (t : List ℕ) (ht : t.length = P.markedFlags.length) :
    (P.blockFactors
      (blockFactor B size profile hsize (fun k => decide (k = 0)) (durationOf t) forward decode)
      0 (embedAssignment size profile hsize σ)).prod =
      segmentedListProduct B (scanWords P decode (embedAssignment size profile hsize σ)).reverse
        t.reverse := by
  rw [blockFactors_valid P B size profile hsize (fun k => decide (k = 0))
    (durationOf t) forward decode σ hdecode 0]
  have hne : (scanWords P decode (embedAssignment size profile hsize σ)).reverse ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_reverse, length_scanWords, List.length_nil] at hl
    omega
  generalize he : (scanWords P decode (embedAssignment size profile hsize σ)).reverse = gs
  cases gs with
  | nil => exact False.elim (hne he)
  | cons g gs =>
      have h := raw_blockFactors_segmentedProduct P B (durationOf t) decode
        (embedAssignment size profile hsize σ) g gs he
      rw [times_durationOf P t ht] at h
      exact h

theorem coefficient_eq_composition_sum
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hblocks : 1 ≤ P.markedFlags.length)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (σ : ∀ i, Words d (size i) (profile i))
    (hdecode : ∀ k i, decode k [i] [embedAssignment size profile hsize σ i] =
      orientedWord (forward k i) (σ i))
    (target : FreeGroup (Fin d))
    (htarget : (scanWords P decode (embedAssignment size profile hsize σ)).reverse.prod = target)
    (hne : ∀ g ∈ (scanWords P decode (embedAssignment size profile hsize σ)).reverse, g ≠ 1)
    (hred : FreeGroup.IsReduced
      ((scanWords P decode (embedAssignment size profile hsize σ)).reverse.flatMap FreeGroup.toWord))
    (q : ℕ) :
    (B ^ q) target = ∑ t ∈ compositions (P.markedFlags.length - 1) q,
      (P.blockFactors
        (blockFactor B size profile hsize (fun k => decide (k = 0)) (durationOf t) forward decode)
        0 (embedAssignment size profile hsize σ)).prod := by
  let gs := (scanWords P decode (embedAssignment size profile hsize σ)).reverse
  have hgs : gs ≠ [] := by
    intro he
    have hl : gs.length = P.markedFlags.length := by simp [gs]
    simp [he] at hl
    omega
  rw [← htarget]
  change (B ^ q) gs.prod = _
  rw [coefficient_factorization_list B hB gs hgs hne hred q]
  have hl : gs.length = P.markedFlags.length := by simp [gs]
  rw [hl, ← sum_reverse (P.markedFlags.length - 1) q (segmentedListProduct B gs)]
  apply Finset.sum_congr rfl
  intro t ht
  have htlen : t.length = P.markedFlags.length := by
    simpa only [Nat.sub_add_cancel hblocks] using length_of_mem ht
  exact (blockFactors_segmentedListProduct P hblocks B size profile hsize forward decode σ
    hdecode t htlen).symm

/-- The sum is the literal coefficient of the original word for each
independent dependent-profile assignment. No operator-norm estimate, kernel
identity or factorization is assumed: all three are proved in the preceding
modules and used here. -/
theorem decoded_coefficient_sum_norm_le
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.Compressed) (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels)
    (hblocks : 1 ≤ P.markedFlags.length)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (hdecode : ∀ (σ : ∀ i, Words d (size i) (profile i)) k i,
      decode k [i] [embedAssignment size profile hsize σ i] = orientedWord (forward k i) (σ i))
    (q : ℕ) (hq : 1 ≤ q)
    (target : (∀ i, Words d (size i) (profile i)) → FreeGroup (Fin d))
    (htarget : ∀ σ, (scanWords P decode (embedAssignment size profile hsize σ)).reverse.prod = target σ)
    (hne : ∀ σ g, g ∈ (scanWords P decode (embedAssignment size profile hsize σ)).reverse → g ≠ 1)
    (hred : ∀ σ, FreeGroup.IsReduced
      ((scanWords P decode (embedAssignment size profile hsize σ)).reverse.flatMap FreeGroup.toWord)) :
    ‖∑ σ, (B ^ q) (target σ)‖ ≤
      P.singletonWeight size d * (q : ℝ) ^ (6 * Fintype.card I - 1) * ‖regular B‖ ^ q := by
  have he : (∑ σ, (B ^ q) (target σ)) =
      ∑ t ∈ compositions (P.markedFlags.length - 1) q,
        compositionCoefficient P B size profile hsize (fun k => decide (k = 0)) forward decode t := by
    simp only [compositionCoefficient]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    exact coefficient_eq_composition_sum P hblocks B hB size profile hsize forward decode σ
      (hdecode σ) (target σ) (htarget σ) (hne σ) (hred σ) q
  rw [he]
  exact composition_sum_norm_le P hP hn hc hblocks B hB size profile hsize
    (fun k => decide (k = 0)) forward decode q hq

end Nonadditivity.HaarDecodedCoefficientBound
