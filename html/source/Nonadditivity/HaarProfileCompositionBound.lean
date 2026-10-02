/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileAssignmentBound
import Mathlib.Data.List.GetD

/-! # Sum the actual profile coefficients over positive segment durations

The literal dependent-profile sums are bounded uniformly over every positive
composition of the moment order. Only marked endpoint durations contribute
polynomial losses, giving the repaired exponent for the compiled core pattern.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarProfileCompositionBound
open scoped BigOperators
open HaarOperatorPolynomial HaarProfilePadding HaarProfileCoefficient HaarPathProfiles
  NoncommutativeCS HaarProfilePatternBound HaarProfileAssignmentBound HaarTimeCompositions
  HaarMarkedCompositions

def durationOf (t : List ℕ) (k : ℕ) : ℕ := t.getD k 1

theorem durationOf_pos {t : List ℕ} (ht : ∀ a ∈ t, 0 < a) (k : ℕ) :
    1 ≤ durationOf t k := by
  unfold durationOf
  by_cases hk : k < t.length
  · rw [List.getD_eq_getElem t 1 hk]
    exact ht _ (List.getElem_mem hk)
  · rw [List.getD_eq_default t 1 (by omega)]

variable {I : Type*}

theorem ofFn_duration_succ (duration : ℕ → ℕ) (r k : ℕ) :
    List.ofFn (fun i : Fin (r + 1) => duration (k + i.val)) =
      duration k :: List.ofFn (fun i : Fin r => duration ((k + 1) + i.val)) := by
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  omega

theorem times_eq_ofFn {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (duration : ℕ → ℕ) (k : ℕ) :
    P.times duration k = List.ofFn (fun i : Fin P.markedFlags.length => duration (k + i.val)) := by
  induction P generalizing k <;>
    simp_all [EndpointSkeleton.times, EndpointSkeleton.markedFlags] <;>
    funext i <;> congr 1 <;> omega

theorem times_durationOf {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (t : List ℕ) (ht : t.length = P.markedFlags.length) :
    P.times (durationOf t) 0 = t := by
  rw [times_eq_ofFn]
  simp only [Nat.zero_add, durationOf]
  rw [← ht]
  convert (List.ofFn_getElem (xs := t)) using 1
  congr 1
  funext i
  exact List.getD_eq_getElem t 1 i.isLt

variable {E : Type*} [DecidableEq I] [Fintype I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d M : ℕ}

/-- The literal operator obtained from the actual dependent profile choices
and one list of positive durations. -/
def compositionCoefficient
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d)) (t : List ℕ) : E →L[ℂ] E :=
  ∑ σ : ∀ i, Words d (size i) (profile i),
    (P.blockFactors (blockFactor B size profile hsize ordinary (durationOf t) forward decode) 0
      (embedAssignment size profile hsize σ)).prod

theorem compositionCoefficient_norm_le
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels)
    (hblocks : 1 ≤ P.markedFlags.length)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    {q : ℕ} {t : List ℕ} (ht : t ∈ compositions (P.markedFlags.length - 1) q) :
    ‖compositionCoefficient P B size profile hsize ordinary forward decode t‖ ≤
      P.singletonWeight size d * (markedProduct P.markedFlags t : ℝ) * ‖regular B‖ ^ q := by
  have hl : t.length = P.markedFlags.length := by
    simpa only [Nat.sub_add_cancel hblocks] using length_of_mem ht
  have h := dependent_profile_sum_norm_le P hn hc B hB size profile hsize ordinary (durationOf t)
    forward decode (durationOf_pos (positive_of_mem ht)) 0
  rw [times_durationOf P t hl, sum_of_mem ht] at h
  exact h

/-- The actual grouped coefficient sum over all positive segment durations
has the repaired BC exponent. Every operator bound is proved upstream for
the literal ordinary/non-returning polynomial coefficients. -/
theorem composition_sum_norm_le
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.Compressed) (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels)
    (hblocks : 1 ≤ P.markedFlags.length)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (q : ℕ) (hq : 1 ≤ q) :
    ‖∑ t ∈ compositions (P.markedFlags.length - 1) q,
      compositionCoefficient P B size profile hsize ordinary forward decode t‖ ≤
      P.singletonWeight size d * (q : ℝ) ^ (6 * Fintype.card I - 1) * ‖regular B‖ ^ q := by
  have hexp := P.coefficient_exponent_le hP
  rw [P.profileLabels_length_eq_card hn hc] at hexp
  have hnat := (marked_composition_sum_le q hq P.markedFlags).trans
    (Nat.pow_le_pow_right hq hexp)
  have hs : (∑ t ∈ compositions (P.markedFlags.length - 1) q,
      (markedProduct P.markedFlags t : ℝ)) ≤ (q : ℝ) ^ (6 * Fintype.card I - 1) := by
    exact_mod_cast hnat
  calc
    _ ≤ ∑ t ∈ compositions (P.markedFlags.length - 1) q,
        ‖compositionCoefficient P B size profile hsize ordinary forward decode t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ compositions (P.markedFlags.length - 1) q,
        P.singletonWeight size d * (markedProduct P.markedFlags t : ℝ) * ‖regular B‖ ^ q := by
      exact Finset.sum_le_sum fun t ht => compositionCoefficient_norm_le P hn hc hblocks
        B hB size profile hsize ordinary forward decode ht
    _ = P.singletonWeight size d *
        (∑ t ∈ compositions (P.markedFlags.length - 1) q, (markedProduct P.markedFlags t : ℝ)) *
          ‖regular B‖ ^ q := by rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (P.singletonWeight_nonneg size d)) (by positivity)

end Nonadditivity.HaarProfileCompositionBound
