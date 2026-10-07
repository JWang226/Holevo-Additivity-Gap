/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClassStats
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Weighted chronological encoding of genuine path classes

The time coordinate is stored as the position of an optional mark rather
than counted again in every event. Weighted enumeration preserves the
important-event budget and avoids the exponential padding overhead.
-/

noncomputable section

namespace Nonadditivity.HaarPathClasses

open HaarPathGraph HaarPathProfiles
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- A chronological sparse code: each actual time carries at most one mark. -/
def sparseExplorationCode (P : Path V 2 m) (hm : 0 < m) :
    Fin m → Option (ExplorationMark m) :=
  fun i => if i ∈ P.importantTimes then some (explorationMark P hm i) else none

theorem eventList_eq_of_sparseCode_eq {P Q : Path V 2 m} (hm : 0 < m)
    (hcode : sparseExplorationCode P hm = sparseExplorationCode Q hm) :
    explorationEventList P hm = explorationEventList Q hm := by
  have htimes : P.importantTimes = Q.importantTimes := by
    ext i
    have hi := congrFun hcode i
    by_cases hP : i ∈ P.importantTimes <;> by_cases hQ : i ∈ Q.importantTimes <;>
      simp [sparseExplorationCode, hP, hQ] at hi ⊢
  unfold explorationEventList
  rw [← htimes]
  apply List.map_congr_left
  intro i hi
  have hP : i ∈ P.importantTimes := by simpa using hi
  have hQ : i ∈ Q.importantTimes := by simpa only [← htimes] using hP
  have hm := congrFun hcode i
  simp only [sparseExplorationCode, if_pos hP, if_pos hQ, Option.some.injEq] at hm
  exact congrArg (fun x => (i, x)) hm

def classSparseCode [Fintype V] {δ : ℕ} (hm : 0 < m)
    (C : DefectClass V m δ hm) : Fin m → Option (ExplorationMark m) :=
  sparseExplorationCode (classRepresentative hm C) hm

theorem classSparseCode_injective [Fintype V] (hm : 0 < m) (δ : ℕ) :
    Function.Injective (@classSparseCode V _ m _ δ hm) := by
  intro C D h
  apply classExplorationCode_injective hm δ
  apply Subtype.ext
  exact eventList_eq_of_sparseCode_eq hm h

def sparseCodeWeight {A I : Type*} [Fintype I] (z : ℝ) (c : I → Option A) : ℝ :=
  ∏ i, (c i).elim 1 (fun _ => z)

theorem sparseCodeWeight_nonneg {A I : Type*} [Fintype I] {z : ℝ} (hz : 0 ≤ z)
    (c : I → Option A) : 0 ≤ sparseCodeWeight z c := by
  apply Finset.prod_nonneg
  intro i _
  cases c i with
  | none => norm_num
  | some a => exact hz

theorem sum_sparseCodeWeight {A I : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (z : ℝ) :
    (∑ c : I → Option A, sparseCodeWeight z c) =
      (1 + (Fintype.card A : ℝ) * z) ^ Fintype.card I := by
  unfold sparseCodeWeight
  rw [← Fintype.prod_sum (fun (_ : I) (a : Option A) => a.elim 1 (fun _ => z))]
  simp [Fintype.sum_option, add_comm]

theorem sparseExplorationCode_weight (P : Path V 2 m) (hm : 0 < m) (z : ℝ) :
    sparseCodeWeight z (sparseExplorationCode P hm) = z ^ P.importantTimes.card := by
  have he : sparseCodeWeight z (sparseExplorationCode P hm) =
      ∏ i : Fin m, if i ∈ P.importantTimes then z else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ P.importantTimes <;> simp [sparseExplorationCode, hi]
  rw [he, Fintype.prod_ite_mem]
  simp

@[simp] theorem card_explorationMark (m : ℕ) :
    Fintype.card (ExplorationMark m) = 64 * m ^ 2 := by
  simp only [ExplorationMark, Color, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ring

/-- Exact weighted code bound on the actual defect classes. Unlike the
unweighted padded-list estimate, this retains the chronological positions. -/
theorem card_defectClass_weighted_le [Fintype V] (hm : 0 < m) (δ : ℕ)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (Fintype.card (DefectClass V m δ hm) : ℝ) * z ^ (δ + 2) ≤
      (1 + 64 * (m : ℝ) ^ 2 * z) ^ m := by
  classical
  let f := @classSparseCode V _ m _ δ hm
  have hf : Function.Injective f := classSparseCode_injective hm δ
  calc
    _ = ∑ C : DefectClass V m δ hm, z ^ (δ + 2) := by simp
    _ ≤ ∑ C : DefectClass V m δ hm, sparseCodeWeight z (f C) := by
      apply Finset.sum_le_sum
      intro C _
      rw [show f C = sparseExplorationCode (classRepresentative hm C) hm from rfl,
        sparseExplorationCode_weight]
      have hc := (classRepresentative hm C).card_importantTimes_le hm
      rw [classRepresentative_defect] at hc
      exact pow_le_pow_of_le_one hz hz1 hc
    _ = ∑ c ∈ Finset.univ.image f, sparseCodeWeight z c := by
      rw [Finset.sum_image]
      intro C _ D _ h
      exact hf h
    _ ≤ ∑ c : Fin m → Option (ExplorationMark m), sparseCodeWeight z c := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun c _ _ => sparseCodeWeight_nonneg hz c)
    _ = _ := by simp only [sum_sparseCodeWeight, card_explorationMark,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Fintype.card_fin]

theorem card_refinedDefectClass_le_coarse_mul [Fintype V] (hm : 0 < m) (δ : ℕ) :
    Fintype.card (RefinedDefectClass V m δ hm) ≤
      Fintype.card (DefectClass V m δ hm) * (4 * m ^ 2) ^ (3 * δ + 4) := by
  classical
  rw [Fintype.card_congr (refinedDefectEquiv hm δ), Fintype.card_sigma]
  calc
    _ ≤ ∑ C : DefectClass V m δ hm, (4 * m ^ 2) ^ (3 * δ + 4) := by
      apply Finset.sum_le_sum
      intro C _
      have h := card_refinedOver_le C.val hm (by decide : 0 < 2)
      have hd := classRepresentative_defect hm C
      change (Quotient.out C.val).defectTwice = δ at hd
      simpa only [hd, show 2 * 2 = 4 from rfl] using h
    _ = _ := by simp

theorem card_refinedDefectClass_weighted_le [Fintype V] (hm : 0 < m) (δ : ℕ)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (Fintype.card (RefinedDefectClass V m δ hm) : ℝ) * z ^ (δ + 2) ≤
      (1 + 64 * (m : ℝ) ^ 2 * z) ^ m * (4 * (m : ℝ) ^ 2) ^ (3 * δ + 4) := by
  have hc : (Fintype.card (RefinedDefectClass V m δ hm) : ℝ) ≤
      (Fintype.card (DefectClass V m δ hm) : ℝ) * (4 * (m : ℝ) ^ 2) ^ (3 * δ + 4) := by
    exact_mod_cast card_refinedDefectClass_le_coarse_mul (V := V) hm δ
  calc
    _ ≤ ((Fintype.card (DefectClass V m δ hm) : ℝ) *
        (4 * (m : ℝ) ^ 2) ^ (3 * δ + 4)) * z ^ (δ + 2) :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hz _)
    _ = ((Fintype.card (DefectClass V m δ hm) : ℝ) * z ^ (δ + 2)) *
        (4 * (m : ℝ) ^ 2) ^ (3 * δ + 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (card_defectClass_weighted_le (V := V) hm δ hz hz1) (by positivity)

theorem card_refined_subfamily_weighted_le [Fintype V] (hm : 0 < m) (δ : ℕ)
    (s : Finset (RefinedClass V 2 m))
    (hs : ∀ C ∈ s, classDefectTwice hm (refinedToCoarse C) = δ)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (s.card : ℝ) * z ^ (δ + 2) ≤
      (1 + 64 * (m : ℝ) ^ 2 * z) ^ m * (4 * (m : ℝ) ^ 2) ^ (3 * δ + 4) := by
  classical
  let f : s → RefinedDefectClass V m δ hm := fun C => ⟨C.val, hs C.val C.property⟩
  have hf : Function.Injective f := by
    intro C D h
    exact Subtype.ext (congrArg (fun x : RefinedDefectClass V m δ hm => x.val) h)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hc
  have hreal : (s.card : ℝ) ≤ Fintype.card (RefinedDefectClass V m δ hm) := by
    exact_mod_cast hc
  exact (mul_le_mul_of_nonneg_right hreal (pow_nonneg hz _)).trans
    (card_refinedDefectClass_weighted_le hm δ hz hz1)

end Nonadditivity.HaarPathClasses
