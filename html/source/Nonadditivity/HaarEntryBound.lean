/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMatchingSharp
import Nonadditivity.HaarWeingartenMomentBound
import Nonadditivity.HaarWeingartenInverse

/-! # Unconditional singleton-sensitive Haar entry estimates

The actual Haar integral is bounded using the constructed inverse Gram matrix.
No matching-count or inverse estimate remains as a hypothesis.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarInvariantTensor
open MeasureTheory HaarModel HaarPathMultiplicity
open scoped BigOperators

def entryList {N p : ℕ} (i j k l : Tuple N p) :=
  List.ofFn (fun a => (i a,j a)) ++ List.ofFn (fun a => (k a,l a))

theorem matchingMultiplicity_le_sharp {N p : ℕ} (hp : 0 < p)
    (i j k l : Tuple N p) (π : Perm p) :
    matchingMultiplicity i j k l π ≤
      p^(π.support.card + highMultiplicityOccurrences (entryList i j k l)/2) := by
  exact HaarMatchingSharp.card_relativeMatching_le_sharp hp i k j l π

theorem singleton_le_support_of_matching {N p : ℕ}
    (i j k l : Tuple N p) (π : Perm p)
    (h : 0 < matchingMultiplicity i j k l π) :
    (singletonEdges (entryList i j k l)).card ≤ 2*π.support.card := by
  obtain ⟨σ,hrow,hcol⟩ := Fintype.card_pos_iff.mp h
  simpa only [inv_mul_cancel_left] using
    HaarMatchingSingletons.singleton_entries_le_two_support i k j l σ (σ*π) hrow hcol

/-- A flexible numerical form, already unconditional on all combinatorics. -/
theorem norm_entry_moment_le {N p : ℕ} (hp : 0 < p) (hpd : p ≤ N+1)
    (hsize : 2*(p:ℝ) ≤ Real.sqrt (N+1))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hη : (p:ℝ) ≤ (Real.sqrt (N+1)/(2*(p:ℝ)))*η^2)
    (i j k l : Tuple N p) :
    ‖∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N‖ ≤
      (2/(N+1:ℝ)^p) * (p:ℝ)^(highMultiplicityOccurrences (entryList i j k l)/2) *
        η^(singletonEdges (entryList i j k l)).card := by
  apply norm_moment_le_of_matching_and_inverse hpd i j k l _ _
    (Real.sqrt (N+1)/(2*(p:ℝ))) η (2/(N+1:ℝ)^p)
    (by positivity) hη0 hη1 hη
  · exact matchingMultiplicity_le_sharp hp i j k l
  · exact singleton_le_support_of_matching i j k l
  · simpa only [HaarWeingartenInverse.weight, HaarPermutationSupport.distance_eq_support,
      inv_one, one_mul] using
      HaarWeingartenInverse.weingarten_weighted_sum_le N p hp hpd hsize 1

/-- With `2*p` total entries, this gives the singleton factor
`2*p / (N+1)^(1/4)` and the numerical prefactor `2`. -/
theorem norm_entry_moment_le_explicit {N p : ℕ} (hp : 0 < p) (hpd : p ≤ N+1)
    (hsize : 4*(p:ℝ)^2 ≤ Real.sqrt (N+1))
    (i j k l : Tuple N p) :
    ‖∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N‖ ≤
      (2/(N+1:ℝ)^p) * (p:ℝ)^(highMultiplicityOccurrences (entryList i j k l)/2) *
        (2*(p:ℝ)/Real.sqrt (Real.sqrt (N+1)))^
          (singletonEdges (entryList i j k l)).card := by
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hq : 0 < Real.sqrt (N+1:ℝ) := by positivity
  have hs : 0 < Real.sqrt (Real.sqrt (N+1:ℝ)) := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  apply norm_entry_moment_le hp hpd (by nlinarith) _ (by positivity)
  · apply (div_le_one hs).mpr
    nlinarith [sq_nonneg (2*(p:ℝ)-Real.sqrt (Real.sqrt (N+1:ℝ)))]
  · have he : Real.sqrt (N+1:ℝ)/(2*(p:ℝ)) *
        (2*(p:ℝ)/Real.sqrt (Real.sqrt (N+1:ℝ)))^2 = 2*(p:ℝ) := by
      field_simp
      nlinarith [hs2]
    rw [he]
    linarith

/-- The dimension hypothesis in an integer-power form, with the otherwise
separate degree-versus-dimension condition derived internally. -/
theorem norm_entry_moment_le_of_dimension {N p : ℕ} (hp : 0 < p)
    (hN : 16*(p:ℝ)^4 ≤ N+1)
    (i j k l : Tuple N p) :
    ‖∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N‖ ≤
      (2/(N+1:ℝ)^p) * (p:ℝ)^(highMultiplicityOccurrences (entryList i j k l)/2) *
        (2*(p:ℝ)/Real.sqrt (Real.sqrt (N+1)))^
          (singletonEdges (entryList i j k l)).card := by
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hp4 : (p:ℝ) ≤ (p:ℝ)^4 := by
    simpa using (pow_le_pow_right₀ hp1 (by omega : 1 ≤ 4))
  have hpd : p ≤ N+1 := by
    have : (p:ℝ) ≤ (N:ℝ)+1 := by nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ p) 4]
    exact_mod_cast this
  apply norm_entry_moment_le_explicit hp hpd
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith

/-- A common degree budget permits multiplication across independent Haar
families. It also covers an absent family (`p=0`). -/
theorem norm_entry_moment_le_uniform {N p P : ℕ} (hpP : p ≤ P)
    (hN : 16*(P:ℝ)^4 ≤ N+1)
    (i j k l : Tuple N p) :
    ‖∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N‖ ≤
      (2/(N+1:ℝ)^p) * (P:ℝ)^(highMultiplicityOccurrences (entryList i j k l)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^
          (singletonEdges (entryList i j k l)).card := by
  by_cases hp : p=0
  · subst p
    simp [HaarMixedMoments.entryMonomial, entryList, highMultiplicityOccurrences, singletonEdges]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    have hpPr : (p:ℝ) ≤ P := by exact_mod_cast hpP
    have hNp : 16*(p:ℝ)^4 ≤ N+1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpPr 4) (by norm_num)).trans hN
    apply (norm_entry_moment_le_of_dimension hp0 hNp i j k l).trans
    gcongr

end Nonadditivity.HaarInvariantTensor
