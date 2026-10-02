/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileOrientation
import Nonadditivity.HaarProfilePadding

/-! # Actual ordinary and non-returning whole-block profile coefficients

Every norm estimate in this file is proved for the actual operator polynomial.
The ordinary/non-returning switch accommodates the initial block of the
last-return expansion. Zero padding preserves the sharp endpoint factors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarProfileBlockCoefficients
open scoped BigOperators
open HaarOperatorPolynomial HaarNonbacktracking HaarProfileCoefficient
  HaarProfilePadding HaarPathProfiles NoncommutativeCS

variable {G E : Type*} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A single coefficient of a killed-return polynomial has no length loss. -/
theorem killed_coefficient_norm_le (A : Polynomial G E) (n : ℕ) (g : G) :
    ‖killedPolynomial A 1 n g‖ ≤ ‖regular A‖ ^ n := by
  have hone : ‖regular (1 : Polynomial G E)‖ ≤ 1 := by
    rw [map_one]
    exact ContinuousLinearMap.norm_id_le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := killed_energy A 1 n {g} x
  simp only [Finset.sum_singleton] at h
  rw [mul_pow]
  apply h.trans
  gcongr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (pow_nonneg (norm_nonneg _) n)

def blockPolynomial (A : Polynomial G E) (ordinary : Bool) (n : ℕ) : Polynomial G E :=
  if ordinary then A ^ n else killedPolynomial A 1 n

theorem block_coefficient_norm_le (A : Polynomial G E) (ordinary : Bool)
    {n : ℕ} (hn : 1 ≤ n) (g : G) :
    ‖blockPolynomial A ordinary n g‖ ≤ ‖regular A‖ ^ n := by
  cases ordinary
  · exact killed_coefficient_norm_le A n g
  · exact (coefficient_norm_le (A ^ n) g).trans (by
      rw [map_pow]
      exact norm_pow_le' _ (by omega))

variable {d k m : ℕ}

def family (A : Polynomial (FreeGroup (Fin d)) E) (ordinary : Bool) (n : ℕ)
    (forward : Bool) (p : Profile (Color d)) (w : Words d k p) : E →L[ℂ] E :=
  blockPolynomial A ordinary n (orientedWord forward w)

theorem family_endpoint_bounds (A : Polynomial (FreeGroup (Fin d)) E)
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1) (ordinary : Bool)
    {n : ℕ} (hn : 1 ≤ n) (forward : Bool) (p : Profile (Color d)) :
    Real.sqrt ‖columnGram (family (k := k) A ordinary n forward p)‖ ≤
      (n : ℝ) * ‖regular A‖ ^ n ∧
    Real.sqrt ‖rowGram (family (k := k) A ordinary n forward p)‖ ≤
      (n : ℝ) * ‖regular A‖ ^ n := by
  cases ordinary
  · have he : family (k := k) A false n forward p =
        orientedCoefficients A (n - 1) forward p := by
      funext w
      simp only [family, blockPolynomial, Bool.false_eq_true, if_false,
        orientedCoefficients, Nat.sub_add_cancel hn]
    rw [he]
    simpa only [Nat.sub_add_cancel hn] using oriented_endpoint_bounds (k := k) A hA
      (n - 1) forward p
  · have hnorm : ‖regular (A ^ n)‖ ≤ ‖regular A‖ ^ n := by
      rw [map_pow]
      exact norm_pow_le' _ (by omega)
    have hmul : ‖regular A‖ ^ n ≤ (n : ℝ) * ‖regular A‖ ^ n := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      simpa using mul_le_mul_of_nonneg_right hn' (pow_nonneg (norm_nonneg _) n)
    constructor
    · exact (Real.sqrt_le_sqrt (coefficient_columnGram_le (A ^ n)
        (orientedWord forward) (orientedWord_injective forward))).trans (by
        rw [Real.sqrt_sq (norm_nonneg _)]
        exact hnorm.trans hmul)
    · exact (Real.sqrt_le_sqrt (coefficient_rowGram_le (A ^ n)
        (orientedWord forward) (orientedWord_injective forward))).trans (by
        rw [Real.sqrt_sq (norm_nonneg _)]
        exact hnorm.trans hmul)

theorem family_singleton_bound (A : Polynomial (FreeGroup (Fin d)) E)
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1) (ordinary : Bool)
    {n : ℕ} (hn : 1 ≤ n) (forward : Bool) (p : Profile (Color d)) :
    ‖∑ w : Words d k p, family A ordinary n forward p w‖ ≤
      Real.sqrt (((2 * d) ^ k : ℕ) : ℝ) * ((n : ℝ) * ‖regular A‖ ^ n) := by
  have hc : (Fintype.card (Words d k p) : ℝ) ≤ (((2 * d) ^ k : ℕ) : ℝ) := by
    exact_mod_cast card_words_le d k p
  exact (HaarCoefficientBounds.singleton_sum_norm_le _).trans
    (mul_le_mul (Real.sqrt_le_sqrt hc)
      (family_endpoint_bounds (k := k) A hA ordinary hn forward p).1
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

def paddedFamily (A : Polynomial (FreeGroup (Fin d)) E) (ordinary : Bool) (n : ℕ)
    (forward : Bool) (p : Profile (Color d)) (hk : k ≤ m) : Palette d m → E →L[ℂ] E :=
  Function.extend (embedWords hk) (family A ordinary n forward p) 0

theorem padded_endpoint_bounds (A : Polynomial (FreeGroup (Fin d)) E)
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1) (ordinary : Bool)
    {n : ℕ} (hn : 1 ≤ n) (forward : Bool) (p : Profile (Color d)) (hk : k ≤ m) :
    Real.sqrt ‖columnGram (paddedFamily A ordinary n forward p hk)‖ ≤
      (n : ℝ) * ‖regular A‖ ^ n ∧
    Real.sqrt ‖rowGram (paddedFamily A ordinary n forward p hk)‖ ≤
      (n : ℝ) * ‖regular A‖ ^ n := by
  unfold paddedFamily
  rw [columnGram_extend_zero _ (embedWords_injective hk),
    rowGram_extend_zero _ (embedWords_injective hk)]
  exact family_endpoint_bounds A hA ordinary hn forward p

theorem padded_singleton_bound (A : Polynomial (FreeGroup (Fin d)) E)
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1) (ordinary : Bool)
    {n : ℕ} (hn : 1 ≤ n) (forward : Bool) (p : Profile (Color d)) (hk : k ≤ m) :
    ‖∑ j : Palette d m, paddedFamily A ordinary n forward p hk j‖ ≤
      Real.sqrt (((2 * d) ^ k : ℕ) : ℝ) * ((n : ℝ) * ‖regular A‖ ^ n) := by
  rw [paddedFamily, sum_extend_zero _ (embedWords_injective hk)]
  exact family_singleton_bound A hA ordinary hn forward p

theorem padded_norm_le (A : Polynomial (FreeGroup (Fin d)) E) (ordinary : Bool)
    {n : ℕ} (hn : 1 ≤ n) (forward : Bool) (p : Profile (Color d)) (hk : k ≤ m)
    (j : Palette d m) :
    ‖paddedFamily A ordinary n forward p hk j‖ ≤ ‖regular A‖ ^ n := by
  exact norm_extend_zero_le _ (embedWords_injective hk) _ _ (by positivity)
    (fun w => block_coefficient_norm_le A ordinary hn (orientedWord forward w)) j

end Nonadditivity.HaarProfileBlockCoefficients
