/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPermutationSupport
import Nonadditivity.WeightedMatrixInverse
import Nonadditivity.HaarWeingartenInverseSum
import Nonadditivity.HaarWeingartenCycles
import Mathlib.Order.Interval.Finset.Nat

/-! # Weighted inverse bounds for permutation Gram matrices

The number of permutations in a Hamming-distance layer is polynomial in the
degree. Summing those layers yields a uniform inverse bound, with no factorial
loss in the number of permutations.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarWeingartenInverse
open HaarPermutationSupport
open scoped BigOperators Matrix

theorem geometric_tail_le_half (p : ℕ) :
    (∑ d ∈ Finset.Icc 2 p, (1/2:ℝ)^d) ≤ 1/2 := by
  have hs : ∀ n : ℕ, (∑ d ∈ Finset.Icc 2 (n+1), (1/2:ℝ)^d) ≤
      1/2-(1/2:ℝ)^(n+1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n+1+1)]
      have he : (1/2:ℝ)^(n+1+1) = (1/2:ℝ)^(n+1)/2 := by rw [pow_succ]; ring
      rw [he]
      linarith
  cases p with
  | zero => norm_num
  | succ n => exact (hs n).trans (by linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (n+1)])

def weight (p : ℕ) (q : ℝ) (σ τ : Equiv.Perm (Fin p)) : ℝ :=
  (q/(2*(p:ℝ)))^(distance σ τ)

theorem weighted_row_sum_le (p : ℕ) (hp : 0 < p) (q : ℝ) (hq : 0 < q)
    (A : Matrix (Equiv.Perm (Fin p)) (Equiv.Perm (Fin p)) ℂ)
    (hdiag : ∀ σ, A σ σ = 1)
    (hA : ∀ σ τ, σ ≠ τ → ‖A σ τ‖ ≤ (q⁻¹)^(distance σ τ))
    (σ : Equiv.Perm (Fin p)) :
    (∑ τ, weight p q σ τ * ‖(1-A) σ τ‖) ≤ 1/2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  let c : ℝ := 1/(2*(p:ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hterm (τ : Equiv.Perm (Fin p)) (hne : τ ≠ σ) :
      weight p q σ τ * ‖(1-A) σ τ‖ ≤ c^(distance σ τ) := by
    have hne' := Ne.symm hne
    have hz : (1-A) σ τ = -A σ τ := by simp [hne']
    rw [hz, norm_neg]
    calc
      _ ≤ weight p q σ τ * (q⁻¹)^(distance σ τ) :=
        mul_le_mul_of_nonneg_left (hA σ τ hne') (by unfold weight; positivity)
      _ = c^(distance σ τ) := by
        unfold weight c
        rw [← mul_pow]
        congr 1
        field_simp
  have hsum : (∑ τ, weight p q σ τ * ‖(1-A) σ τ‖) ≤
      ∑ τ ∈ Finset.univ.erase σ, c^(distance σ τ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ σ)]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, hdiag, sub_self, norm_zero,
      mul_zero, add_zero]
    exact Finset.sum_le_sum (fun τ hτ => hterm τ (Finset.mem_erase.mp hτ).1)
  have hfiber : (∑ τ ∈ Finset.univ.erase σ, c^(distance σ τ)) =
      ∑ d ∈ Finset.Icc 2 p,
        ∑ τ ∈ (Finset.univ.erase σ).filter (fun τ => distance σ τ=d), c^d := by
    symm
    have hmap : ∀ τ ∈ Finset.univ.erase σ, distance σ τ ∈ Finset.Icc 2 p := by
      intro τ hτ
      exact Finset.mem_Icc.mpr ⟨two_le_distance_of_ne σ τ (Ne.symm (Finset.mem_erase.mp hτ).1),
        by simpa using distance_le_card σ τ⟩
    simpa using Finset.sum_fiberwise_of_maps_to' hmap (fun d => c^d)
  have hlayer (d : ℕ) :
      ((Finset.univ.erase σ).filter (fun τ => distance σ τ=d)).card ≤ p^d := by
    calc
      _ ≤ (Finset.univ.filter (fun τ : Equiv.Perm (Fin p) => distance σ τ=d)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
      _ = Fintype.card {τ : Equiv.Perm (Fin p) // distance σ τ=d} := by
        simp [Fintype.card_subtype]
      _ ≤ p^d := by simpa using card_distance_layer_le_pow σ d
  calc
    _ ≤ ∑ τ ∈ Finset.univ.erase σ, c^(distance σ τ) := hsum
    _ = _ := hfiber
    _ ≤ ∑ d ∈ Finset.Icc 2 p, (1/2:ℝ)^d := by
      apply Finset.sum_le_sum
      intro d hd
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ (p:ℝ)^d * c^d := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc d)
          exact_mod_cast hlayer d
        _ = (1/2:ℝ)^d := by
          rw [← mul_pow]
          congr 1
          dsimp [c]
          field_simp
    _ ≤ _ := geometric_tail_le_half p

/-- Hamming decay of the inverse of a normalized Gram matrix. -/
theorem inverse_entry_bound (p : ℕ) (hp : 0 < p) (q : ℝ)
    (hq : 2*(p:ℝ) ≤ q)
    (A X : Matrix (Equiv.Perm (Fin p)) (Equiv.Perm (Fin p)) ℂ)
    (hAX : A*X=1) (hdiag : ∀ σ, A σ σ=1)
    (hA : ∀ σ τ, σ ≠ τ → ‖A σ τ‖ ≤ (q⁻¹)^(distance σ τ))
    (σ τ : Equiv.Perm (Fin p)) :
    weight p q σ τ * ‖X σ τ‖ ≤ 2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hr : 1 ≤ q/(2*(p:ℝ)) := (le_div_iff₀ (by positivity)).mpr (by simpa using hq)
  apply WeightedMatrixInverse.weighted_inverse_entry_le_two A X hAX (weight p q)
  · intro σ τ
    unfold weight
    positivity
  · intro σ
    simp [weight]
  · intro σ κ τ
    unfold weight
    rw [← pow_add]
    exact pow_le_pow_right₀ hr (distance_triangle σ κ τ)
  · exact weighted_row_sum_le p hp q hq0 A hdiag hA

theorem inverse_sum_bound (p : ℕ) (hp : 0 < p) (q : ℝ)
    (hq : 2*(p:ℝ) ≤ q)
    (A X : Matrix (Equiv.Perm (Fin p)) (Equiv.Perm (Fin p)) ℂ)
    (hAX : A*X=1) (hdiag : ∀ σ, A σ σ=1)
    (hA : ∀ σ τ, σ ≠ τ → ‖A σ τ‖ ≤ (q⁻¹)^(distance σ τ))
    (σ : Equiv.Perm (Fin p)) :
    (∑ τ, weight p q σ τ * ‖X σ τ‖) ≤ 2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hr : 1 ≤ q/(2*(p:ℝ)) := (le_div_iff₀ (by positivity)).mpr (by simpa using hq)
  apply WeightedMatrixInverse.weighted_inverse_sum_le_two A X hAX (weight p q)
  · intro σ τ
    unfold weight
    positivity
  · intro σ
    simp [weight]
  · intro σ κ τ
    unfold weight
    rw [← pow_add]
    exact pow_le_pow_right₀ hr (distance_triangle σ κ τ)
  · exact weighted_row_sum_le p hp q hq0 A hdiag hA

open HaarInvariantTensor in
/-- A uniform weighted absolute row bound for the actual inverse Haar Gram
matrix. Both the matrix and its inverse are the constructed invariant-tensor
objects, and the only premises are explicit numerical dimension bounds. -/
theorem weingarten_weighted_sum_le (N p : ℕ) (hp : 0 < p) (hpd : p ≤ N+1)
    (hsize : 2*(p:ℝ) ≤ Real.sqrt (N+1)) (σ : Perm p) :
    (∑ τ, weight p (Real.sqrt (N+1)) σ τ * ‖weingarten N p σ τ‖) ≤
      2/(N+1:ℝ)^p := by
  let r : ℝ := (N+1:ℝ)^p
  let q : ℝ := Real.sqrt (N+1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  let A : Matrix (Perm p) (Perm p) ℂ := r⁻¹ • gram N p
  let X : Matrix (Perm p) (Perm p) ℂ := r • weingarten N p
  have hAX : A*X=1 := by
    dsimp [A,X]
    rw [smul_mul_smul_comm, gram_mul_weingarten hpd, inv_mul_cancel₀ (ne_of_gt hr)]
    ext σ τ
    simp
  have hdiag (σ : Perm p) : A σ σ=1 := by
    change r⁻¹ • gram N p σ σ = 1
    rw [gram_apply_self]
    have he : (N+1:ℂ)^p = (r:ℂ) := by dsimp [r]; norm_cast
    rw [he]
    change (r⁻¹:ℝ) • (r:ℂ) = 1
    simp only [Complex.real_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (ne_of_gt hr), Complex.ofReal_one]
  have hA (σ τ : Perm p) (_hne : σ ≠ τ) : ‖A σ τ‖ ≤ q⁻¹^(distance σ τ) := by
    have hs : ‖A σ τ‖ = r⁻¹*‖gram N p σ τ‖ := by
      simp [A, Matrix.smul_apply, Real.norm_eq_abs, abs_of_pos hr]
    have hg := HaarWeingartenCycles.norm_gram_mul_sqrt_pow_le N p σ τ
    rw [← distance_eq_support] at hg
    change ‖gram N p σ τ‖ * q^(distance σ τ) ≤ r at hg
    rw [inv_pow, ← one_div]
    apply (le_div_iff₀ (pow_pos hq _)).mpr
    rw [hs, mul_assoc]
    calc
      _ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hr.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hr)
  have h := inverse_sum_bound p hp q hsize A X hAX hdiag hA σ
  have hnorm (τ : Perm p) : ‖X σ τ‖ = r*‖weingarten N p σ τ‖ := by
    simp [X, Matrix.smul_apply, Real.norm_eq_abs, abs_of_pos hr]
  simp_rw [hnorm] at h
  apply (le_div_iff₀ hr).mpr
  calc
    _ = ∑ τ, weight p q σ τ * (r*‖weingarten N p σ τ‖) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      ring
    _ ≤ 2 := h

end Nonadditivity.HaarWeingartenInverse
