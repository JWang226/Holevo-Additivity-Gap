/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeightedMatrixInverse

/-! # Weighted absolute row sums of an actual inverse

This stronger form of entrywise inverse decay permits summing Weingarten
coefficients without paying for a second permutation count.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace Nonadditivity.WeightedMatrixInverse

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A weighted row norm of an actual inverse is bounded by the inverse of the
diagonal-dominance margin. -/
theorem weighted_inverse_sum_le (A X : Matrix ι ι ℂ) (hAX : A*X=1)
    (W : ι → ι → ℝ) (hW : ∀ i j, 0 ≤ W i j) (hdiag : ∀ i, W i i = 1)
    (htri : ∀ i k j, W i j ≤ W i k * W k j)
    {δ : ℝ} (hδ : δ < 1)
    (hrow : ∀ i, ∑ k, W i k * ‖(1-A) i k‖ ≤ δ) (i : ι) :
    ∑ j, W i j * ‖X i j‖ ≤ (1-δ)⁻¹ := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ
    (fun k => ∑ j, W k j * ‖X k j‖) Finset.univ_nonempty
  let M : ℝ := ∑ j, W a j * ‖X a j‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => mul_nonneg (hW _ _) (norm_nonneg _))
  have hmax (k : ι) : (∑ j, W k j * ‖X k j‖) ≤ M := ha k (Finset.mem_univ _)
  have hpoint (j : ι) : W a j * ‖X a j‖ ≤
      W a j * ‖(1 : Matrix ι ι ℂ) a j‖ +
        ∑ k, W a k * ‖(1-A) a k‖ * (W k j * ‖X k j‖) := by
    have hx := congrArg (fun B : Matrix ι ι ℂ => B a j) (inverse_eq_one_add_residual A X hAX)
    change X a j = (1 + (1-A)*X) a j at hx
    have hn : ‖X a j‖ ≤ ‖(1 : Matrix ι ι ℂ) a j‖ +
        ∑ k, ‖(1-A) a k‖ * ‖X k j‖ := by
      rw [hx, Matrix.add_apply, Matrix.mul_apply]
      exact (norm_add_le _ _).trans (add_le_add_right
        ((norm_sum_le _ _).trans_eq (by simp only [norm_mul])) _)
    calc
      _ ≤ W a j * (‖(1 : Matrix ι ι ℂ) a j‖ +
          ∑ k, ‖(1-A) a k‖ * ‖X k j‖) := mul_le_mul_of_nonneg_left hn (hW _ _)
      _ = W a j * ‖(1 : Matrix ι ι ℂ) a j‖ +
          ∑ k, W a j * (‖(1-A) a k‖ * ‖X k j‖) := by rw [mul_add, Finset.mul_sum]
      _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum fun k _ => by
        calc
          _ ≤ (W a k * W k j) * (‖(1-A) a k‖ * ‖X k j‖) :=
            mul_le_mul_of_nonneg_right (htri _ _ _) (by positivity)
          _ = _ := by ring)
  have hid : (∑ j, W a j * ‖(1 : Matrix ι ι ℂ) a j‖) = 1 := by
    simp [Matrix.one_apply, apply_ite norm, mul_ite, hdiag]
  have hlinear : M ≤ 1+δ*M := by
    calc
      M ≤ ∑ j, (W a j * ‖(1 : Matrix ι ι ℂ) a j‖ +
          ∑ k, W a k * ‖(1-A) a k‖ * (W k j * ‖X k j‖)) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = 1 + ∑ k, W a k * ‖(1-A) a k‖ * (∑ j, W k j * ‖X k j‖) := by
        rw [Finset.sum_add_distrib, hid, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ ≤ 1 + ∑ k, W a k * ‖(1-A) a k‖ * M :=
        add_le_add le_rfl (Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hmax k) (mul_nonneg (hW _ _) (norm_nonneg _)))
      _ = 1+(∑ k, W a k * ‖(1-A) a k‖)*M := by rw [Finset.sum_mul]
      _ ≤ 1+δ*M := add_le_add le_rfl (mul_le_mul_of_nonneg_right (hrow a) hM)
  apply (hmax i).trans
  rw [← one_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith

theorem weighted_inverse_sum_le_two (A X : Matrix ι ι ℂ) (hAX : A*X=1)
    (W : ι → ι → ℝ) (hW : ∀ i j, 0 ≤ W i j) (hdiag : ∀ i, W i i = 1)
    (htri : ∀ i k j, W i j ≤ W i k * W k j)
    (hrow : ∀ i, ∑ k, W i k * ‖(1-A) i k‖ ≤ 1/2) (i : ι) :
    ∑ j, W i j * ‖X i j‖ ≤ 2 := by
  have h := weighted_inverse_sum_le A X hAX W hW hdiag htri
    (by norm_num : (1/2:ℝ)<1) hrow i
  norm_num at h
  exact h

end Nonadditivity.WeightedMatrixInverse
