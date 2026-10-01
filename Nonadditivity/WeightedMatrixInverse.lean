/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # Entrywise inverse bounds from weighted row sums

The argument uses a largest weighted entry of an actual inverse column.
It avoids an infinite Neumann series and works for any submultiplicative
pair weight, including exponentials of permutation distance.
-/

noncomputable section
namespace Nonadditivity.WeightedMatrixInverse
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem inverse_eq_one_add_residual (A X : Matrix ι ι ℂ) (hAX : A*X=1) :
    X = 1 + (1-A)*X := by
  rw [Matrix.sub_mul, Matrix.one_mul, hAX]
  abel

/-- Small weighted row sums force decay of every entry of an actual inverse.
The same weight may be asymmetric; only its triangle inequality is needed. -/
theorem weighted_inverse_entry_le (A X : Matrix ι ι ℂ) (hAX : A*X=1)
    (W : ι → ι → ℝ) (hW : ∀ i j, 0 ≤ W i j) (hdiag : ∀ i, W i i = 1)
    (htri : ∀ i k j, W i j ≤ W i k * W k j)
    {δ : ℝ} (hδ : δ < 1)
    (hrow : ∀ i, ∑ k, W i k * ‖(1-A) i k‖ ≤ δ) (i j : ι) :
    W i j * ‖X i j‖ ≤ (1-δ)⁻¹ := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ
    (fun k => W k j * ‖X k j‖) Finset.univ_nonempty
  let M := W a j * ‖X a j‖
  have hM : 0 ≤ M := mul_nonneg (hW _ _) (norm_nonneg _)
  have hmax (k : ι) : W k j * ‖X k j‖ ≤ M := ha k (Finset.mem_univ _)
  have hid : W a j * ‖(1 : Matrix ι ι ℂ) a j‖ ≤ 1 := by
    by_cases h : a=j
    · subst a
      simp [hdiag]
    · simp [h]
  have hx := congrArg (fun B : Matrix ι ι ℂ => B a j) (inverse_eq_one_add_residual A X hAX)
  change X a j = (1 + (1-A)*X) a j at hx
  have hn : ‖X a j‖ ≤ ‖(1 : Matrix ι ι ℂ) a j‖ +
      ∑ k, ‖(1-A) a k‖ * ‖X k j‖ := by
    rw [hx, Matrix.add_apply, Matrix.mul_apply]
    exact (norm_add_le _ _).trans (add_le_add_right
      ((norm_sum_le _ _).trans_eq (by simp only [norm_mul])) _)
  have hterm (k : ι) :
      W a j * (‖(1-A) a k‖ * ‖X k j‖) ≤ W a k * ‖(1-A) a k‖ * M := by
    calc
      _ ≤ (W a k * W k j) * (‖(1-A) a k‖ * ‖X k j‖) :=
        mul_le_mul_of_nonneg_right (htri _ _ _) (by positivity)
      _ = (W a k * ‖(1-A) a k‖) * (W k j * ‖X k j‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmax k) (mul_nonneg (hW _ _) (norm_nonneg _))
  have hlinear : M ≤ 1+δ*M := by
    calc
      M ≤ W a j * (‖(1 : Matrix ι ι ℂ) a j‖ +
          ∑ k, ‖(1-A) a k‖ * ‖X k j‖) := mul_le_mul_of_nonneg_left hn (hW _ _)
      _ = W a j * ‖(1 : Matrix ι ι ℂ) a j‖ +
          ∑ k, W a j * (‖(1-A) a k‖ * ‖X k j‖) := by rw [mul_add, Finset.mul_sum]
      _ ≤ 1 + ∑ k, W a k * ‖(1-A) a k‖ * M :=
        add_le_add hid (Finset.sum_le_sum (fun k _ => hterm k))
      _ = 1+(∑ k, W a k * ‖(1-A) a k‖)*M := by rw [Finset.sum_mul]
      _ ≤ 1+δ*M := add_le_add_right (mul_le_mul_of_nonneg_right (hrow a) hM) _
  apply (hmax i).trans
  rw [← one_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith

theorem weighted_inverse_entry_le_two (A X : Matrix ι ι ℂ) (hAX : A*X=1)
    (W : ι → ι → ℝ) (hW : ∀ i j, 0 ≤ W i j) (hdiag : ∀ i, W i i = 1)
    (htri : ∀ i k j, W i j ≤ W i k * W k j)
    (hrow : ∀ i, ∑ k, W i k * ‖(1-A) i k‖ ≤ 1/2) (i j : ι) :
    W i j * ‖X i j‖ ≤ 2 := by
  have h := weighted_inverse_entry_le A X hAX W hW hdiag htri
    (by norm_num : (1/2 : ℝ)<1) hrow i j
  norm_num at h
  exact h

end Nonadditivity.WeightedMatrixInverse
