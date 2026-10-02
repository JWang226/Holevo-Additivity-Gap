/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarModel
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Probability.Independence.Integration

/-! # Exact first and second moments of the canonical Haar unitaries

The low-order Haar integration identities are proved directly by invariance,
row sign changes, permutation symmetry, and unitarity. No moment formula or
strong-convergence assumption is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarMoments

open MeasureTheory HaarModel
open scoped Matrix Matrix.Norms.L2Operator

variable {N : ℕ}

/-- Every fixed matrix entry is continuous on the actual compact unitary group. -/
theorem continuous_entry (i j : Fin (N + 1)) :
    Continuous (fun U : LocalUnitary N => (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j) :=
  continuous_subtype_val.matrix_elem i j

/-- The entry products needed below are integrable under normalized Haar measure. -/
theorem integrable_entry_product (i j k l : Fin (N + 1)) :
    Integrable (fun U : LocalUnitary N =>
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l)) (haar N) :=
  ((continuous_entry i j).mul (continuous_entry k l).star).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Every Haar-unitary entry has mean zero. -/
theorem integral_entry (i j : Fin (N + 1)) :
    (∫ U : LocalUnitary N, (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j ∂haar N) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := (-1 : LocalUnitary N))
  intro U
  change ((-1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) i j = - _
  simp

/-- The diagonal unitary which changes just one row sign. -/
def rowSign (i : Fin (N + 1)) : LocalUnitary N :=
  ⟨Matrix.diagonal (fun r => if r = i then (-1 : ℂ) else 1), by
    have hs : star (fun r : Fin (N + 1) => if r = i then (-1 : ℂ) else 1) =
        (fun r : Fin (N + 1) => if r = i then (-1 : ℂ) else 1) := by
      funext r
      by_cases h : r = i <;> simp [h]
    rw [Unitary.mem_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, hs,
      Matrix.diagonal_mul_diagonal, and_self]
    ext r s
    by_cases hrs : r = s
    · subst s
      by_cases h : r = i <;> simp [h]
    · simp [hrs]⟩

@[simp] theorem rowSign_mul_entry (i r s : Fin (N + 1)) (U : LocalUnitary N) :
    ((rowSign i * U : LocalUnitary N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) r s =
      (if r = i then -1 else 1) * (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) r s := by
  change (Matrix.diagonal (fun a : Fin (N + 1) => if a = i then (-1 : ℂ) else 1) * (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) r s = _
  simp [Matrix.diagonal_mul]

/-- Entry correlations in distinct rows vanish. -/
theorem integral_entry_product_of_ne (i j k l : Fin (N + 1)) (hik : i ≠ k) :
    (∫ U : LocalUnitary N,
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l) ∂haar N) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := rowSign i)
  intro U
  simp [Ne.symm hik]

/-- Every permutation of the rows is an actual unitary. -/
def rowPermutation (e : Equiv.Perm (Fin (N + 1))) : LocalUnitary N :=
  ⟨e.permMatrix ℂ, by
    rw [Unitary.mem_iff]
    change (e.permMatrix ℂ)ᴴ * e.permMatrix ℂ = 1 ∧
      e.permMatrix ℂ * (e.permMatrix ℂ)ᴴ = 1
    simp [← Matrix.permMatrix_mul]⟩

@[simp] theorem rowPermutation_mul_entry (e : Equiv.Perm (Fin (N + 1)))
    (i j : Fin (N + 1)) (U : LocalUnitary N) :
    ((rowPermutation e * U : LocalUnitary N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j =
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (e i) j := by
  change (e.permMatrix ℂ * (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) i j = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]

/-- All rows have the same same-row covariance. -/
theorem integral_same_row_eq (i k j l : Fin (N + 1)) :
    (∫ U : LocalUnitary N,
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i l) ∂haar N) =
    ∫ U : LocalUnitary N,
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l) ∂haar N := by
  simpa using (integral_mul_left_eq_self (μ := haar N)
    (fun U : LocalUnitary N =>
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l))
    (rowPermutation (Equiv.swap i k)))

/-- Summed entry correlations are the exact column-orthogonality identity. -/
theorem sum_entry_product (U : LocalUnitary N) (j l : Fin (N + 1)) :
    ∑ i, (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i l) =
      if j = l then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ => M l j)
    (Unitary.star_mul_self_of_mem U.property)
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    mul_comm, Matrix.one_apply, eq_comm] using h

/-- The same-row covariance is the normalized Kronecker delta. -/
theorem integral_same_row (i j l : Fin (N + 1)) :
    (∫ U : LocalUnitary N,
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i l) ∂haar N) =
      (if j = l then 1 else 0) / (N + 1 : ℂ) := by
  have hsum : (∑ k : Fin (N + 1), ∫ U : LocalUnitary N,
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l) ∂haar N) =
      if j = l then 1 else 0 := by
    rw [← integral_finset_sum _ (fun k _ => integrable_entry_product k j k l)]
    simp_rw [sum_entry_product]
    simp
  simp_rw [integral_same_row_eq _ i j l] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hsum
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero N : (N + 1 : ℂ) ≠ 0)).mpr
  simpa [mul_comm] using hsum

/-- Exact second entry moment of the canonical Haar unitary, in dimension `N+1`. -/
theorem integral_entry_product (i j k l : Fin (N + 1)) :
    (∫ U : LocalUnitary N,
      (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j * star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l) ∂haar N) =
      (if i = k ∧ j = l then 1 else 0) / (N + 1 : ℂ) := by
  by_cases hik : i = k
  · subst k
    simpa using integral_same_row i j l
  · simpa only [if_neg (not_and_of_not_left _ hik), zero_div] using
      integral_entry_product_of_ne i j k l hik

/-- Every Haar entry has exact second absolute moment `1/(N+1)`. -/
theorem integral_entry_norm_sq (i j : Fin (N + 1)) :
    (∫ U : LocalUnitary N,
      ‖(U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j‖ ^ 2 ∂haar N) =
        1 / (N + 1 : ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
    mul_comm (starRingEnd ℂ _)]
  simpa using integral_entry_product i j i j

/-- Haar conjugation averages every finite matrix to its scalar trace part. -/
theorem integral_twirl_entry
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i j : Fin (N + 1)) :
    (∫ U : LocalUnitary N,
      ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * A *
        (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)ᴴ) i j ∂haar N) =
      if i = j then A.trace / (N + 1 : ℂ) else 0 := by
  have he (U : LocalUnitary N) :
      ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * A *
        (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)ᴴ) i j =
      ∑ k, ∑ l, A k l * ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i k *
        star ((U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) j l)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _
    (fun l _ => (integrable_entry_product i k j l).const_mul (A k l)))]
  simp_rw [integral_finset_sum _ (fun l _ =>
    (integrable_entry_product i _ j l).const_mul (A _ l))]
  simp_rw [integral_const_mul, integral_entry_product]
  by_cases hij : i = j
  · simp [hij, mul_ite, Matrix.trace, Matrix.diag, div_eq_mul_inv, Finset.sum_mul]
  · simp [hij]

/-- The mean of every coordinate entry in the actual independent block sample is zero. -/
theorem integral_sample_entry (K n : ℕ) (a : Fin n × Fin K)
    (i j : Fin (N + 1)) :
    (∫ ω : Sample K n N,
      (ω a : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j
        ∂sampleMeasure K n N) = 0 := by
  exact (integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := a)
    (continuous_entry i j).aestronglyMeasurable).trans (integral_entry i j)

/-- Second entry moments persist in every coordinate of the product Haar model. -/
theorem integral_sample_entry_product_same (K n : ℕ) (a : Fin n × Fin K)
    (i j k l : Fin (N + 1)) :
    (∫ ω : Sample K n N,
      (ω a : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j *
        star ((ω a : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l)
        ∂sampleMeasure K n N) =
      (if i = k ∧ j = l then 1 else 0) / (N + 1 : ℂ) := by
  exact (integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := a)
    ((continuous_entry i j).mul (continuous_entry k l).star).aestronglyMeasurable).trans
      (integral_entry_product i j k l)

/-- Entries belonging to distinct sampled unitaries have zero covariance. -/
theorem integral_sample_entry_product_ne (K n : ℕ) (a b : Fin n × Fin K)
    (hab : a ≠ b) (i j k l : Fin (N + 1)) :
    (∫ ω : Sample K n N,
      (ω a : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i j *
        star ((ω b : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) k l)
        ∂sampleMeasure K n N) = 0 := by
  have hind := ((independent_coordinates K n N).indepFun hab).comp
    (continuous_entry i j).measurable (continuous_entry k l).star.measurable
  have h := hind.integral_fun_mul_eq_mul_integral
    ((continuous_entry i j).comp (continuous_apply a)).aestronglyMeasurable
    (((continuous_entry k l).comp (continuous_apply b)).star).aestronglyMeasurable
  simpa only [Function.comp_apply, integral_sample_entry, zero_mul] using h

end Nonadditivity.HaarMoments
