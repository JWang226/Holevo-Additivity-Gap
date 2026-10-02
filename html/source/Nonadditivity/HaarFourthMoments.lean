/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMoments

/-! # Exact fourth entry moments from Haar invariance

Explicit phase and two-row Hadamard unitaries, together with a four-phase
polarization identity, prove the first higher Haar moments.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarFourthMoments
open MeasureTheory HaarModel HaarMoments
open scoped Matrix Matrix.Norms.L2Operator
variable {N : ℕ}
abbrev Mat (N : ℕ) := Matrix (Fin (N+1)) (Fin (N+1)) ℂ

def rowPhase (i : Fin (N+1)) (z : ℂ) (hz : star z * z = 1) : LocalUnitary N :=
  ⟨Matrix.diagonal (fun r => if r = i then z else 1), by
    change (starRingEnd ℂ) z * z = 1 at hz
    rw [Unitary.mem_iff]
    constructor <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal] <;>
      ext r s <;> by_cases hrs : r = s
    · subst s; by_cases h : r = i <;> simp [h, hz]
    · simp [hrs]
    · subst s; by_cases h : r = i <;> simp [h, mul_comm z, hz]
    · simp [hrs]⟩

@[simp] theorem rowPhase_mul_entry (i r s : Fin (N+1)) (z : ℂ)
    (hz : star z * z = 1) (U : LocalUnitary N) :
    ((rowPhase i z hz * U : LocalUnitary N) : Mat N) r s =
      (if r = i then z else 1) * (U : Mat N) r s := by
  change (Matrix.diagonal (fun a : Fin (N+1) => if a = i then z else 1) * (U : Mat N)) r s = _
  simp [Matrix.diagonal_mul]

def rotationCoefficient : ℂ := (Real.sqrt 2 : ℂ)⁻¹

lemma rotationCoefficient_star : starRingEnd ℂ rotationCoefficient = rotationCoefficient := by
  simp [rotationCoefficient]

lemma rotationCoefficient_sq : rotationCoefficient ^ 2 = 1 / 2 := by
  simp [rotationCoefficient, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

lemma rotationCoefficient_norm_four : ‖rotationCoefficient‖ ^ 4 = (1:ℝ) / 4 := by
  have h := congrArg norm rotationCoefficient_sq
  norm_num [norm_pow, norm_div] at h
  nlinarith [sq_nonneg (‖rotationCoefficient‖ ^ 2)]

/-- A Hadamard transformation on two rows, and the identity on their complement. -/
def rotationMatrix (i k : Fin (N+1)) : Mat N := fun r s =>
  if r = i then rotationCoefficient * (if s = i then 1 else 0) +
    rotationCoefficient * (if s = k then 1 else 0)
  else if r = k then rotationCoefficient * (if s = i then 1 else 0) -
    rotationCoefficient * (if s = k then 1 else 0)
  else if r = s then 1 else 0

lemma rotationMatrix_mul (i k : Fin (N+1)) (M : Mat N) (r s) :
    (rotationMatrix i k * M) r s =
      if r = i then rotationCoefficient * M i s + rotationCoefficient * M k s
      else if r = k then rotationCoefficient * M i s - rotationCoefficient * M k s
      else M r s := by
  by_cases hri : r = i
  · subst r
    simp [Matrix.mul_apply, rotationMatrix, add_mul, mul_ite,
      Finset.sum_add_distrib]
  · by_cases hrk : r = k
    · subst r
      simp [Matrix.mul_apply, rotationMatrix, hri, sub_mul, mul_ite,
        Finset.sum_sub_distrib]
    · simp [Matrix.mul_apply, rotationMatrix, hri, hrk]

lemma rotationMatrix_star (i k : Fin (N+1)) (hik : i ≠ k) :
    star (rotationMatrix i k) = rotationMatrix i k := by
  ext r s
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  by_cases hri : r = i <;> by_cases hrk : r = k <;>
    by_cases hsi : s = i <;> by_cases hsk : s = k <;>
    simp_all [rotationMatrix, rotationCoefficient_star, eq_comm]

lemma rotationMatrix_sq (i k : Fin (N+1)) (hik : i ≠ k) :
    rotationMatrix i k * rotationMatrix i k = 1 := by
  ext r s
  rw [rotationMatrix_mul i k]
  by_cases hri : r = i <;> by_cases hrk : r = k <;>
    by_cases hsi : s = i <;> by_cases hsk : s = k <;>
    simp_all [rotationMatrix, Matrix.one_apply, eq_comm, ← two_mul,
      ← sq, rotationCoefficient_sq]

/-- The explicit Hadamard matrix is an actual member of the compact unitary group. -/
def rowRotation (i k : Fin (N+1)) (hik : i ≠ k) : LocalUnitary N :=
  ⟨rotationMatrix i k, by
    rw [Unitary.mem_iff, rotationMatrix_star i k hik]
    exact ⟨rotationMatrix_sq i k hik, rotationMatrix_sq i k hik⟩⟩

@[simp] lemma rowRotation_mul_entry (i k j : Fin (N+1)) (hik : i ≠ k)
    (U : LocalUnitary N) :
    ((rowRotation i k hik * U : LocalUnitary N) : Mat N) i j =
      rotationCoefficient * ((U : Mat N) i j + (U : Mat N) k j) := by
  change (rotationMatrix i k * (U : Mat N)) i j = _
  simp [rotationMatrix_mul i k, mul_add]

lemma fourth_polarization (x y : ℂ) :
    ‖x + y‖ ^ 4 + ‖x - y‖ ^ 4 + ‖x + Complex.I * y‖ ^ 4 +
      ‖x - Complex.I * y‖ ^ 4 =
    4 * ‖x‖ ^ 4 + 4 * ‖y‖ ^ 4 + 16 * (‖x‖ ^ 2 * ‖y‖ ^ 2) := by
  have he (z : ℂ) : ‖z‖ ^ 4 = (Complex.normSq z) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    ring
  simp_rw [he, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

lemma integrable_continuous {f : LocalUnitary N → ℝ} (hf : Continuous f) :
    Integrable f (haar N) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def fourthMoment (i j : Fin (N+1)) : ℝ := ∫ U : LocalUnitary N, ‖(U : Mat N) i j‖ ^ 4 ∂haar N

def mixedMoment (i k j : Fin (N+1)) : ℝ := ∫ U : LocalUnitary N,
  ‖(U : Mat N) i j‖ ^ 2 * ‖(U : Mat N) k j‖ ^ 2 ∂haar N

lemma fourthMoment_row_eq (i k j : Fin (N+1)) : fourthMoment i j = fourthMoment k j := by
  simpa [fourthMoment] using (integral_mul_left_eq_self (μ := haar N)
    (fun U : LocalUnitary N => ‖(U : Mat N) k j‖ ^ 4)
    (rowPermutation (Equiv.swap i k)))

lemma phase_sum_fourth (i k j : Fin (N+1)) (hik : i ≠ k) (z : ℂ)
    (hz : star z * z = 1) :
    (∫ U : LocalUnitary N, ‖(U : Mat N) i j + z * (U : Mat N) k j‖ ^ 4 ∂haar N) =
    ∫ U : LocalUnitary N, ‖(U : Mat N) i j + (U : Mat N) k j‖ ^ 4 ∂haar N := by
  simpa [hik] using (integral_mul_left_eq_self (μ := haar N)
    (fun U : LocalUnitary N => ‖(U : Mat N) i j + (U : Mat N) k j‖ ^ 4)
    (rowPhase k z hz))

lemma rotated_fourth (i k j : Fin (N+1)) (hik : i ≠ k) :
    (∫ U : LocalUnitary N, ‖(U : Mat N) i j + (U : Mat N) k j‖ ^ 4 ∂haar N) =
      4 * fourthMoment i j := by
  have h := integral_mul_left_eq_self (μ := haar N)
    (fun U : LocalUnitary N => ‖(U : Mat N) i j‖ ^ 4) (rowRotation i k hik)
  simp only [rowRotation_mul_entry, norm_mul, mul_pow, rotationCoefficient_norm_four,
    integral_const_mul] at h
  unfold fourthMoment
  linarith

/-- A coordinate fourth moment is twice a distinct-row mixed square moment. -/
lemma fourthMoment_eq_two_mixed (i k j : Fin (N+1)) (hik : i ≠ k) :
    fourthMoment i j = 2 * mixedMoment i k j := by
  have hm := phase_sum_fourth i k j hik (-1) (by simp)
  have hi := phase_sum_fourth i k j hik Complex.I (by simp)
  have hmi := phase_sum_fourth i k j hik (-Complex.I) (by simp)
  simp only [neg_one_mul, ← sub_eq_add_neg] at hm
  simp only [neg_mul, ← sub_eq_add_neg] at hmi
  have hpol := integral_congr_ae (μ := haar N)
    (Filter.Eventually.of_forall fun U : LocalUnitary N => fourth_polarization
      ((U : Mat N) i j) ((U : Mat N) k j))
  have hc₁ := (continuous_entry i j).norm.pow 4
  have hc₂ := (continuous_entry k j).norm.pow 4
  have hp := ((continuous_entry i j).add (continuous_entry k j)).norm.pow 4
  have hm' := ((continuous_entry i j).sub (continuous_entry k j)).norm.pow 4
  have hi' := ((continuous_entry i j).add
    ((continuous_entry k j).const_mul Complex.I)).norm.pow 4
  have hmi' := ((continuous_entry i j).sub
    ((continuous_entry k j).const_mul Complex.I)).norm.pow 4
  have hcross := ((continuous_entry i j).norm.pow 2).mul
    ((continuous_entry k j).norm.pow 2)
  have h₁ := integral_add (integrable_continuous ((hp.add hm').add hi'))
    (integrable_continuous hmi')
  have h₂ := integral_add (integrable_continuous (hp.add hm')) (integrable_continuous hi')
  have h₃ := integral_add (integrable_continuous hp) (integrable_continuous hm')
  have h₄ := integral_add (integrable_continuous ((hc₁.const_mul 4).add (hc₂.const_mul 4)))
    (integrable_continuous (hcross.const_mul 16))
  have h₅ := integral_add (integrable_continuous (hc₁.const_mul 4))
    (integrable_continuous (hc₂.const_mul 4))
  simp only [Pi.add_apply, Pi.mul_apply] at h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅] at hpol
  simp only [integral_const_mul] at hpol
  rw [hm, hi, hmi, rotated_fourth i k j hik] at hpol
  change 4 * fourthMoment i j + 4 * fourthMoment i j + 4 * fourthMoment i j +
    4 * fourthMoment i j = 4 * fourthMoment i j + 4 * fourthMoment k j +
      16 * mixedMoment i k j at hpol
  rw [← fourthMoment_row_eq i k j] at hpol
  linarith

lemma column_sum_norm_sq (U : LocalUnitary N) (j : Fin (N+1)) :
    ∑ k, ‖(U : Mat N) k j‖ ^ 2 = 1 := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self,
    mul_comm (starRingEnd ℂ _)]
  simpa using HaarMoments.sum_entry_product U j j

lemma mixedMoment_self (i j : Fin (N+1)) : mixedMoment i i j = fourthMoment i j := by
  unfold mixedMoment fourthMoment
  apply integral_congr_ae
  filter_upwards [] with U
  ring

lemma sum_mixedMoment (i j : Fin (N+1)) :
    ∑ k, mixedMoment i k j = 1 / (N+1:ℝ) := by
  unfold mixedMoment
  have hs := integral_finset_sum Finset.univ (fun k _ => integrable_continuous
    (((continuous_entry i j).norm.pow 2).mul ((continuous_entry k j).norm.pow 2)))
  simp only [Pi.mul_apply] at hs
  rw [← hs]
  simp_rw [← Finset.mul_sum, column_sum_norm_sq, mul_one]
  exact integral_entry_norm_sq i j

/-- Exact fourth absolute moment of every Haar-unitary entry. -/
theorem integral_entry_norm_four (i j : Fin (N+1)) :
    (∫ U : LocalUnitary N, ‖(U : Mat N) i j‖ ^ 4 ∂haar N) =
      2 / ((N+1:ℝ) * (N+2:ℝ)) := by
  have hm (k : Fin (N+1)) : mixedMoment i k j =
      if k = i then fourthMoment i j else fourthMoment i j / 2 := by
    by_cases hki : k = i
    · subst k; simp [mixedMoment_self]
    · rw [if_neg hki]
      have h := fourthMoment_eq_two_mixed i k j (Ne.symm hki)
      linarith
  have h := sum_mixedMoment i j
  simp_rw [hm] at h
  have he (k : Fin (N+1)) :
      (if k = i then fourthMoment i j else fourthMoment i j / 2) =
      (if k = i then fourthMoment i j / 2 else 0) + fourthMoment i j / 2 := by
    split <;> ring
  simp_rw [he] at h
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  have hN₁ : (N+1:ℝ) ≠ 0 := by positivity
  have hN₂ : (N+2:ℝ) ≠ 0 := by positivity
  change fourthMoment i j = _
  apply (eq_div_iff (mul_ne_zero hN₁ hN₂)).mpr
  have h' := (eq_div_iff hN₁).mp h
  nlinarith

/-- Exact mixed square moment for two distinct rows in the same Haar column. -/
theorem integral_entry_norm_sq_mul_norm_sq (i k j : Fin (N+1)) (hik : i ≠ k) :
    (∫ U : LocalUnitary N, ‖(U : Mat N) i j‖ ^ 2 * ‖(U : Mat N) k j‖ ^ 2 ∂haar N) =
      1 / ((N+1:ℝ) * (N+2:ℝ)) := by
  have h := fourthMoment_eq_two_mixed i k j hik
  have hf : fourthMoment i j = 2 / ((N+1:ℝ) * (N+2:ℝ)) := integral_entry_norm_four i j
  rw [hf] at h
  change mixedMoment i k j = _
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  linarith

end Nonadditivity.HaarFourthMoments
