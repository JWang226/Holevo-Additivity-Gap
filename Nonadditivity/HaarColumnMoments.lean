/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarFourthMoments
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Arbitrary moments of a Haar column

The argument uses exact two-row rotations and coefficient comparison in a
finite polynomial.  It never assumes a Gaussian description of Haar measure.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarColumnMoments
open MeasureTheory HaarModel HaarMoments HaarFourthMoments Polynomial
open scoped Matrix Matrix.Norms.L2Operator
variable {N : ℕ}

def rowRotationMatrix (i k : Fin (N+1)) (a b : ℝ) : Mat N := fun r s =>
  if r = i then (a:ℂ) * (if s = i then 1 else 0) +
    (b:ℂ) * (if s = k then 1 else 0)
  else if r = k then (b:ℂ) * (if s = i then 1 else 0) -
    (a:ℂ) * (if s = k then 1 else 0)
  else if r = s then 1 else 0

lemma rowRotationMatrix_mul (i k : Fin (N+1)) (a b : ℝ) (M : Mat N) (r s) :
    (rowRotationMatrix i k a b * M) r s =
      if r = i then (a:ℂ) * M i s + (b:ℂ) * M k s
      else if r = k then (b:ℂ) * M i s - (a:ℂ) * M k s
      else M r s := by
  by_cases hri : r = i
  · subst r
    simp [Matrix.mul_apply, rowRotationMatrix, add_mul, mul_ite,
      Finset.sum_add_distrib]
  · by_cases hrk : r = k
    · subst r
      simp [Matrix.mul_apply, rowRotationMatrix, hri, sub_mul, mul_ite,
        Finset.sum_sub_distrib]
    · simp [Matrix.mul_apply, rowRotationMatrix, hri, hrk]

lemma rowRotationMatrix_star (i k : Fin (N+1)) (hik : i ≠ k) (a b : ℝ) :
    star (rowRotationMatrix i k a b) = rowRotationMatrix i k a b := by
  ext r s
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  by_cases hri : r = i <;> by_cases hrk : r = k <;>
    by_cases hsi : s = i <;> by_cases hsk : s = k <;>
    simp_all [rowRotationMatrix, eq_comm]

lemma rowRotationMatrix_sq (i k : Fin (N+1)) (hik : i ≠ k)
    (a b : ℝ) (hab : a^2 + b^2 = 1) :
    rowRotationMatrix i k a b * rowRotationMatrix i k a b = 1 := by
  have hab' : (a:ℂ)^2 + (b:ℂ)^2 = 1 := by exact_mod_cast hab
  clear hab'
  ext r s
  rw [rowRotationMatrix_mul]
  by_cases hri : r = i <;> by_cases hrk : r = k <;>
    by_cases hsi : s = i <;> by_cases hsk : s = k <;>
    simp_all [rowRotationMatrix, Matrix.one_apply, eq_comm] <;>
    first | ring1 |
      (have hc : (a:ℂ)^2 + (b:ℂ)^2 = 1 := by exact_mod_cast hab
       linear_combination hc)

def rotation (i k : Fin (N+1)) (hik : i ≠ k)
    (a b : ℝ) (hab : a^2 + b^2 = 1) : LocalUnitary N :=
  ⟨rowRotationMatrix i k a b, by
    rw [Unitary.mem_iff, rowRotationMatrix_star i k hik]
    exact ⟨rowRotationMatrix_sq i k hik a b hab,
      rowRotationMatrix_sq i k hik a b hab⟩⟩

@[simp] lemma rotation_mul_entry (i k j : Fin (N+1)) (hik : i ≠ k)
    (a b : ℝ) (hab : a^2 + b^2 = 1) (U : LocalUnitary N) :
    ((rotation i k hik a b hab * U : LocalUnitary N) : Mat N) i j =
      (a:ℂ) * (U : Mat N) i j + (b:ℂ) * (U : Mat N) k j := by
  change (rowRotationMatrix i k a b * (U : Mat N)) i j = _
  simp [rowRotationMatrix_mul]

def moment (i j : Fin (N+1)) (p : ℕ) : ℝ :=
  ∫ U : LocalUnitary N, ‖(U : Mat N) i j‖^(2*p) ∂haar N

lemma moment_zero (i j : Fin (N+1)) : moment i j 0 = 1 := by
  simp [moment]

lemma moment_one (i j : Fin (N+1)) : moment i j 1 = 1 / (N+1:ℝ) := by
  simpa [moment] using integral_entry_norm_sq i j

lemma moment_rotation (i k j : Fin (N+1)) (hik : i ≠ k)
    (a b : ℝ) (hab : a^2 + b^2 = 1) (p : ℕ) :
    (∫ U : LocalUnitary N,
      ‖(a:ℂ) * (U : Mat N) i j + (b:ℂ) * (U : Mat N) k j‖^(2*p) ∂haar N) =
        moment i j p := by
  simpa [moment] using integral_mul_left_eq_self (μ := haar N)
    (fun U : LocalUnitary N => ‖(U : Mat N) i j‖^(2*p)) (rotation i k hik a b hab)

lemma moment_add (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) (t : ℝ) :
    (∫ U : LocalUnitary N,
      ‖(U : Mat N) i j + (t:ℂ) * (U : Mat N) k j‖^(2*p) ∂haar N) =
        (1+t^2)^p * moment i j p := by
  let a : ℝ := (Real.sqrt (1+t^2))⁻¹
  have ht : 0 < 1+t^2 := by positivity
  have ha : a^2 * (1+t^2) = 1 := by
    dsimp [a]
    rw [inv_pow, Real.sq_sqrt ht.le, inv_mul_cancel₀ ht.ne']
  have hab : a^2 + (a*t)^2 = 1 := by nlinarith
  have hr := moment_rotation i k j hik a (a*t) hab p
  have he (x y : ℂ) : (a:ℂ)*x + ((a*t:ℝ):ℂ)*y = (a:ℂ)*(x+(t:ℂ)*y) := by
    push_cast
    ring
  simp_rw [he, norm_mul, mul_pow, integral_const_mul] at hr
  have hp : ‖(a:ℂ)‖^(2*p) * (1+t^2)^p = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs, ← mul_pow, ha, one_pow]
  let Ival : ℝ := ∫ U : LocalUnitary N,
    ‖(U : Mat N) i j + (t:ℂ) * (U : Mat N) k j‖^(2*p) ∂haar N
  change Ival = _
  change ‖(a:ℂ)‖^(2*p) * Ival = _ at hr
  calc
    Ival = (‖(a:ℂ)‖^(2*p) * (1+t^2)^p) * Ival := by rw [hp, one_mul]
    _ = (1+t^2)^p * (‖(a:ℂ)‖^(2*p) * Ival) := by ring
    _ = _ := by rw [hr]

/-- Integrate a uniformly bounded-degree polynomial coefficient by coefficient. -/
def averagePolynomial (P : LocalUnitary N → ℂ[X]) (d : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range d, monomial k (∫ U, (P U).coeff k ∂haar N)

lemma averagePolynomial_coeff (P : LocalUnitary N → ℂ[X]) (d k : ℕ)
    (hk : k < d) : (averagePolynomial P d).coeff k = ∫ U, (P U).coeff k ∂haar N := by
  simp [averagePolynomial, coeff_monomial, hk]

lemma averagePolynomial_eval (P : LocalUnitary N → ℂ[X]) (d : ℕ)
    (hdeg : ∀ U, (P U).natDegree < d)
    (hint : ∀ k, Integrable (fun U => (P U).coeff k) (haar N)) (z : ℂ) :
    (averagePolynomial P d).eval z = ∫ U, (P U).eval z ∂haar N := by
  simp only [averagePolynomial, eval_finset_sum, eval_monomial]
  simp_rw [← integral_mul_const]
  rw [← integral_finset_sum _ (fun k _ => (hint k).mul_const _)]
  apply integral_congr_ae
  filter_upwards [] with U
  exact (eval_eq_sum_range' (hdeg U) z).symm

lemma coeff_mul_two (P Q : ℂ[X]) :
    (P*Q).coeff 2 = P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 +
      P.coeff 2 * Q.coeff 0 := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.antidiagonal_zero]
  ring

lemma coeff_linear_pow_zero (x y : ℂ) (p : ℕ) :
    ((C x + X * C y)^p).coeff 0 = x^p := by rw [coeff_zero_eq_eval_zero]; simp

lemma coeff_linear_pow_one (x y : ℂ) (p : ℕ) :
    ((C x + X * C y)^(p+1)).coeff 1 = (p+1:ℂ)*x^p*y := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, mul_coeff_one, ih]
    simp [coeff_zero_eq_eval_zero]
    ring

lemma coeff_linear_pow_two (x y : ℂ) (p : ℕ) :
    ((C x + X * C y)^(p+2)).coeff 2 =
      ((p+2:ℂ)*(p+1:ℂ)/2)*x^p*y^2 := by
  induction p with
  | zero =>
    rw [pow_two, coeff_mul_two]
    simp
    ring
  | succ p ih =>
    rw [show p+1+2 = (p+2)+1 by omega, pow_succ, coeff_mul_two, ih]
    rw [show p+2 = (p+1)+1 by omega, coeff_linear_pow_one]
    simp only [coeff_add, coeff_C, coeff_X_mul, if_true, if_false, zero_add,
      add_zero, one_ne_zero, Nat.cast_add, Nat.cast_one]
    simp
    ring


lemma continuous_coeff_pow {P : LocalUnitary N → ℂ[X]}
    (hP : ∀ k, Continuous (fun U => (P U).coeff k)) (p k : ℕ) :
    Continuous (fun U => ((P U)^p).coeff k) := by
  induction p generalizing k with
  | zero => simpa using (continuous_const : Continuous (fun _ : LocalUnitary N => (1:ℂ[X]).coeff k))
  | succ p ih =>
    simp only [pow_succ, coeff_mul]
    exact continuous_finset_sum _ (fun x _ => (ih x.1).mul (hP x.2))

def entryPolynomial (i k j : Fin (N+1)) (p : ℕ) (U : LocalUnitary N) : ℂ[X] :=
  (C ((U:Mat N) i j) + X*C ((U:Mat N) k j))^p *
  (C (star ((U:Mat N) i j)) + X*C (star ((U:Mat N) k j)))^p

lemma continuous_entryPolynomial_coeff (i k j : Fin (N+1)) (p r : ℕ) :
    Continuous (fun U : LocalUnitary N => (entryPolynomial i k j p U).coeff r) := by
  have hf (a b : LocalUnitary N → ℂ) (ha : Continuous a) (hb : Continuous b) (q : ℕ) :
      Continuous (fun U => ((C (a U) + X*C (b U))^p).coeff q) := by
    apply continuous_coeff_pow
    intro l
    cases l with
    | zero => simpa [coeff_zero_eq_eval_zero] using ha
    | succ l =>
      cases l with
      | zero => simpa using hb
      | succ l => simpa using (continuous_const : Continuous (fun _ : LocalUnitary N => (0:ℂ)))
  simp only [entryPolynomial, coeff_mul]
  exact continuous_finset_sum _ (fun x _ =>
    (hf _ _ (continuous_entry i j) (continuous_entry k j) x.1).mul
      (hf _ _ (continuous_entry i j).star (continuous_entry k j).star x.2))

lemma entryPolynomial_degree (i k j : Fin (N+1)) (p : ℕ) (U : LocalUnitary N) :
    (entryPolynomial i k j p U).natDegree < 2*p+1 := by
  have hlin (x y : ℂ) : (C x + X*C y).natDegree ≤ 1 := by
    compute_degree
  have hp (x y : ℂ) : ((C x + X*C y)^p).natDegree ≤ p := by
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left p (hlin x y))
  exact (natDegree_mul_le.trans (Nat.add_le_add (hp _ _) (hp _ _))).trans_lt (by omega)

lemma norm_even_complex (z : ℂ) (p : ℕ) :
    ((‖z‖^(2*p):ℝ):ℂ) = z^p * (star z)^p := by
  rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.ofReal_pow,
    Complex.normSq_eq_conj_mul_self, mul_pow, mul_comm]
  rfl

lemma entryPolynomial_eval_real (i k j : Fin (N+1)) (p : ℕ)
    (U : LocalUnitary N) (t : ℝ) :
    (entryPolynomial i k j p U).eval (t:ℂ) =
      ((‖(U:Mat N) i j + (t:ℂ)*(U:Mat N) k j‖^(2*p):ℝ):ℂ) := by
  rw [norm_even_complex]
  simp only [entryPolynomial, eval_mul, eval_pow, eval_add, eval_C, eval_X,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
  congr 1; ring

lemma average_entryPolynomial (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) :
    averagePolynomial (entryPolynomial i k j p) (2*p+1) =
      C (moment i j p : ℂ) * (1+X^2)^p := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (Complex.ofReal : ℝ → ℂ)) :=
    Set.infinite_range_of_injective Complex.ofReal_injective
  apply hinf.mono
  rintro _ ⟨t, rfl⟩
  change _ = _
  rw [averagePolynomial_eval _ _ (entryPolynomial_degree i k j p)
    (fun r => (continuous_entryPolynomial_coeff i k j p r).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp_rw [entryPolynomial_eval_real]
  rw [integral_complex_ofReal, moment_add i k j hik]
  simp
  ring

lemma integral_phase_square_left_zero (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) :
    (∫ U : LocalUnitary N, ((U:Mat N) i j)^p * ((U:Mat N) k j)^2 *
      (star ((U:Mat N) i j))^(p+2) ∂haar N) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := rowPhase k Complex.I (by simp))
  intro U
  simp [hik, mul_pow]

lemma integral_phase_square_right_zero (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) :
    (∫ U : LocalUnitary N, ((U:Mat N) i j)^(p+2) *
      (star ((U:Mat N) i j))^p * (star ((U:Mat N) k j))^2 ∂haar N) = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := rowPhase k Complex.I (by simp))
  intro U
  simp [hik, mul_pow]

lemma coeff_one_add_X_sq_pow_zero (p : ℕ) :
    ((1+X^2:ℂ[X])^p).coeff 0 = 1 := by simp [coeff_zero_eq_eval_zero]

lemma coeff_one_add_X_sq_pow_one (p : ℕ) :
    ((1+X^2:ℂ[X])^p).coeff 1 = 0 := by
  induction p with
  | zero => simp [coeff_one]
  | succ p ih =>
    rw [pow_succ, mul_coeff_one, ih]
    simp [coeff_one, coeff_zero_eq_eval_zero]

lemma coeff_one_add_X_sq_pow_two (p : ℕ) :
    ((1+X^2:ℂ[X])^p).coeff 2 = (p:ℂ) := by
  induction p with
  | zero => simp [coeff_one]
  | succ p ih =>
    rw [pow_succ, coeff_mul_two, ih, coeff_one_add_X_sq_pow_zero,
      coeff_one_add_X_sq_pow_one]
    simp [coeff_one]
    ring

def mixed (i k j : Fin (N+1)) (p : ℕ) : ℝ :=
  ∫ U : LocalUnitary N, ‖(U:Mat N) i j‖^(2*p) * ‖(U:Mat N) k j‖^2 ∂haar N

lemma entryPolynomial_coeff_two (i k j : Fin (N+1)) (p : ℕ) (U : LocalUnitary N) :
    (entryPolynomial i k j (p+2) U).coeff 2 =
      ((p+2:ℂ)*(p+1:ℂ)/2) *
        (((U:Mat N) i j)^p * ((U:Mat N) k j)^2 * (star ((U:Mat N) i j))^(p+2)) +
      ((p+2:ℂ)*(p+1:ℂ)/2) *
        (((U:Mat N) i j)^(p+2) * (star ((U:Mat N) i j))^p * (star ((U:Mat N) k j))^2) +
      (p+2:ℂ)^2 *
        ((‖(U:Mat N) i j‖^(2*(p+1)) * ‖(U:Mat N) k j‖^2 : ℝ):ℂ) := by
  rw [entryPolynomial, coeff_mul_two, coeff_linear_pow_zero,
    coeff_linear_pow_zero, coeff_linear_pow_two, coeff_linear_pow_two]
  rw [show p+2 = (p+1)+1 by omega, coeff_linear_pow_one, coeff_linear_pow_one]
  rw [Complex.ofReal_mul, norm_even_complex]
  have hy := norm_even_complex ((U:Mat N) k j) 1
  norm_num only [Nat.mul_one, pow_one] at hy
  rw [hy]
  push_cast
  ring

lemma integral_entryPolynomial_coeff_two (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) :
    (∫ U : LocalUnitary N, (entryPolynomial i k j (p+2) U).coeff 2 ∂haar N) =
      (p+2:ℂ)^2 * (mixed i k j (p+1) : ℂ) := by
  let c : ℂ := (p+2:ℂ)*(p+1:ℂ)/2
  let f : LocalUnitary N → ℂ := fun U =>
    ((U:Mat N) i j)^p * ((U:Mat N) k j)^2 * (star ((U:Mat N) i j))^(p+2)
  let g : LocalUnitary N → ℂ := fun U =>
    ((U:Mat N) i j)^(p+2) * (star ((U:Mat N) i j))^p * (star ((U:Mat N) k j))^2
  let h : LocalUnitary N → ℝ := fun U =>
    ‖(U:Mat N) i j‖^(2*(p+1)) * ‖(U:Mat N) k j‖^2
  have hf : Continuous f := ((continuous_entry i j).pow p |>.mul
    ((continuous_entry k j).pow 2)).mul ((continuous_entry i j).star.pow (p+2))
  have hg : Continuous g := ((continuous_entry i j).pow (p+2) |>.mul
    ((continuous_entry i j).star.pow p)).mul ((continuous_entry k j).star.pow 2)
  have hh : Continuous (fun U => (h U : ℂ)) := Complex.continuous_ofReal.comp
    (((continuous_entry i j).norm.pow (2*(p+1))).mul ((continuous_entry k j).norm.pow 2))
  have hif : Integrable (fun U => c * f U) (haar N) := (hf.const_mul c).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hig : Integrable (fun U => c * g U) (haar N) := (hg.const_mul c).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hih : Integrable (fun U => (p+2:ℂ)^2 * (h U : ℂ)) (haar N) := (hh.const_mul ((p+2:ℂ)^2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [entryPolynomial_coeff_two]
  have hi1 := integral_add (hif.add hig) hih
  have hi2 := integral_add hif hig
  simp only [Pi.add_apply] at hi1 hi2
  dsimp only [c, f, g, h] at hi1 hi2
  rw [hi1, hi2]
  simp only [integral_const_mul, integral_phase_square_left_zero i k j hik,
    integral_phase_square_right_zero i k j hik, mul_zero, zero_add]
  rw [integral_complex_ofReal]
  rfl

/-- The degree-two coefficient of rotation invariance determines the mixed moment. -/
theorem moment_eq_succ_mul_mixed (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) :
    moment i j (p+2) = (p+2:ℝ) * mixed i k j (p+1) := by
  have he := congrArg (fun P : ℂ[X] => P.coeff 2)
    (average_entryPolynomial i k j hik (p+2))
  dsimp only at he
  rw [averagePolynomial_coeff _ _ _ (by omega), integral_entryPolynomial_coeff_two i k j hik,
    coeff_C_mul, coeff_one_add_X_sq_pow_two] at he
  have hreal : (p+2:ℝ)^2 * mixed i k j (p+1) = moment i j (p+2) * (p+2:ℝ) := by
    exact_mod_cast he
  have hp : (0:ℝ) < p+2 := by positivity
  nlinarith

lemma mixed_self (i j : Fin (N+1)) (p : ℕ) : mixed i i j p = moment i j (p+1) := by
  unfold mixed moment
  apply integral_congr_ae
  filter_upwards [] with U
  rw [← pow_add]
  congr 1

lemma mixed_of_ne (i k j : Fin (N+1)) (hik : i ≠ k) (p : ℕ) :
    mixed i k j p = moment i j (p+1) / (p+1:ℝ) := by
  cases p with
  | zero => simp [mixed, moment_one, integral_entry_norm_sq]
  | succ p =>
    have hm := moment_eq_succ_mul_mixed i k j hik p
    push_cast
    apply (eq_div_iff (by positivity : (p+1+1:ℝ) ≠ 0)).mpr
    convert hm.symm using 1; ring

lemma sum_mixed (i j : Fin (N+1)) (p : ℕ) : ∑ k, mixed i k j p = moment i j p := by
  unfold mixed moment
  have hi := integral_finset_sum Finset.univ (fun k _ => integrable_continuous
    (((continuous_entry i j).norm.pow (2*p)).mul ((continuous_entry k j).norm.pow 2)))
  simp only [Pi.mul_apply] at hi
  rw [← hi]
  simp_rw [← Finset.mul_sum, column_sum_norm_sq, mul_one]

/-- The all-order Haar moment recurrence, with no asymptotic hypothesis. -/
theorem moment_recurrence (i j : Fin (N+1)) (p : ℕ) :
    (N+p+1:ℝ) * moment i j (p+1) = (p+1:ℝ) * moment i j p := by
  have hm (k : Fin (N+1)) : mixed i k j p =
      (if k=i then moment i j (p+1) - moment i j (p+1)/(p+1:ℝ) else 0) +
        moment i j (p+1)/(p+1:ℝ) := by
    by_cases hki : k=i
    · subst k
      simp [mixed_self]
    · simp [hki, mixed_of_ne i k j (Ne.symm hki)]
  have hs := sum_mixed i j p
  simp_rw [hm] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hs
  have hp : (p+1:ℝ) ≠ 0 := by positivity
  field_simp at hs
  nlinarith

/-- Every even absolute Haar entry moment is the exact factorial ratio. -/
theorem integral_entry_norm_even (i j : Fin (N+1)) (p : ℕ) :
    (∫ U : LocalUnitary N, ‖(U:Mat N) i j‖^(2*p) ∂haar N) =
      (p.factorial:ℝ) / ((N+1).ascFactorial p : ℝ) := by
  change moment i j p = _
  induction p with
  | zero => simp [moment_zero]
  | succ p ih =>
    have hm := moment_recurrence i j p
    rw [ih] at hm
    rw [Nat.factorial_succ, Nat.ascFactorial_succ]
    push_cast
    have hd : (0:ℝ) < (N+1).ascFactorial p := by exact_mod_cast Nat.ascFactorial_pos N p
    have hp : (0:ℝ) < N+1+p := by positivity
    apply (eq_div_iff (mul_ne_zero hp.ne' hd.ne')).mpr
    field_simp at hm
    nlinarith

/-- The exact moments obey the Gaussian-size upper bound at every order. -/
theorem integral_entry_norm_even_le (i j : Fin (N+1)) (p : ℕ) :
    (∫ U : LocalUnitary N, ‖(U:Mat N) i j‖^(2*p) ∂haar N) ≤
      (p.factorial:ℝ) / (N+1:ℝ)^p := by
  rw [integral_entry_norm_even]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.pow_succ_le_ascFactorial (N+1) p

/-- The exact formula persists for each independent sampled block coordinate. -/
theorem integral_sample_entry_norm_even (K n : ℕ) (a : Fin n × Fin K)
    (i j : Fin (N+1)) (p : ℕ) :
    (∫ ω : Sample K n N, ‖(ω a : Mat N) i j‖^(2*p) ∂sampleMeasure K n N) =
      (p.factorial:ℝ) / ((N+1).ascFactorial p : ℝ) := by
  exact (integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := a)
    ((continuous_entry i j).norm.pow (2*p)).aestronglyMeasurable).trans
      (integral_entry_norm_even i j p)

end Nonadditivity.HaarColumnMoments


