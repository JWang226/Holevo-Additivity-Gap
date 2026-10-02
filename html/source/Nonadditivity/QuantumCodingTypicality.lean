/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Entropy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite independent sampling and entropy typicality

All expectations below are literal finite sums against the product law.
Zeros in the single-letter distribution are allowed; their words have zero
weight, so no full-support assumption is needed.
-/
noncomputable section
namespace Nonadditivity.QuantumCodingTypicality
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def wordProbability (p : ι → ℝ) (n : ℕ) (x : Fin n → ι) : ℝ := ∏ i, p (x i)

def wordSum (f : ι → ℝ) (n : ℕ) (x : Fin n → ι) : ℝ := ∑ i, f (x i)

def expectation (p : ι → ℝ) (n : ℕ) (f : (Fin n → ι) → ℝ) : ℝ :=
  ∑ x, wordProbability p n x * f x

def entropy (p : ι → ℝ) : ℝ := Entropy.shannon p

def information (p : ι → ℝ) (i : ι) : ℝ := -Real.log (p i)

def surprisal (p : ι → ℝ) (n : ℕ) : (Fin n → ι) → ℝ := wordSum (information p) n

def variance (p : ι → ℝ) : ℝ := ∑ i, p i * (information p i - entropy p)^2

def wordConsEquiv (n : ℕ) : ι × (Fin n → ι) ≃ (Fin (n+1) → ι) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv x := by cases x; rfl
  right_inv x := by funext i; exact Fin.cases rfl (fun j => rfl) i

theorem sum_words_succ (n : ℕ) (f : (Fin (n+1) → ι) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x, f (Fin.cons a x) := by
  rw [←(wordConsEquiv (ι := ι) n).sum_comp f]
  simp only [Fintype.sum_prod_type, wordConsEquiv, Equiv.coe_fn_mk]

omit [Fintype ι] in
@[simp] theorem wordProbability_cons (p : ι → ℝ) (n : ℕ) (a : ι) (x : Fin n → ι) :
    wordProbability p (n+1) (Fin.cons a x) = p a * wordProbability p n x := by
  simp [wordProbability, Fin.prod_univ_succ]

omit [Fintype ι] in
@[simp] theorem wordSum_cons (f : ι → ℝ) (n : ℕ) (a : ι) (x : Fin n → ι) :
    wordSum f (n+1) (Fin.cons a x) = f a + wordSum f n x := by
  simp [wordSum, Fin.sum_univ_succ]

omit [Fintype ι] in
theorem wordProbability_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (n : ℕ) (x : Fin n → ι) : 0 ≤ wordProbability p n x :=
  Finset.prod_nonneg (fun i _ => hp (x i))

theorem sum_wordProbability (p : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    ∑ x, wordProbability p n x = 1 := by
  induction n with
  | zero => simp [wordProbability]
  | succ n ih =>
    rw [sum_words_succ]
    simp_rw [wordProbability_cons, ←Finset.mul_sum, ih, mul_one]
    exact hp

theorem expectation_const (p : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) (c : ℝ) :
    expectation p n (fun _ => c) = c := by
  simp only [expectation, ←Finset.sum_mul, sum_wordProbability p hp, one_mul]

theorem expectation_add (p : ι → ℝ) (n : ℕ) (f g : (Fin n → ι) → ℝ) :
    expectation p n (fun x => f x + g x) = expectation p n f + expectation p n g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mul_const (p : ι → ℝ) (n : ℕ) (f : (Fin n → ι) → ℝ) (c : ℝ) :
    expectation p n (fun x => f x * c) = expectation p n f * c := by
  simp only [expectation, ←mul_assoc, Finset.sum_mul]

theorem expectation_succ (p : ι → ℝ) (n : ℕ) (f : (Fin (n+1) → ι) → ℝ) :
    expectation p (n+1) f = ∑ a, p a * expectation p n (fun x => f (Fin.cons a x)) := by
  unfold expectation
  rw [sum_words_succ]
  simp only [wordProbability_cons, mul_assoc, Finset.mul_sum]

theorem expectation_wordSum (p f : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    expectation p n (wordSum f n) = n * ∑ i, p i * f i := by
  induction n with
  | zero => simp [expectation, wordSum]
  | succ n ih =>
    rw [expectation_succ]
    simp only [wordSum_cons, expectation_add, expectation_const p hp, ih,
      mul_add, Finset.sum_add_distrib, ←Finset.sum_mul, hp, one_mul, Nat.cast_add,
      Nat.cast_one]
    ring

theorem expectation_wordSum_sq_of_centered (p f : ι → ℝ) (hp : ∑ i, p i = 1)
    (hf : ∑ i, p i * f i = 0) (n : ℕ) :
    expectation p n (fun x => (wordSum f n x)^2) = n * ∑ i, p i * (f i)^2 := by
  induction n with
  | zero => simp [expectation, wordSum]
  | succ n ih =>
    rw [expectation_succ]
    have he (a : ι) : expectation p n (fun x => (wordSum f (n+1) (Fin.cons a x))^2) =
        (f a)^2 + n * ∑ i, p i * (f i)^2 := by
      simp only [wordSum_cons]
      have hpoly : (fun x : Fin n → ι => (f a + wordSum f n x)^2) =
          (fun x => (f a)^2 + wordSum f n x * (2*f a) + (wordSum f n x)^2) := by
        funext x
        ring
      rw [hpoly, expectation_add, expectation_add, expectation_const p hp,
        expectation_mul_const, expectation_wordSum p f hp, hf, mul_zero, zero_mul,
        add_zero, ih]
    simp_rw [he, mul_add, Finset.sum_add_distrib, ←Finset.sum_mul, hp, one_mul]
    push_cast
    ring

theorem information_mean (p : ι → ℝ) : ∑ i, p i * information p i = entropy p := by
  simp only [information, entropy, Entropy.shannon, mul_neg, Finset.sum_neg_distrib]

theorem information_centered (p : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (information p i - entropy p) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, information_mean, ←Finset.sum_mul,
    hp, one_mul, sub_self]

theorem centered_wordSum (p : ι → ℝ) (n : ℕ) (x : Fin n → ι) :
    wordSum (fun i => information p i - entropy p) n x = surprisal p n x - n*entropy p := by
  simp [wordSum, surprisal, Finset.sum_sub_distrib]

theorem surprisal_mean (p : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    expectation p n (surprisal p n) = n * entropy p := by
  exact (expectation_wordSum p (information p) hp n).trans (by rw [information_mean])

theorem surprisal_variance (p : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    expectation p n (fun x => (surprisal p n x - n*entropy p)^2) = n * variance p := by
  simpa only [centered_wordSum, variance] using
    expectation_wordSum_sq_of_centered p (fun i => information p i - entropy p)
      hp (information_centered p hp) n

theorem variance_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ variance p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

/-- The finite Chebyshev inequality, proved directly from its weighted sum. -/
theorem finite_chebyshev (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (μ a : ℝ) (ha : 0 < a) :
    1 - (∑ i, w i * (f i-μ)^2)/a^2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => |f i-μ| < a), w i := by
  classical
  let bad := Finset.univ.filter (fun i => ¬ |f i-μ| < a)
  have hb : (∑ i ∈ bad, w i)*a^2 ≤ ∑ i, w i*(f i-μ)^2 := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i ∈ bad, w i*(f i-μ)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : a ≤ |f i-μ| := le_of_not_gt (Finset.mem_filter.mp hi).2
        apply mul_le_mul_of_nonneg_left _ (hw i)
        exact sq_le_sq.mpr (by simpa only [abs_of_pos ha] using hi')
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
  have hb' := (le_div_iff₀ (sq_pos_of_pos ha)).mpr hb
  have ht := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => |f i-μ| < a) w
  rw [hs] at ht
  change (∑ i ∈ Finset.univ.filter (fun i => |f i-μ| < a), w i) +
    (∑ i ∈ bad, w i) = 1 at ht
  linarith

def typicalSet (p : ι → ℝ) (n : ℕ) (δ : ℝ) : Finset (Fin n → ι) := by
  classical
  exact Finset.univ.filter (fun x => |surprisal p n x - n*entropy p| < n*δ)

/-- Product sampling places all but `V/(n δ²)` of its mass in the entropy
window, including distributions that vanish on part of the alphabet. -/
theorem typical_mass_ge (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    1 - variance p / (n*δ^2) ≤ ∑ x ∈ typicalSet p n δ, wordProbability p n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h := finite_chebyshev (wordProbability p n) (surprisal p n)
    (wordProbability_nonneg p hp n) (sum_wordProbability p hs n)
    (n*entropy p) (n*δ) (mul_pos hn' hδ)
  change 1 - expectation p n (fun x => (surprisal p n x-n*entropy p)^2)/(n*δ)^2 ≤ _ at h
  rw [surprisal_variance p hs] at h
  have he : (n:ℝ)*variance p/((n:ℝ)*δ)^2 = variance p/((n:ℝ)*δ^2) := by
    field_simp
  simpa only [he, typicalSet] using h

omit [Fintype ι] in
/-- On words of positive probability, the sum of letter informations is the
negative logarithm of the actual product probability. -/
theorem log_wordProbability (p : ι → ℝ) (n : ℕ) (x : Fin n → ι)
    (hx : wordProbability p n x ≠ 0) :
    Real.log (wordProbability p n x) = -surprisal p n x := by
  have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin n)), p (x i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hx
  rw [wordProbability, Real.log_prod hcoord]
  simp only [surprisal, wordSum, information, Finset.sum_neg_distrib, neg_neg]

theorem probability_bounds_of_typical (p : ι → ℝ) (n : ℕ) (δ : ℝ) (x : Fin n → ι)
    (hx : x ∈ typicalSet p n δ) (hpos : 0 < wordProbability p n x) :
    Real.exp (-(n*entropy p)-n*δ) ≤ wordProbability p n x ∧
      wordProbability p n x ≤ Real.exp (-(n*entropy p)+n*δ) := by
  have hdev := abs_lt.mp (Finset.mem_filter.mp hx).2
  have hlog := log_wordProbability p n x hpos.ne'
  constructor
  · rw [←Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    linarith
  · rw [←Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    linarith

/-- The actual eigenvalue window has the same guaranteed mass as the
information window. Zero-probability words contribute exactly zero. -/
theorem spectral_band_mass_ge (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    1 - variance p/(n*δ^2) ≤
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → ι =>
        Real.exp (-(n*entropy p)-n*δ) ≤ wordProbability p n x ∧
        wordProbability p n x ≤ Real.exp (-(n*entropy p)+n*δ)), wordProbability p n x := by
  classical
  apply (typical_mass_ge p hp hs n hn δ hδ).trans
  rw [typicalSet]
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases ht : |surprisal p n x - n*entropy p| < n*δ
  · by_cases hz : wordProbability p n x = 0
    · simp [hz]
    · have hpos := lt_of_le_of_ne (wordProbability_nonneg p hp n x) (Ne.symm hz)
      have hb := probability_bounds_of_typical p n δ x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩) hpos
      simp [ht,hb]
  · simp only [if_neg ht]
    split_ifs
    · exact wordProbability_nonneg p hp n x
    · rfl

def letterMean (p f : ι → ℝ) : ℝ := ∑ i, p i * f i

def letterVariance (p f : ι → ℝ) : ℝ := ∑ i, p i * (f i-letterMean p f)^2

/-- Independent finite sampling has variance exactly `n` times the one-letter
variance for every real observable, including conditional information. -/
theorem wordSum_variance (p f : ι → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    expectation p n (fun x => (wordSum f n x-n*letterMean p f)^2) =
      n*letterVariance p f := by
  have hc : ∑ i, p i*(f i-letterMean p f) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ←Finset.sum_mul, hp, one_mul]
    exact sub_self _
  have he (x : Fin n → ι) :
      wordSum (fun i => f i-letterMean p f) n x = wordSum f n x-n*letterMean p f := by
    simp [wordSum, Finset.sum_sub_distrib]
  simpa only [he, letterVariance] using
    expectation_wordSum_sq_of_centered p (fun i => f i-letterMean p f) hp hc n

/-- Typicality for an arbitrary observable; this is also the conditional
entropy typicality estimate when letters are joint input/eigenvalue labels. -/
theorem wordSum_concentration (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    1-letterVariance p f/(n*δ^2) ≤
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → ι =>
        |wordSum f n x-n*letterMean p f| < n*δ), wordProbability p n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h := finite_chebyshev (wordProbability p n) (wordSum f n)
    (wordProbability_nonneg p hp n) (sum_wordProbability p hs n)
    (n*letterMean p f) (n*δ) (mul_pos hn' hδ)
  change 1-expectation p n (fun x => (wordSum f n x-n*letterMean p f)^2)/(n*δ)^2 ≤ _ at h
  rw [wordSum_variance p f hs] at h
  have he : (n:ℝ)*letterVariance p f/((n:ℝ)*δ)^2 = letterVariance p f/((n:ℝ)*δ^2) := by
    field_simp
  simpa only [he] using h

end Nonadditivity.QuantumCodingTypicality
