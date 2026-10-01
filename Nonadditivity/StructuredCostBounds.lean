/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Quantitative
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Div

/-! Exact products of the structured tensor and word support budgets. -/

namespace Nonadditivity.StructuredCostBounds

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 800000

def dyadicCeil (m j : ℕ) : ℕ := ⌈(m : ℝ) / 2 ^ j⌉₊
def tensorSteps (n : ℕ) : ℕ := Nat.clog 2 n
def wordLength (K : ℕ) : ℕ := 2 * Nat.log2 (K - 1) + 1
def wordSteps (K : ℕ) : ℕ := Nat.clog 2 (wordLength K)
def tensorSupportBound (K n j : ℕ) : ℕ := 1 + 2 ^ (j + 1) * K ^ dyadicCeil n j
def wordSupportBound (K n i : ℕ) : ℕ := 2 * n * 3 ^ dyadicCeil (wordLength K) i

theorem dyadicCeil_le (m j : ℕ) :
    (dyadicCeil m j : ℝ) ≤ (m : ℝ) / 2 ^ j + 1 := by
  exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (m : ℝ) / 2 ^ j)).le

theorem geometric_sum_le (m q : ℕ) :
    ∑ j ∈ Finset.range q, (m : ℝ) / 2 ^ (j + 1) ≤ m := by
  have h : ∑ j ∈ Finset.range q, (m : ℝ) / 2 ^ (j + 1) =
      m - (m : ℝ) / 2 ^ q := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring
  rw [h]
  exact sub_le_self _ (by positivity)

theorem sum_dyadicCeil_le (m q : ℕ) :
    ∑ j ∈ Finset.range q, (dyadicCeil m (j + 1) : ℝ) ≤ (m : ℝ) + (q : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range q, ((m : ℝ) / 2 ^ (j + 1) + 1) :=
      Finset.sum_le_sum fun j _ => dyadicCeil_le m (j + 1)
    _ = (∑ j ∈ Finset.range q, (m : ℝ) / 2 ^ (j + 1)) + (q : ℝ) := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    _ ≤ (m : ℝ) + (q : ℝ) := by linarith [geometric_sum_le m q]

theorem clog_le_log (m : ℕ) :
    (Nat.clog 2 m : ℝ) ≤ 1 + Real.log (m : ℝ) / Real.log 2 := by
  rw [← Real.natCeil_logb_natCast]
  have hnonneg : 0 ≤ Real.logb 2 (m : ℝ) := by
    by_cases hm : m = 0
    · simp [hm]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)
  simpa [Real.logb, add_comm] using (Nat.ceil_lt_add_one hnonneg).le

theorem wordLength_le {K : ℕ} (hK : 2 ≤ K) :
    (wordLength K : ℝ) ≤ 3 * (1 + Real.log (K : ℝ)) := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKm : (0 : ℝ) < (K : ℝ) - 1 := by linarith
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ K)]; norm_num
  have hm := Real.log2_le_logb (K - 1)
  rw [Real.logb, hcast] at hm
  have hl := Real.log_le_log hKm (show (K : ℝ) - 1 ≤ K by linarith)
  have h2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K))
  have hd : Real.log (K : ℝ) / Real.log 2 ≤ 3 / 2 * Real.log (K : ℝ) := by
    apply (div_le_iff₀ h2).2
    nlinarith [mul_nonneg hh0 (show 0 ≤ Real.log 2 - 2 / 3 by linarith [Real.log_two_gt_d9])]
  have hm' := hm.trans ((div_le_div_iff_of_pos_right h2).2 hl)
  dsimp [wordLength]
  push_cast
  linarith

theorem log_three_lt : Real.log 3 < (4 : ℝ) / 3 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_six_lt : Real.log 6 < (2 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem step_bounds {K n : ℕ} (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    (tensorSteps n : ℝ) ≤ 3 / 2 * (1 + Real.log K + Real.log n) ∧
    (wordSteps K : ℝ) ≤ 1 + Real.log K + Real.log n ∧
    Real.log (2 * (n : ℝ)) ≤ 1 + Real.log K + Real.log n := by
  obtain ⟨hh, hn64, hu, _⟩ := Quantitative.threshold_consequences hK hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hv : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2lower : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2upper : Real.log 2 ≤ (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  have hlogK : (2 : ℝ) / 3 ≤ Real.log (K : ℝ) := by
    have hk := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ (K : ℝ) by exact_mod_cast hK)
    linarith
  have hq := clog_le_log n
  have hd : Real.log (n : ℝ) / Real.log 2 ≤ 3 / 2 * Real.log n := by
    apply (div_le_iff₀ h2).2
    nlinarith [mul_nonneg hv (sub_nonneg.mpr h2lower)]
  refine ⟨by dsimp [tensorSteps]; linarith, ?_, ?_⟩
  · have hy : 0 < 1 + Real.log (K : ℝ) := by linarith
    have hlpos : (0 : ℝ) < wordLength K := by dsimp [wordLength]; positivity
    have hle := Real.log_le_log hlpos (wordLength_le hK)
    rw [Real.log_mul (by norm_num) hy.ne'] at hle
    have hylog := Real.log_le_sub_one_of_pos (div_pos hy (by norm_num : (0 : ℝ) < 2))
    rw [Real.log_div hy.ne' (by norm_num)] at hylog
    have hlogl : 0 ≤ Real.log (wordLength K : ℝ) :=
      Real.log_nonneg (by dsimp [wordLength]; push_cast; linarith [(Nat.cast_nonneg (Nat.log2 (K - 1)) : (0 : ℝ) ≤ (Nat.log2 (K - 1) : ℝ))])
    have hld : Real.log (wordLength K : ℝ) / Real.log 2 ≤
        3 / 2 * Real.log (wordLength K : ℝ) := by
      apply (div_le_iff₀ h2).2
      nlinarith [mul_nonneg hlogl (sub_nonneg.mpr h2lower)]
    have hs := clog_le_log (wordLength K)
    have hv6 : 6 ≤ Real.log (n : ℝ) := by
      have hbase : 256 * (1 + Real.log (K : ℝ)) ^ 2 ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have hn512 : (512 : ℝ) ≤ n := by nlinarith [sq_nonneg (1 + Real.log (K : ℝ) - 5 / 3)]
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 512) hn512
      have he : Real.log (512 : ℝ) = 9 * Real.log 2 := by
        rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]; norm_num
      rw [he] at hl
      linarith
    dsimp [wordSteps]
    linarith [log_three_lt]
  · rw [Real.log_mul (by norm_num) hn0.ne']
    linarith

theorem dyadicCeil_eq_div (m j : ℕ) :
    dyadicCeil m j = (m + 2 ^ j - 1) / 2 ^ j := by
  change dyadicCeil m j = m ⌈/⌉ (2 ^ j)
  apply eq_of_forall_ge_iff
  intro a
  rw [ceilDiv_le_iff_le_mul (by positivity : 0 < (2 : ℕ) ^ j)]
  dsimp [dyadicCeil]
  rw [Nat.ceil_le, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)]
  norm_cast
  rw [Nat.mul_comm]

theorem tensorSupportBound_pos (K n j : ℕ) : 0 < tensorSupportBound K n j := by
  dsimp [tensorSupportBound]; positivity

theorem wordSupportBound_pos {n : ℕ} (hn : 0 < n) (K i : ℕ) :
    0 < wordSupportBound K n i := by
  dsimp [wordSupportBound]; positivity

theorem log_tensorSupportBound_le {K : ℕ} (hK : 1 ≤ K) (n j : ℕ) :
    Real.log (tensorSupportBound K n j : ℝ) ≤
      (j + 2 : ℕ) * Real.log 2 + (dyadicCeil n j : ℝ) * Real.log K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hpow : (1 : ℝ) ≤ (K : ℝ) ^ dyadicCeil n j :=
    one_le_pow₀ (by exact_mod_cast hK)
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hprod : (1 : ℝ) ≤ 2 ^ (j + 1) * (K : ℝ) ^ dyadicCeil n j :=
    one_le_mul_of_one_le_of_one_le htwo hpow
  have hb : (tensorSupportBound K n j : ℝ) ≤
      2 ^ (j + 2) * (K : ℝ) ^ dyadicCeil n j := by
    dsimp [tensorSupportBound]
    push_cast
    simp only [show j + 2 = (j + 1) + 1 by omega, pow_succ] at hprod ⊢
    nlinarith
  have hl := Real.log_le_log (by exact_mod_cast tensorSupportBound_pos K n j) hb
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
  exact hl

theorem sum_linear_indices (q : ℕ) :
    ∑ j ∈ Finset.range q, ((j : ℝ) + 3) = (q : ℝ) * (q + 5) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem tensor_sum_log_coarse {K : ℕ} (hK : 2 ≤ K) (n q : ℕ) :
    (∑ j ∈ Finset.range q, Real.log (tensorSupportBound K n (j + 1) : ℝ)) ≤
      (n : ℝ) * Real.log K + q * Real.log K +
        (q : ℝ) * (q + 5) / 2 * Real.log 2 := by
  have hh : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K))
  calc
    _ ≤ ∑ j ∈ Finset.range q,
        (((j : ℝ) + 3) * Real.log 2 + (dyadicCeil n (j + 1) : ℝ) * Real.log K) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using
        log_tensorSupportBound_le (by omega : 1 ≤ K) n (j + 1)
    _ = ((q : ℝ) * (q + 5) / 2) * Real.log 2 +
        (∑ j ∈ Finset.range q, (dyadicCeil n (j + 1) : ℝ)) * Real.log K := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sum_linear_indices]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (sum_dyadicCeil_le n q) hh]

theorem tensor_sum_log_bound {K n : ℕ} (hK : 2 ≤ K) :
    (∑ j ∈ Finset.range (tensorSteps n),
      Real.log (tensorSupportBound K n (j + 1) : ℝ)) ≤
    (n : ℝ) * Real.log K + 3 / 4 * (1 + Real.log K + Real.log n) ^ 2 +
      2 * (1 + Real.log K + Real.log n) := by
  have hh : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K))
  have hv : 0 ≤ Real.log (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have h2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2lo : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : Real.log 2 ≤ (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  have hq := clog_le_log n
  change (tensorSteps n : ℝ) ≤ 1 + Real.log (n : ℝ) / Real.log 2 at hq
  have hqd : (tensorSteps n : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log n := by
    have h := (le_div_iff₀ h2).1 (show (tensorSteps n : ℝ) - 1 ≤ Real.log n / Real.log 2 by linarith)
    nlinarith
  have hq0 : (0 : ℝ) ≤ tensorSteps n := by positivity
  have hqlo : (tensorSteps n : ℝ) ≤ 1 + 3 / 2 * Real.log n := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr h2lo)]
  have hqh := mul_le_mul_of_nonneg_right hqlo hh
  have hqv := mul_le_mul_of_nonneg_right hqlo hv
  have hqq := mul_le_mul_of_nonneg_left hqd hq0
  have hq2 : (tensorSteps n : ℝ) ^ 2 * Real.log 2 ≤
      3 / 2 * Real.log (n : ℝ) ^ 2 + 2 * Real.log n + Real.log 2 := by
    nlinarith
  have hcoarse := tensor_sum_log_coarse hK n (tensorSteps n)
  have hhsq := sq_nonneg (Real.log (K : ℝ) - 1)
  nlinarith

theorem word_sum_log_bound {K n : ℕ} (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    (∑ i ∈ Finset.range (wordSteps K),
      Real.log (wordSupportBound K n (i + 1) : ℝ)) ≤
    (1 + Real.log K + Real.log n) ^ 2 + 6 * (1 + Real.log K + Real.log n) := by
  obtain ⟨hh, hn64, hu, _⟩ := Quantitative.threshold_consequences hK hn
  obtain ⟨_, hs, hlog2n⟩ := step_bounds hK hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog2n0 : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hs0 : (0 : ℝ) ≤ wordSteps K := by positivity
  have hu0 : 0 ≤ 1 + Real.log (K : ℝ) + Real.log n := by linarith
  have heq : (∑ i ∈ Finset.range (wordSteps K),
      Real.log (wordSupportBound K n (i + 1) : ℝ)) =
      (wordSteps K : ℝ) * Real.log (2 * (n : ℝ)) +
      (∑ i ∈ Finset.range (wordSteps K), (dyadicCeil (wordLength K) (i + 1) : ℝ)) * Real.log 3 := by
    simp only [wordSupportBound, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Real.log_mul (by positivity : (2 : ℝ) * n ≠ 0) (by positivity : (3 : ℝ) ^ _ ≠ 0),
      Real.log_pow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.sum_mul]
  rw [heq]
  have hsum := mul_le_mul_of_nonneg_right (sum_dyadicCeil_le (wordLength K) (wordSteps K)) hlog3
  have hsmul := mul_le_mul hs hlog2n hlog2n0 hu0
  have hl := wordLength_le hK
  have hv : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hsumfactor : (wordLength K : ℝ) + wordSteps K ≤
      4 * (1 + Real.log K + Real.log n) := by linarith
  have hsumfactor0 : (0 : ℝ) ≤ (wordLength K : ℝ) + wordSteps K := by positivity
  have hb := mul_le_mul hsumfactor (show Real.log 3 ≤ (3 : ℝ) / 2 by linarith [log_three_lt])
    hlog3 (by linarith : 0 ≤ 4 * (1 + Real.log (K : ℝ) + Real.log n))
  nlinarith

/-- Product of all tensor and word support budgets, including each stage's
multiplicative overhead.  Use `a=6` for errors and `a=2` for dimensions. -/
def supportProduct (K n : ℕ) (a : ℝ) : ℝ :=
  (∏ j ∈ Finset.range (tensorSteps n), a * (tensorSupportBound K n (j + 1) : ℝ)) *
  (∏ i ∈ Finset.range (wordSteps K), a * (wordSupportBound K n (i + 1) : ℝ))

theorem supportProduct_pos {K n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a) :
    0 < supportProduct K n a := by
  apply mul_pos
  · exact Finset.prod_pos fun j _ => mul_pos ha (by exact_mod_cast tensorSupportBound_pos K n (j + 1))
  · exact Finset.prod_pos fun i _ => mul_pos ha (by exact_mod_cast wordSupportBound_pos hn K (i + 1))

theorem log_supportProduct {K n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a) :
    Real.log (supportProduct K n a) =
      ((tensorSteps n : ℝ) + wordSteps K) * Real.log a +
      (∑ j ∈ Finset.range (tensorSteps n), Real.log (tensorSupportBound K n (j + 1) : ℝ)) +
      (∑ i ∈ Finset.range (wordSteps K), Real.log (wordSupportBound K n (i + 1) : ℝ)) := by
  have ht : ∀ j, (tensorSupportBound K n (j + 1) : ℝ) ≠ 0 := fun j => by
    exact_mod_cast (tensorSupportBound_pos K n (j + 1)).ne'
  have hw : ∀ i, (wordSupportBound K n (i + 1) : ℝ) ≠ 0 := fun i => by
    exact_mod_cast (wordSupportBound_pos hn K (i + 1)).ne'
  dsimp [supportProduct]
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero ha.ne' (ht j))
    (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero ha.ne' (hw i))]
  rw [Real.log_prod (fun j _ => mul_ne_zero ha.ne' (ht j)),
    Real.log_prod (fun i _ => mul_ne_zero ha.ne' (hw i))]
  simp_rw [Real.log_mul ha.ne' (ht _), Real.log_mul ha.ne' (hw _)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem supportProduct_dimension_log_bound {K n : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    Real.log (supportProduct K n 2) < (n : ℝ) * Real.log K + n / 3 := by
  obtain ⟨_, hn64, hu, hthreshold⟩ := Quantitative.threshold_consequences hK hn
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  obtain ⟨hq, hs, _⟩ := step_bounds hK hn
  have hsteps : (0 : ℝ) ≤ (tensorSteps n : ℝ) + wordSteps K := by positivity
  have hov : ((tensorSteps n : ℝ) + wordSteps K) * Real.log 2 ≤
      5 / 2 * (1 + Real.log K + Real.log n) := by
    have hm := mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9]) hsteps
    nlinarith
  rw [log_supportProduct hn0 (by norm_num)]
  exact Quantitative.reduction_coefficient_log_bound hu hthreshold hov
    (tensor_sum_log_bound hK) (word_sum_log_bound hK hn)

/-- Upper bound for the initial shifted-dilation error factor from the
prescribed witness's lower norm. -/
def initialFactor (K n : ℕ) : ℝ :=
  3 * (1 + Real.exp (((n : ℝ) + 1) * Real.log K / 2) / Real.sqrt 2)

theorem initialFactor_pos (K n : ℕ) : 0 < initialFactor K n := by
  dsimp [initialFactor]; positivity

theorem initialFactor_log_bound {K n : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    Real.log (initialFactor K n) ≤
      (n : ℝ) * Real.log K / 2 + (1 + Real.log K + Real.log n) := by
  obtain ⟨hh, hn64, _, _⟩ := Quantitative.threshold_consequences hK hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hx0 : 0 ≤ ((n : ℝ) + 1) * Real.log K / 2 := by positivity
  have he : 1 ≤ Real.exp (((n : ℝ) + 1) * Real.log K / 2) := Real.one_le_exp_iff.mpr hx0
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hd : Real.exp (((n : ℝ) + 1) * Real.log K / 2) / Real.sqrt 2 ≤
      Real.exp (((n : ℝ) + 1) * Real.log K / 2) := div_le_self (by positivity) hs
  have hi : initialFactor K n ≤ 6 * Real.exp (((n : ℝ) + 1) * Real.log K / 2) := by
    dsimp [initialFactor]; linarith
  have hl := Real.log_le_log (initialFactor_pos K n) hi
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at hl
  have hv : 1 ≤ Real.log (n : ℝ) := by
    apply (Real.le_log_iff_exp_le hn0).2
    linarith [Real.exp_one_lt_three]
  linarith [log_six_lt]

/-- The full relative-error amplification budget, as an actual product. -/
def errorProduct (K n : ℕ) : ℝ := initialFactor K n * supportProduct K n 6

theorem errorProduct_bound {K n : ℕ} (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    errorProduct K n ≤ Real.exp (Quantitative.gamma (Real.log K) * n) := by
  obtain ⟨_, hn64, hu, hthreshold⟩ := Quantitative.threshold_consequences hK hn
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  obtain ⟨hq, hs, _⟩ := step_bounds hK hn
  have hsteps : (0 : ℝ) ≤ (tensorSteps n : ℝ) + wordSteps K := by positivity
  have hov : ((tensorSteps n : ℝ) + wordSteps K) * Real.log 6 ≤
      5 * (1 + Real.log K + Real.log n) := by
    have hm := mul_le_mul_of_nonneg_left log_six_lt.le hsteps
    nlinarith
  have hb := Quantitative.reduction_error_log_bound hu hthreshold
    (initialFactor_log_bound hK hn) hov (tensor_sum_log_bound hK) (word_sum_log_bound hK hn)
  have hepos : 0 < errorProduct K n := mul_pos (initialFactor_pos K n)
    (supportProduct_pos hn0 (by norm_num))
  apply (Real.log_le_iff_le_exp hepos).mp
  dsimp [errorProduct]
  rw [Real.log_mul (initialFactor_pos K n).ne' (supportProduct_pos hn0 (by norm_num)).ne',
    log_supportProduct hn0 (by norm_num)]
  linarith

/-- Largest permitted test net size in the traceless Hermitian sphere. -/
def netCardBound (K n : ℕ) : ℕ := (1 + 2 * n) ^ (K ^ (2 * n) - 1)

/-- The actual coefficient budget including the initial `2 J K^n` and all
subsequent structured support factors. -/
def coefficientBound (K n : ℕ) : ℝ :=
  2 * netCardBound K n * (K : ℝ) ^ n * supportProduct K n 2

theorem netCardBound_pos (K n : ℕ) : 0 < netCardBound K n := by
  dsimp [netCardBound]; positivity

theorem coefficientBound_log {K n : ℕ} (hK : 2 ≤ K) (hn : 0 < n) :
    Real.log (2 * coefficientBound K n) =
      Real.log 4 + (K ^ (2 * n) - 1 : ℝ) * Real.log (1 + 2 * (n : ℝ)) +
      (n : ℝ) * Real.log K + Real.log (supportProduct K n 2) := by
  have hKpos : 0 < K := by omega
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hj : (0 : ℝ) < netCardBound K n := by exact_mod_cast netCardBound_pos K n
  have he : 2 * coefficientBound K n =
      4 * (netCardBound K n : ℝ) * (K : ℝ) ^ n * supportProduct K n 2 := by
    dsimp [coefficientBound]; ring
  rw [he, Real.log_mul (by positivity) (supportProduct_pos hn (by norm_num)).ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hj.ne', Real.log_pow]
  have hjlog : Real.log (netCardBound K n : ℝ) =
      ((K : ℝ) ^ (2 * n) - 1) * Real.log (1 + 2 * (n : ℝ)) := by
    dsimp [netCardBound]
    rw [Nat.cast_pow, Real.log_pow]
    congr 1
    · rw [Nat.cast_sub (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))), Nat.cast_pow, Nat.cast_one]
    · push_cast; rfl
  rw [hjlog]

theorem coefficientBound_log_bound {K n : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    Real.log (2 * coefficientBound K n) ≤
      2 * (K : ℝ) ^ (2 * n) * Real.log (1 + 2 * (n : ℝ)) := by
  obtain ⟨_, hn64, _, _⟩ := Quantitative.threshold_consequences hK hn
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr0 : (0 : ℝ) < K := by linarith
  have hh : (2 : ℝ) / 3 ≤ Real.log (K : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hKr
    linarith [Real.log_two_gt_d9]
  have hexp : Real.exp (2 * (n : ℝ) * Real.log K) = (K : ℝ) ^ (2 * n) := by
    rw [show 2 * (n : ℝ) * Real.log K = (2 * n : ℕ) * Real.log K by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hKr0]
  rw [coefficientBound_log hK hn0]
  have h := Quantitative.final_coefficient_size hh (show (2 : ℝ) ≤ n by linarith)
    (J := ((K : ℝ) ^ (2 * n) - 1) * Real.log (1 + 2 * (n : ℝ)))
    (by rw [hexp]) (supportProduct_dimension_log_bound hK hn).le (le_refl _)
  simpa only [hexp] using h

end
end Nonadditivity.StructuredCostBounds
