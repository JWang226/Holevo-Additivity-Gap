/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Asymptotic consequences of the numerical channel bounds

The sequence `blockLength K = ⌈K / √(ln K)⌉₊` is the actual sequence in
Corollary 4 (vanishing Holevo information and diverging capacity).
The scalar limits below are unconditional theorems of real analysis.
The channel-specific conclusion takes the proved numerical bounds as explicit
hypotheses; it does not assert or axiomatize the random-channel construction.
-/

namespace Nonadditivity.Asymptotics

open Filter Topology

noncomputable section

/-- The exact integer block length in the separation corollary. -/
def blockLength (K : ℕ) : ℕ := ⌈(K : ℝ) / Real.sqrt (Real.log K)⌉₊

/-- Upper bound for the single-use Holevo information, in bits. -/
def separationUpper (K : ℕ) : ℝ :=
  9 * (blockLength K : ℝ) / ((K : ℝ) * Real.log 2) + 1 / (K : ℝ)

/-- Lower bound for half of the two-use Holevo information, in bits. -/
def separationLower (K : ℕ) : ℝ :=
  (blockLength K : ℝ) * Real.log K / (2 * (K : ℝ) * Real.log 2)

lemma log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

lemma log_nat_pos {K : ℕ} (hK : 2 ≤ K) : 0 < Real.log (K : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < K by omega)

lemma blockLength_pos {K : ℕ} (hK : 2 ≤ K) : 0 < blockLength K := by
  unfold blockLength
  apply Nat.ceil_pos.2
  apply div_pos
  · exact_mod_cast (show 0 < K by omega)
  · exact Real.sqrt_pos.2 (log_nat_pos hK)

/-- Rounding preserves enough growth to send the integer block length to
infinity; this simple bound avoids assuming any logarithmic rate estimate. -/
lemma sqrt_le_blockLength {K : ℕ} (hK : 2 ≤ K) :
    Real.sqrt K ≤ (blockLength K : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hspos : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 (log_nat_pos hK)
  have hc := (div_le_iff₀ hspos).1 (Nat.le_ceil ((K : ℝ) / Real.sqrt (Real.log K)))
  have hs : Real.sqrt (Real.log K) ≤ Real.sqrt K :=
    Real.sqrt_le_sqrt (Real.log_le_self hKpos.le)
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (blockLength K) :
    (0 : ℝ) ≤ (blockLength K : ℝ))
  have hsq := Real.mul_self_sqrt hKpos.le
  have hsK := Real.sqrt_pos.2 hKpos
  apply (mul_le_mul_iff_left₀ hsK).1
  calc
    Real.sqrt K * Real.sqrt K = (K : ℝ) := hsq
    _ ≤ (blockLength K : ℝ) * Real.sqrt (Real.log K) := hc
    _ ≤ (blockLength K : ℝ) * Real.sqrt K := hm

lemma blockLength_tendsto_atTop : Tendsto blockLength atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).1
  apply tendsto_atTop_mono' atTop _
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 2] with K hK
  exact sqrt_le_blockLength hK

lemma blockLength_div_upper {K : ℕ} (hK : 2 ≤ K) :
    (blockLength K : ℝ) / K ≤
      1 / Real.sqrt (Real.log K) + 1 / (K : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hspos : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 (log_nat_pos hK)
  have hc : (blockLength K : ℝ) ≤
      (K : ℝ) / Real.sqrt (Real.log K) + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg K) (Real.sqrt_nonneg _))).le
  apply (div_le_iff₀ hKpos).2
  convert hc using 1
  field_simp

lemma blockLength_div_lower {K : ℕ} (hK : 2 ≤ K) :
    1 / Real.sqrt (Real.log K) ≤ (blockLength K : ℝ) / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hc := Nat.le_ceil ((K : ℝ) / Real.sqrt (Real.log K))
  apply (le_div_iff₀ hKpos).2
  convert hc using 1
  ring

lemma log_sqrt_tendsto_atTop :
    Tendsto (fun K : ℕ => Real.sqrt (Real.log K)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma blockLength_div_tendsto_zero :
    Tendsto (fun K : ℕ => (blockLength K : ℝ) / K) atTop (𝓝 0) := by
  have hs : Tendsto (fun K : ℕ => 1 / Real.sqrt (Real.log K)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_sqrt_tendsto_atTop
  have hn : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun K => by positivity)
  · filter_upwards [eventually_ge_atTop 2] with K hK
    exact blockLength_div_upper hK
  · simpa using hs.add hn

/-- The explicit single-use upper bound tends to zero; no limit is assumed. -/
theorem separationUpper_tendsto_zero :
    Tendsto separationUpper atTop (𝓝 0) := by
  have h := blockLength_div_tendsto_zero.const_mul (9 / Real.log 2)
  have hn : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun K : ℕ =>
      (9 / Real.log 2) * ((blockLength K : ℝ) / K) + 1 / (K : ℝ)) atTop (𝓝 0) := by
    simpa using h.add hn
  convert hsum using 1
  ext K
  simp only [separationUpper, div_eq_mul_inv, mul_inv_rev]
  ring

lemma separationLower_ge_sqrt {K : ℕ} (hK : 2 ≤ K) :
    Real.sqrt (Real.log K) / (2 * Real.log 2) ≤ separationLower K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hl := log_nat_pos hK
  have hspos : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 hl
  have hc := Nat.le_ceil ((K : ℝ) / Real.sqrt (Real.log K))
  have hb : (K : ℝ) ≤ (blockLength K : ℝ) * Real.sqrt (Real.log K) :=
    (div_le_iff₀ hspos).1 hc
  have hb' := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (Real.log K))
  have hs : Real.sqrt (Real.log K) * Real.sqrt (Real.log K) = Real.log K :=
    Real.mul_self_sqrt hl.le
  have hn : Real.sqrt (Real.log K) * K ≤ (blockLength K : ℝ) * Real.log K := by
    nlinarith [hb', hs]
  unfold separationLower
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.log (2 : ℝ))
    (by positivity : 0 < 2 * (K : ℝ) * Real.log (2 : ℝ))).2
  nlinarith [mul_le_mul_of_nonneg_right hn log_two_pos.le]

/-- The exact rounded lower bound diverges to infinity. -/
theorem separationLower_tendsto_atTop : Tendsto separationLower atTop atTop := by
  have h : Tendsto (fun K : ℕ => Real.sqrt (Real.log K) / (2 * Real.log 2))
      atTop atTop := log_sqrt_tendsto_atTop.atTop_div_const (by positivity)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop 2] with K hK
  exact separationLower_ge_sqrt hK

/-- The finite-size correction `4 log₂((n+1)/(n-1))` in the gap bound. -/
def finiteSizeCorrection (n : ℕ) : ℝ :=
  4 * Real.log (((n : ℝ) + 1) / ((n : ℝ) - 1)) / Real.log 2

/-- The explicit logarithmic correction tends to zero. -/
theorem finiteSizeCorrection_tendsto_zero :
    Tendsto finiteSizeCorrection atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 2 / ((n : ℝ) - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) - 1))
      atTop (𝓝 1) := by
    have haux : Tendsto (fun n : ℕ => 1 + 2 / ((n : ℝ) - 1)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hi
    apply haux.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  simpa only [finiteSizeCorrection, Real.log_one, mul_zero, zero_div] using
    (hr.log (by norm_num)).const_mul 4 |>.div_const (Real.log 2)

lemma finiteSizeCorrection_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ finiteSizeCorrection n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 1 := by linarith
  have hr : 1 ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
    apply (le_div_iff₀ hd).2
    linarith
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hr)) log_two_pos.le

/-- The explicit-construction finite-size correction vanishes along the
same growing integer block sequence used for the qualitative separation. -/
theorem finiteSizeCorrection_blockLength_tendsto_zero :
    Tendsto (fun K : ℕ => finiteSizeCorrection (blockLength K)) atTop (𝓝 0) :=
  finiteSizeCorrection_tendsto_zero.comp blockLength_tendsto_atTop

/-- The normalized finite-size correction also tends to zero. -/
theorem finiteSizeCorrection_div_tendsto_zero :
    Tendsto (fun n : ℕ => finiteSizeCorrection n / n) atTop (𝓝 0) :=
  finiteSizeCorrection_tendsto_zero.div_atTop tendsto_natCast_atTop_atTop

/-- A positive `δ` yields an eventual linear lower bound from the manuscript's
explicit finite-size estimate. This is the lower half of its `Θ(n)` claim. -/
theorem eventually_linear_gap (gap : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᶠ n : ℕ in atTop, (n : ℝ) * δ - finiteSizeCorrection n ≤ gap n) :
    ∀ᶠ n : ℕ in atTop, (δ / 2) * n ≤ gap n := by
  have he : ∀ᶠ n : ℕ in atTop, finiteSizeCorrection n < δ / 2 :=
    finiteSizeCorrection_tendsto_zero.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [hgap, he, eventually_ge_atTop 1] with n hbound hc hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- In particular the additive gap diverges; this is a proved consequence of
its numerical bound, independent of any channel representation. -/
theorem gap_tendsto_atTop (gap : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᶠ n : ℕ in atTop, (n : ℝ) * δ - finiteSizeCorrection n ≤ gap n) :
    Tendsto gap atTop atTop := by
  have hlinear : Tendsto (fun n : ℕ => (δ / 2) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hδ)
  exact tendsto_atTop_mono' atTop (eventually_linear_gap gap hδ hgap) hlinear

/-- The normalized gap is eventually at least `δ - ε` for every positive ε.
This is the quantitative lower-limit statement before conversion to a liminf. -/
theorem eventually_normalized_gap_lower (gap : ℕ → ℝ) {δ ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ᶠ n : ℕ in atTop, (n : ℝ) * δ - finiteSizeCorrection n ≤ gap n) :
    ∀ᶠ n : ℕ in atTop, δ - ε ≤ gap n / n := by
  have he : ∀ᶠ n : ℕ in atTop, finiteSizeCorrection n / n < ε :=
    finiteSizeCorrection_div_tendsto_zero.eventually (gt_mem_nhds hε)
  filter_upwards [hgap, he, eventually_ge_atTop 1] with n hbound hc hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc' : finiteSizeCorrection n < ε * n := (div_lt_iff₀ hnR).1 hc
  apply (le_div_iff₀ hnR).2
  nlinarith

/-- The liminf form of the linear gap estimate. The output-dimension upper
bound makes the real-valued liminf well defined in its boundedness conditions. -/
theorem normalized_gap_liminf (gap : ℕ → ℝ) {δ U : ℝ}
    (hgap : ∀ᶠ n : ℕ in atTop, (n : ℝ) * δ - finiteSizeCorrection n ≤ gap n)
    (hupper : ∀ᶠ n : ℕ in atTop, gap n ≤ (n : ℝ) * U) :
    δ ≤ liminf (fun n : ℕ => gap n / n) atTop := by
  have hu : ∀ᶠ n : ℕ in atTop, gap n / n ≤ U := by
    filter_upwards [hupper, eventually_ge_atTop 1] with n hbound hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hl : ∀ᶠ n : ℕ in atTop, δ - 1 ≤ gap n / n :=
    eventually_normalized_gap_lower gap (by norm_num) hgap
  apply (le_liminf_iff'
    (isBoundedUnder_of_eventually_le hu).isCoboundedUnder_ge
    (isBoundedUnder_of_eventually_ge hl)).2
  intro y hy
  have he := eventually_normalized_gap_lower gap (sub_pos.2 hy) hgap
  simpa only [sub_sub_cancel] using he

/-- The guaranteed fraction of the output size: if the output size is `n L`
qubits with `L ≥ 1`, its normalized liminf is at least `δ/L`. -/
theorem output_normalized_gap_liminf (gap : ℕ → ℝ) {δ U L : ℝ} (hL : 1 ≤ L)
    (hgap : ∀ᶠ n : ℕ in atTop, (n : ℝ) * δ - finiteSizeCorrection n ≤ gap n)
    (hupper : ∀ᶠ n : ℕ in atTop, gap n ≤ (n : ℝ) * U) :
    δ / L ≤ liminf (fun n : ℕ => gap n / ((n : ℝ) * L)) atTop := by
  have hLpos : 0 < L := by linarith
  have hs : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (δ / L) - finiteSizeCorrection n ≤ gap n / L := by
    filter_upwards [hgap, eventually_ge_atTop 2] with n hb hn
    have hc := finiteSizeCorrection_nonneg hn
    apply (le_div_iff₀ hLpos).2
    calc
      ((n : ℝ) * (δ / L) - finiteSizeCorrection n) * L =
          (n : ℝ) * δ - finiteSizeCorrection n * L := by
        field_simp
      _ ≤ (n : ℝ) * δ - finiteSizeCorrection n := by nlinarith
      _ ≤ gap n := hb
  have hu : ∀ᶠ n : ℕ in atTop, gap n / L ≤ (n : ℝ) * (U / L) := by
    filter_upwards [hupper] with n hn
    convert div_le_div_of_nonneg_right hn hLpos.le using 1
    ring
  have h := normalized_gap_liminf (fun n => gap n / L) hs hu
  convert h using 1
  congr 1
  ext n
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The lower-limit ratio assertion in a form valid even when the ratios
are unbounded. The scalar finite-size denominator converges without assuming
that convergence as a premise. -/
theorem eventually_ratio_lower (ratio : ℕ → ℝ) {a b R : ℝ} (ha : 0 < a)
    (hR : R < b / (2 * a))
    (hbound : ∀ᶠ n : ℕ in atTop,
      b / (2 * a + finiteSizeCorrection n / n) ≤ ratio n) :
    ∀ᶠ n : ℕ in atTop, R ≤ ratio n := by
  have hd : Tendsto (fun n : ℕ => 2 * a + finiteSizeCorrection n / n)
      atTop (𝓝 (2 * a)) := by
    simpa using tendsto_const_nhds.add finiteSizeCorrection_div_tendsto_zero
  have hm : Tendsto (fun n : ℕ => b / (2 * a + finiteSizeCorrection n / n))
      atTop (𝓝 (b / (2 * a))) :=
    tendsto_const_nhds.div hd (by positivity)
  have he : ∀ᶠ n : ℕ in atTop, R < b / (2 * a + finiteSizeCorrection n / n) :=
    hm.eventually (lt_mem_nhds hR)
  filter_upwards [hbound, he] with n hb he
  exact he.le.trans hb

/-- Division in the Holevo ratio is justified by the explicit positive
single-use information premise. The constants and finite-size correction
are exactly those of the manuscript after setting `b = log₂ K / K`. -/
lemma ratio_lower_of_holevo_bounds {n : ℕ} (hn : 2 ≤ n)
    {a b chi₁ chi₂ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hchi : 0 < chi₁)
    (hupper : chi₁ ≤ (n : ℝ) * a + finiteSizeCorrection n / 2)
    (hlower : (n : ℝ) * b ≤ chi₂) :
    b / (2 * a + finiteSizeCorrection n / n) ≤ chi₂ / (2 * chi₁) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := finiteSizeCorrection_nonneg hn
  have hd : 0 < 2 * a + finiteSizeCorrection n / n := by positivity
  have hh : 2 * chi₁ ≤ (n : ℝ) * (2 * a + finiteSizeCorrection n / n) := by
    have hcancel : (finiteSizeCorrection n / (n : ℝ)) * n = finiteSizeCorrection n :=
      div_mul_cancel₀ _ hnR.ne'
    nlinarith
  apply (div_le_div_iff₀ hd (by positivity : 0 < 2 * chi₁)).2
  calc
    b * (2 * chi₁) ≤ b * ((n : ℝ) * (2 * a + finiteSizeCorrection n / n)) :=
      mul_le_mul_of_nonneg_left hh hb
    _ = ((n : ℝ) * b) * (2 * a + finiteSizeCorrection n / n) := by ring
    _ ≤ chi₂ * (2 * a + finiteSizeCorrection n / n) :=
      mul_le_mul_of_nonneg_right hlower hd.le

/-- Every strict lower threshold below `b/(2a)` is eventually attained by
`χ₂/(2χ₁)`, proved directly from the one-use and two-use bounds. -/
theorem eventually_ratio_of_holevo_bounds (chi₁ chi₂ : ℕ → ℝ) {a b R : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hR : R < b / (2 * a))
    (hchi : ∀ᶠ n : ℕ in atTop, 0 < chi₁ n)
    (hupper : ∀ᶠ n : ℕ in atTop,
      chi₁ n ≤ (n : ℝ) * a + finiteSizeCorrection n / 2)
    (hlower : ∀ᶠ n : ℕ in atTop, (n : ℝ) * b ≤ chi₂ n) :
    ∀ᶠ n : ℕ in atTop, R ≤ chi₂ n / (2 * chi₁ n) := by
  apply eventually_ratio_lower (fun n => chi₂ n / (2 * chi₁ n)) ha hR
  filter_upwards [hchi, hupper, hlower, eventually_ge_atTop 2] with n hc hu hl hn
  exact ratio_lower_of_holevo_bounds hn ha hb hc hu hl

/-- Any requested finite gap and ratio can be achieved simultaneously once
one fixes parameters with a positive slope and a sufficiently large ratio
limit. Channel existence remains an explicit hypothesis in the calling layer. -/
theorem exists_large_gap_and_ratio (gap ratio : ℕ → ℝ) {δ a b A R : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hR : R < b / (2 * a)) (n₀ : ℕ)
    (hgap : ∀ᶠ n : ℕ in atTop, (n : ℝ) * δ - finiteSizeCorrection n ≤ gap n)
    (hratio : ∀ᶠ n : ℕ in atTop,
      b / (2 * a + finiteSizeCorrection n / n) ≤ ratio n) :
    ∃ n, n₀ ≤ n ∧ A ≤ gap n ∧ R ≤ ratio n := by
  have hg : ∀ᶠ n : ℕ in atTop, A ≤ gap n :=
    (gap_tendsto_atTop gap hδ hgap).eventually (eventually_ge_atTop A)
  have hr := eventually_ratio_lower ratio ha hR hratio
  exact (by
    filter_upwards [eventually_ge_atTop n₀, hg, hr] with n hn hg hr
    exact ⟨hn, hg, hr⟩ : ∀ᶠ n : ℕ in atTop, n₀ ≤ n ∧ A ≤ gap n ∧ R ≤ ratio n).exists

/-- Corollary 4, with all channel-specific ingredients displayed as hypotheses.
`twoUseHalf` denotes half of the two-use Holevo information. -/
theorem vanishing_diverging_of_bounds
    (chi twoUseHalf capacity : ℕ → ℝ)
    (hchi_nonneg : ∀ K, 0 ≤ chi K)
    (hchi : ∀ K, 2 ≤ K → chi K ≤ separationUpper K)
    (htwo : ∀ K, 2 ≤ K → separationLower K ≤ twoUseHalf K)
    (hcapacity : ∀ K, twoUseHalf K ≤ capacity K) :
    Tendsto chi atTop (𝓝 0) ∧
      Tendsto twoUseHalf atTop atTop ∧ Tendsto capacity atTop atTop := by
  have hc : Tendsto chi atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall hchi_nonneg)
    · filter_upwards [eventually_ge_atTop 2] with K hK
      exact hchi K hK
    · exact separationUpper_tendsto_zero
  have ht : Tendsto twoUseHalf atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ separationLower_tendsto_atTop
    filter_upwards [eventually_ge_atTop 2] with K hK
    exact htwo K hK
  exact ⟨hc, ht, tendsto_atTop_mono hcapacity ht⟩

/-- The pointwise epsilon/rate separation follows from the actual sequence. -/
theorem exists_small_large_of_bounds
    (chi twoUseHalf : ℕ → ℝ)
    (hchi_nonneg : ∀ K, 0 ≤ chi K)
    (hchi : ∀ K, 2 ≤ K → chi K ≤ separationUpper K)
    (htwo : ∀ K, 2 ≤ K → separationLower K ≤ twoUseHalf K)
    {ε R : ℝ} (hε : 0 < ε) :
    ∃ K, 2 ≤ K ∧ chi K ≤ ε ∧ R ≤ twoUseHalf K := by
  obtain ⟨hc, ht, _⟩ :=
    vanishing_diverging_of_bounds chi twoUseHalf twoUseHalf hchi_nonneg hchi htwo
      (fun _ => le_rfl)
  have hsmall : ∀ᶠ K in atTop, chi K < ε := hc.eventually (gt_mem_nhds hε)
  have hlarge : ∀ᶠ K in atTop, R ≤ twoUseHalf K := ht.eventually (eventually_ge_atTop R)
  exact (by
    filter_upwards [eventually_ge_atTop 2, hsmall, hlarge] with K hK hs hl
    exact ⟨hK, hs.le, hl⟩ : ∀ᶠ K in atTop, 2 ≤ K ∧ chi K ≤ ε ∧ R ≤ twoUseHalf K).exists

/-- Regrouping tensor powers of one fixed channel cannot produce a linear gap.
The sole hypothesis is the normalized Holevo convergence defining its capacity.
The conclusion uses the actual regrouped expression, including at `m = 0`. -/
theorem regrouping_gap_div_tendsto_zero (chi : ℕ → ℝ) (C : ℝ)
    (h : Tendsto (fun m : ℕ => chi m / m) atTop (𝓝 C)) :
    Tendsto (fun m : ℕ => (chi (2 * m) - 2 * chi m) / m) atTop (𝓝 0) := by
  have hd : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m : ℕ => show id m ≤ 2 * m by change m ≤ 2 * m; omega) tendsto_id
  have hh : Tendsto (fun m : ℕ =>
      2 * (chi (2 * m) / (2 * m : ℕ) - chi m / m)) atTop (𝓝 0) := by
    simpa using ((h.comp hd).sub h).const_mul 2
  convert hh using 1
  ext m
  by_cases hm : m = 0
  · simp [hm]
  · have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    push_cast
    field_simp

end

end Nonadditivity.Asymptotics
