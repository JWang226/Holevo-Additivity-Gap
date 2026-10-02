/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarConsequences
import Nonadditivity.HaarMomentTail

/-! # One-sided Haar upper tails suffice for channel separation

The channel proof uses no lower spectral convergence. This module proves the
finite-net selection directly from upper tails and connects that weaker input
to actual channel bounds. The Haar upper-tail estimate itself is not assumed
proved by the existence of this interface.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.UpperHaarRealization

open MeasureTheory Filter FiniteRealization AdjointPurity BlockConstruction
open Channels.KrausChannel BlockScalars ActualConsequences
open scoped Topology Matrix.Norms.L2Operator

section FiniteNet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Only the upper deviations on each fixed sphere point are needed to
construct an eventual uniform norm certificate. -/
theorem eventually_exists_certificate_of_upper_tails
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {F : ν → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (μ : (i : ν) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : (i : ν) → Ω i → E →L[ℝ] F i) (l : Filter ν)
    {κ c : ℝ} (hκ : 1 < κ) (hc : 0 < c)
    (htail : ∀ y, ‖y‖ = 1 → ∀ ε : ℝ, 0 < ε → Tendsto
      (fun i => μ i {ω | c + ε ≤ ‖T i ω y‖}) l (𝓝 0)) :
    ∀ᶠ i in l, ∃ ω, ∀ x : E, ‖T i ω x‖ ≤ κ * c * ‖x‖ := by
  have hd : 0 < κ + 1 := by linarith
  have hr : 0 < (κ - 1) / (κ + 1) := div_pos (by linarith) hd
  have hr1 : (κ - 1) / (κ + 1) < 1 := by
    apply (div_lt_one hd).mpr
    linarith
  obtain ⟨tests, hunit, hnet⟩ := exists_unitSphereNet (E := E) hr
  have hB : 0 < (1 + (κ - 1) / (κ + 1)) * c := mul_pos (by linarith) hc
  have hf : ∀ y ∈ tests, Tendsto
      (fun i => μ i {ω | (1 + (κ - 1) / (κ + 1)) * c < ‖T i ω y‖}) l (𝓝 0) := by
    intro y hy
    have h := htail y (hunit y hy) (((κ - 1) / (κ + 1)) * c) (mul_pos hr hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le _) ?_
    intro i
    apply measure_mono
    intro ω hω
    dsimp only [Set.mem_setOf_eq] at hω
    change c + (κ - 1) / (κ + 1) * c ≤ ‖T i ω y‖
    nlinarith
  have hcert := eventually_exists_norm_certificate_of_test_failures
    μ T l hr.le hr1 hB.le hnet hf
  have heq : ((1 + (κ - 1) / (κ + 1)) * c) /
      (1 - (κ - 1) / (κ + 1)) = κ * c := by
    field_simp
    ring
  exact hcert.mono fun i ⟨ω, _, hω⟩ => ⟨ω, by simpa only [heq] using hω⟩

end FiniteNet

variable {K : ℕ} [NeZero K]

/-- The precise weaker input: the upper tail above the proved CY constant
vanishes on each fixed normalized traceless Hermitian test. -/
def HaarUpperConvergence (K n : ℕ) [NeZero K] : Prop :=
  ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
    A.IsHermitian → A.trace = 0 → hsLength A = 1 →
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun N => HaarModel.sampleMeasure K n N {ω |
        collinsYounConstant K n + ε ≤
          ‖(blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A‖})
      atTop (𝓝 0)

/-- A literal sufficient high-moment estimate for the canonical Haar model.
The order may grow with the input dimension and may depend on the fixed test
and tolerance. This estimate remains an analytic obligation. -/
def HaarTraceMomentControl (K n : ℕ) [NeZero K] : Prop :=
  ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
    A.IsHermitian → A.trace = 0 → hsLength A = 1 →
    ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → ℕ, Tendsto (fun N =>
      (∫⁻ ω, ENNReal.ofReal
        ((((blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A)
          ^ (2 * p N)).trace.re) ∂HaarModel.sampleMeasure K n N) /
        ENNReal.ofReal (collinsYounConstant K n + ε) ^ (2 * p N))
      atTop (𝓝 0)

/-- The high-moment criterion implies exactly the upper tails consumed by
the finite-net channel argument. -/
theorem upper_of_trace_moments {n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (hmoment : HaarTraceMomentControl K n) : HaarUpperConvergence K n := by
  intro A hA ht hhs ε hε
  obtain ⟨p, hp⟩ := hmoment A hA ht hhs ε hε
  exact HaarMomentTail.canonical_upper_tail_of_trace_moments n A hA p
    (add_pos (collinsYounConstant_pos hK hn) hε) hp

theorem upper_of_strong {n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (hBC : HaarModel.HaarStrongConvergence K n) : HaarUpperConvergence K n := by
  intro A hA ht hhs ε hε
  have hfree := FreeBridge.outputFreeNorm_unit_bound
    (CollinsYounProduct.collinsYounBound hK hn) A hA ht hhs
  have h := hBC A hA ht hhs ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le _) ?_
  intro N
  apply measure_mono
  intro ω hω
  dsimp only [Set.mem_setOf_eq] at hω
  have habs := le_abs_self
    (‖(blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A‖ -
      FreeBridge.outputFreeNorm K n A)
  change ε ≤ |‖(blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A‖ -
    FreeBridge.outputFreeNorm K n A|
  linarith

theorem eventually_exists_certificate {n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    {κ : ℝ} (hκ : 1 < κ) (hupper : HaarUpperConvergence K n) :
    ∀ᶠ N in atTop, ∃ ω,
      ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
        A.IsHermitian → A.trace = 0 →
        ‖(blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A‖ ≤
          κ * collinsYounConstant K n * hsLength A := by
  have hcert := eventually_exists_certificate_of_upper_tails
    (E := ObservableSpace (ZMod (K ^ n)))
    (HaarModel.sampleMeasure K n)
    (fun N ω => adjointOnObservables (blockChannel (HaarModel.sampleUnitary K n N ω) n))
    atTop hκ (collinsYounConstant_pos hK hn)
    (fun x hx ε hε => by
      simpa only [adjointOnObservables_apply] using
        hupper (observableMatrix x) (observableMatrix_isHermitian x)
          (observableMatrix_trace_zero x) (by rwa [← observable_norm_eq_hsLength]) ε hε)
  exact hcert.mono fun N ⟨ω, hω⟩ => ⟨ω,
    matrix_certificate_of_observable_bound _ (κ * collinsYounConstant K n) hω⟩

/-- The actual finite-channel estimates use only the stated one-sided tail.
No lower convergence to the free operator norm is required. -/
theorem exists_block_channel {n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    {η : ℝ} (hη : 0 < η) (hupper : HaarUpperConvergence K n) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      T.chi ≤ (n : ℝ) * Scalar.aK K + η ∧
      (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo ∧
      (n : ℝ) * Scalar.deltaK K - 2 * η ≤ T.gap := by
  let ε := η * Real.log 2
  have hε : 0 < ε := mul_pos hη Scalar.log_two_pos
  obtain ⟨N, ω, hω⟩ :=
    (eventually_exists_certificate hK hn (amplification_gt_one hε) hupper).exists
  let U := HaarModel.sampleUnitary K n N ω
  have h := block_converted_bounds_of_certificate U n
    (amplification_times_constant_pos (η := ε) hK hn).le hω
  have hu := h.1.trans (log_purity_factor_le_eta hK hε)
  let T := FiniteQuantumChannel.ofKraus (Conversion.converted (blockChannel U n))
  have hp : 0 < T.chi := PositiveHolevo.block_converted_holevoBits_pos hK U hn
  have hu' : T.chi ≤ (n : ℝ) * Scalar.aK K + η := HolevoBits.natural_upper_to_bits n hu
  have hl : (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo :=
    HolevoBits.natural_lower_to_bits n h.2.1
  refine ⟨T, hp, hu', hl, ?_⟩
  unfold FiniteQuantumChannel.gap Scalar.deltaK
  rw [mul_sub, ← mul_div_assoc]
  nlinarith only [hu', hl]

/-- Direct end-to-end route from the literal high-trace estimate to the
finite channel and all three information bounds. -/
theorem exists_block_channel_of_trace_moments {n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    {η : ℝ} (hη : 0 < η) (hmoment : HaarTraceMomentControl K n) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      T.chi ≤ (n : ℝ) * Scalar.aK K + η ∧
      (n : ℝ) * Scalar.log2 K / (K : ℝ) ≤ T.chiTwo ∧
      (n : ℝ) * Scalar.deltaK K - 2 * η ≤ T.gap :=
  exists_block_channel hK hn hη (upper_of_trace_moments hK hn hmoment)

theorem exists_arbitrarily_large_gap (hK : 2 ≤ K) (hlog : 18 < Real.log (K : ℝ))
    (hupper : ∀ n : ℕ, 1 ≤ n → HaarUpperConvergence K n) (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ R ≤ T.gap := by
  have hδ := Scalar.deltaK_pos
    (show (0 : ℝ) < K by exact_mod_cast (by omega : 0 < K)) hlog
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + Scalar.deltaK K / 2) / Scalar.deltaK K)
  have hmul := (div_lt_iff₀ hδ).mp hn
  obtain ⟨T, hp, _, _, hg⟩ := exists_block_channel hK
    (show 1 ≤ n + 1 by omega) (show 0 < Scalar.deltaK K / 4 by positivity)
    (hupper (n+1) (by omega))
  refine ⟨T, hp, ?_⟩
  push_cast at hg
  nlinarith

/-- The remaining upper-tail assertion at every fixed parameter pair. -/
def AllHaarUpperConvergence : Prop :=
  ∀ (K : ℕ) [NeZero K] (n : ℕ), 2 ≤ K → 1 ≤ n → HaarUpperConvergence K n

/-- An unbounded additive gap needs only the one-sided canonical Haar tails. -/
theorem exists_arbitrarily_large_gap_of_all_upper
    (hupper : AllHaarUpperConvergence) (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ R ≤ T.gap := by
  let K : ℕ := max 2 ⌈Real.exp 19⌉₊
  have hK : 2 ≤ K := le_max_left _ _
  letI : NeZero K := ⟨by omega⟩
  have hceil : (⌈Real.exp 19⌉₊ : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (le_max_right 2 ⌈Real.exp 19⌉₊)
  have hlog := Real.log_le_log (Real.exp_pos 19) ((Nat.le_ceil _).trans hceil)
  rw [Real.log_exp] at hlog
  exact exists_arbitrarily_large_gap hK (by linarith)
    (fun n hn => hupper K n hK hn) R

/-- The one-block multiplicative lower bound also consumes only an upper tail. -/
theorem exists_one_block_ratio (hK : 2 ≤ K) (hupper : HaarUpperConvergence K 1) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧
      Real.log (K : ℝ) / 36 ≤ T.twoUseRatio := by
  have hKr : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hKpos : (0 : ℝ) < K := by linarith
  obtain ⟨T, hp, hu, hl, _⟩ := exists_block_channel hK
    (by omega : 1 ≤ 1) (Scalar.aK_pos hKpos) hupper
  simp only [Nat.cast_one, one_mul] at hu hl
  refine ⟨T, hp, ?_⟩
  have hnum : 0 ≤ Scalar.log2 K / (K : ℝ) := by
    unfold Scalar.log2
    exact div_nonneg (div_nonneg (Real.log_pos hKr).le Scalar.log_two_pos.le) hKpos.le
  unfold FiniteQuantumChannel.twoUseRatio
  calc
    Real.log (K : ℝ) / 36 = (Real.log (K : ℝ) / 18) / 2 := by ring
    _ ≤ (Scalar.log2 K / (2 * (K : ℝ) * Scalar.aK K)) / 2 :=
      div_le_div_of_nonneg_right (Scalar.ratio_lower hKr) (by norm_num)
    _ = (Scalar.log2 K / (K : ℝ)) / (4 * Scalar.aK K) := by field_simp; ring
    _ ≤ (Scalar.log2 K / (K : ℝ)) / (2 * T.chi) :=
      div_le_div_of_nonneg_left hnum (by positivity) (by linarith)
    _ ≤ T.chiTwo / (2 * T.chi) := div_le_div_of_nonneg_right hl (by positivity)

theorem exists_arbitrarily_large_ratio
    (hupper : ∀ (K : ℕ) [NeZero K], 2 ≤ K → HaarUpperConvergence K 1) (R : ℝ) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ R ≤ T.twoUseRatio := by
  let L : ℝ := 36 * max R 0 + 1
  let K : ℕ := max 2 ⌈Real.exp L⌉₊
  have hK : 2 ≤ K := le_max_left _ _
  letI : NeZero K := ⟨by omega⟩
  have hceil : (⌈Real.exp L⌉₊ : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (le_max_right 2 ⌈Real.exp L⌉₊)
  have hlog := Real.log_le_log (Real.exp_pos L) ((Nat.le_ceil _).trans hceil)
  rw [Real.log_exp] at hlog
  obtain ⟨T, hp, hr⟩ := exists_one_block_ratio hK (hupper K hK)
  refine ⟨T, hp, ?_⟩
  have hmax : R ≤ max R 0 := le_max_left _ _
  dsimp [L] at hlog
  linarith

end Nonadditivity.UpperHaarRealization
