/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianCertificates
import Nonadditivity.GaussianSampleEvaluation
import Nonadditivity.InitialNetReduction

/-! # Unconditional finite Gaussian channel construction

An actual rectangular Gaussian sample simultaneously passes the two finite
nets, and its polar normalization gives an actual trace-preserving channel.
No Haar convergence or concentration proposition is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Nonadditivity.GaussianConstruction

open MeasureTheory ProbabilityTheory FiniteRealization GaussianRectangular
  GaussianNormalization GaussianNetRealization Channels
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- A finite channel with a dimension-independent Hilbert--Schmidt-to-operator
constant, constructed with no unproved probabilistic assumption. -/
theorem exists_channel (K N : ℕ) [NeZero K]
    (hK : 4096 ≤ K) (hN : K ^ 2 ≤ N) :
    ∃ T : KrausChannel (Fin N) (ZMod K) (Fin N),
      ∀ A : Matrix (ZMod K) (ZMod K) ℂ, A.IsHermitian → A.trace = 0 →
        ‖T.adjointMap A‖ ≤ (512 / (K : ℝ)) * AdjointPurity.hsLength A := by
  classical
  have hKnat : 0 < K := by omega
  have hNnat : 0 < N := lt_of_lt_of_le (pow_pos hKnat _) hN
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKnat
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNnat
  letI : NeZero N := ⟨ne_of_gt hNnat⟩
  obtain ⟨inputs, hiunit, hinet, hicard⟩ := QuadraticNet.exists_complex_input_net (Fin N)
  obtain ⟨outputs, hounit, honet, hocard⟩ := QuadraticNet.exists_observable_net (ZMod K)
  let T₀ : inputs → Sample (ZMod K) (Fin N) (Fin N) →L[ℝ]
      Sample (ZMod K) (Fin N) (Fin N) :=
    fun x => quadraticOperator (Env := Fin N) (1 : Matrix (ZMod K) (ZMod K) ℂ) x.val
  let T₁ : (outputs × inputs) → Sample (ZMod K) (Fin N) (Fin N) →L[ℝ]
      Sample (ZMod K) (Fin N) (Fin N) :=
    fun ax => quadraticOperator (Env := Fin N) (observableMatrix ax.1.val) ax.2.val
  have hhs (a : outputs) : AdjointPurity.hsLength (observableMatrix a.val) = 1 := by
    rw [← observable_norm_eq_hsLength]
    exact hounit a.val a.property
  have hop (a : outputs) : ‖observableMatrix a.val‖ ≤ 1 := by
    exact (InitialNetReduction.norm_le_hsLength _ (observableMatrix_isHermitian a.val)).trans_eq (hhs a)
  have hn₀ (x : inputs) : (2 * (K : ℝ) * N) * ‖T₀ x‖ ≤ 1 := by
    have h := quadraticOperator_norm_le (Env := Fin N)
      (1 : Matrix (ZMod K) (ZMod K) ℂ) x.val (hiunit x.val x.property)
    simp only [norm_one, ZMod.card, Fintype.card_fin] at h
    simpa only [T₀, mul_comm] using
      (le_div_iff₀ (show (0 : ℝ) < 2 * K * N by positivity)).mp h
  have hn₁ (ax : outputs × inputs) : (2 * (K : ℝ) * N) * ‖T₁ ax‖ ≤ 1 := by
    have h := quadraticOperator_norm_le (Env := Fin N)
      (observableMatrix ax.1.val) ax.2.val (hiunit ax.2.val ax.2.property)
    have hbase : ‖T₁ ax‖ ≤ ‖observableMatrix ax.1.val‖ / (2 * (K : ℝ) * N) := by
      simpa only [T₁, ZMod.card, Fintype.card_fin] using h
    have h' : ‖T₁ ax‖ ≤ 1 / (2 * (K : ℝ) * N) :=
      hbase.trans (div_le_div_of_nonneg_right (hop ax.1) (by positivity))
    simpa only [mul_comm] using (le_div_iff₀ (show (0 : ℝ) < 2 * K * N by positivity)).mp h'
  have hv₀ (x : inputs) : (2 * (K : ℝ) * N) *
      ((T₀ x).toLinearMap * (T₀ x).toLinearMap).trace ℝ (Sample (ZMod K) (Fin N) (Fin N)) ≤ 1 := by
    dsimp only [T₀]
    rw [quadraticOperator_trace_square _ _ (hiunit x.val x.property)]
    simp only [Matrix.one_mul, Matrix.trace_one, Complex.natCast_re, ZMod.card, Fintype.card_fin]
    apply le_of_eq
    field_simp
  have hv₁ (ax : outputs × inputs) : (2 * (K : ℝ) ^ 2 * N) *
      ((T₁ ax).toLinearMap * (T₁ ax).toLinearMap).trace ℝ (Sample (ZMod K) (Fin N) (Fin N)) ≤ 1 := by
    dsimp only [T₁]
    rw [quadraticOperator_trace_square _ _ (hiunit ax.2.val ax.2.property),
      ← AdjointPurity.hsLength_sq_of_isHermitian _ (observableMatrix_isHermitian ax.1.val), hhs ax.1]
    simp only [one_pow, ZMod.card, Fintype.card_fin]
    apply le_of_eq
    field_simp
  have hc₀ : (Fintype.card inputs : ℝ) ≤ (9 : ℝ) ^ (2 * N) := by
    simp only [Fintype.card_coe]
    exact_mod_cast (by simpa only [Fintype.card_fin] using hicard)
  have hc₁ : (Fintype.card (outputs × inputs) : ℝ) ≤
      (5 : ℝ) ^ (K ^ 2) * (9 : ℝ) ^ (2 * N) := by
    simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
    apply mul_le_mul
    · exact_mod_cast (by simpa only [ZMod.card] using hocard)
    · exact_mod_cast (by simpa only [Fintype.card_fin] using hicard)
    · positivity
    · positivity
  obtain ⟨z, hz₀, hz₁⟩ := GaussianCertificates.exists_isometry_and_observable_tests K N hK hN
    T₀ T₁
    (fun x => quadraticOperator_symmetric _ Matrix.isHermitian_one x.val)
    (fun ax => quadraticOperator_symmetric _ (observableMatrix_isHermitian ax.1.val) ax.2.val)
    hn₀ hn₁ hv₀ hv₁ hc₀ hc₁
  let G := sampleMatrix (ZMod K) (Fin N) (Fin N) z
  have hgram : ∀ x ∈ inputs, |quadratic (gram G) x - 1| ≤ 1 / 4 := by
    intro x hx
    have h := (hz₀ ⟨x, hx⟩).le
    dsimp only [T₀] at h
    rw [quadraticOperator_one_quadratic, quadraticOperator_trace _ _ (hiunit x hx)] at h
    simpa only [Matrix.trace_one, Complex.natCast_re, ZMod.card, div_self (ne_of_gt hKr), G] using h
  have hraw : ∀ a ∈ outputs, ∀ x ∈ inputs,
      |quadratic (rawAdjoint G (observableMatrix a)) x| ≤ 64 / (K : ℝ) := by
    intro a ha x hx
    have h := (hz₁ (⟨a, ha⟩, ⟨x, hx⟩)).le
    dsimp only [T₁] at h
    rw [quadraticOperator_quadratic, quadraticOperator_trace _ _ (hiunit x hx)] at h
    simpa only [observableMatrix_trace_zero, Complex.zero_re, zero_div, sub_zero, G] using h
  obtain ⟨T, hT⟩ := channel_certificate_of_tests G inputs outputs hiunit hinet honet
    (64 / (K : ℝ)) (by positivity) hgram hraw
  refine ⟨T, fun A hA htr => ?_⟩
  convert hT A hA htr using 1; ring

end Nonadditivity.GaussianConstruction
