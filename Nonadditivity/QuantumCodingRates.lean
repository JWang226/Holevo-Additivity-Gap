/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalCapacity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! # Integer message counts and the vanishing coding error

Rounding exponential message counts up preserves the desired communication
rate. The finite typical-projector packing bound tends to zero whenever
that rate lies strictly below the interference exponent.
-/

noncomputable section
namespace Nonadditivity.QuantumCoding

open Filter Topology

/-- Positive integer message counts at a specified rate in nats. -/
def expMessages (r : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.exp (((n + 1 : ℕ) : ℝ) * r)⌉₊

theorem expMessages_pos (r : ℝ) (n : ℕ) : 0 < expMessages r n := by
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

theorem expMessages_lower (r : ℝ) (n : ℕ) :
    Real.exp (((n + 1 : ℕ) : ℝ) * r) ≤ (expMessages r n : ℝ) :=
  Nat.le_ceil _

theorem expMessages_upper {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (expMessages r n : ℝ) ≤ 2 * Real.exp (((n + 1 : ℕ) : ℝ) * r) := by
  have hc := Nat.ceil_lt_add_one (Real.exp_nonneg (((n + 1 : ℕ) : ℝ) * r))
  have he : 1 ≤ Real.exp (((n + 1 : ℕ) : ℝ) * r) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hr)
  change (⌈Real.exp (((n + 1 : ℕ) : ℝ) * r)⌉₊ : ℝ) ≤ _
  linarith

/-- The rounded message counts meet the target rate at every length. -/
theorem expMessages_rate_lower (r : ℝ) (n : ℕ) :
    r / Real.log 2 ≤ Scalar.log2 (expMessages r n) / ((n + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log (Real.exp_pos _) (expMessages_lower r n)
  rw [Real.log_exp] at hlog
  apply (le_div_iff₀ hn).mpr
  apply (le_div_iff₀ Scalar.log_two_pos).mpr
  have hcancel : r / Real.log 2 * ((n + 1 : ℕ) : ℝ) * Real.log 2 =
      ((n + 1 : ℕ) : ℝ) * r := by
    field_simp
  rwa [hcancel]

theorem inverse_blocklength_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).comp
    (tendsto_add_atTop_nat 1)

theorem exp_negative_blocklength_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-((n + 1 : ℕ) : ℝ) * c)) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg (-c))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc))
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using
    h.comp (tendsto_add_atTop_nat 1)

/-- Explicit upper bound after choosing the integer number of messages. -/
theorem expMessages_interference_le {r : ℝ} (hr : 0 ≤ r) (I : ℝ) (n : ℕ) :
    (expMessages r n : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) * I) ≤
      2 * Real.exp (-((n + 1 : ℕ) : ℝ) * (I - r)) := by
  calc
    _ ≤ (2 * Real.exp (((n + 1 : ℕ) : ℝ) * r)) *
        Real.exp (-((n + 1 : ℕ) : ℝ) * I) :=
      mul_le_mul_of_nonneg_right (expMessages_upper hr n) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The actual finite packing estimate vanishes with positive rate slack. -/
theorem packingError_tendsto_zero {r I : ℝ} (hr : 0 ≤ r) (hgap : r < I)
    (V : ℝ) :
    Tendsto (fun n : ℕ => V / ((n + 1 : ℕ) : ℝ) +
      4 * (expMessages r n : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) * I))
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n : ℕ => V / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using inverse_blocklength_tendsto.const_mul V
  have hsecond : Tendsto (fun n : ℕ =>
      4 * (expMessages r n : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) * I))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity)
      (fun n => ?_) (by
        simpa only [mul_zero] using
          (exp_negative_blocklength_tendsto (sub_pos.mpr hgap)).const_mul 8)
    have h := expMessages_interference_le hr I n
    nlinarith
  simpa only [zero_add] using hfirst.add hsecond

/-- Assemble an actual code at every length into an operationally achievable
rate. The premise is a quantitative statement about physical code errors,
and is discharged by the finite packing construction. -/
theorem achievableRate_of_finite_codes {ι ο κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]
    (T : Channels.KrausChannel ι ο κ) {r I : ℝ}
    (hr : 0 ≤ r) (hgap : r < I) (V : ℝ)
    (hcode : ∀ n, ∃ C : Operational.Code (RegularizedHolevo.positiveTensorPower T n)
      (expMessages r n), C.error ≤ V / ((n + 1 : ℕ) : ℝ) +
        4 * (expMessages r n : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) * I)) :
    Operational.AchievableRate T (r / Real.log 2) := by
  classical
  let S : Operational.CodeSequence T := {
    messages := expMessages r
    messages_pos := expMessages_pos r
    code := fun n => (hcode n).choose }
  refine ⟨S, ?_, ?_⟩
  · apply squeeze_zero (fun n => (S.code n).error_nonneg)
      (fun n => (hcode n).choose_spec) (packingError_tendsto_zero hr hgap V)
  · intro q hq
    apply Filter.Eventually.of_forall
    intro n
    exact hq.le.trans (expMessages_rate_lower r n)

end Nonadditivity.QuantumCoding
