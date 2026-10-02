/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Net
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar consequences of the actual block norm certificate

These lemmas insert the exact Collins--Youn constant and output dimension
into the channel entropy bounds.  Entropies here use natural logarithms.
The tolerance can be chosen arbitrarily small using `κ = exp (η/2)`.
-/

noncomputable section

namespace Nonadditivity.BlockScalars

/-- The exact logarithmic loss after inserting `c_n²`. -/
theorem log_purity_factor_le {K n : ℕ} {κ : ℝ} (hK : 2 ≤ K) (hκ : 1 ≤ κ) :
    Real.log (1 + (K : ℝ) ^ n * (κ * collinsYounConstant K n) ^ 2) ≤
      (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + 2 * Real.log κ := by
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hκpos : 0 < κ := by linarith
  have hleft : 0 < 1 + (K : ℝ) ^ n * (κ * collinsYounConstant K n) ^ 2 := by positivity
  have hb : 0 < 1 + 9 / (K : ℝ) := by positivity
  have hp := collinsYoun_purity_factor_le (n := n) hK hκ
  have hl := Real.log_le_log hleft hp
  rw [Real.log_mul (pow_ne_zero _ hκpos.ne') (pow_ne_zero _ hb.ne'),
    Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

def amplification (η : ℝ) : ℝ := Real.exp (η / 2)

theorem amplification_gt_one {η : ℝ} (hη : 0 < η) : 1 < amplification η := by
  dsimp [amplification]
  exact Real.one_lt_exp_iff.mpr (by linarith)

theorem amplification_log (η : ℝ) : 2 * Real.log (amplification η) = η := by
  rw [amplification, Real.log_exp]
  ring

theorem amplification_times_constant_pos {K n : ℕ} {η : ℝ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) :
    0 < amplification η * collinsYounConstant K n :=
  mul_pos (Real.exp_pos _) (collinsYounConstant_pos hK hn)

/-- Arbitrarily small additive entropy loss from an arbitrarily accurate
finite-dimensional norm approximation. -/
theorem log_purity_factor_le_eta {K n : ℕ} {η : ℝ}
    (hK : 2 ≤ K) (hη : 0 < η) :
    Real.log (1 + (K : ℝ) ^ n *
      (amplification η * collinsYounConstant K n) ^ 2) ≤
      (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + η := by
  have hh := log_purity_factor_le (n := n) hK (amplification_gt_one hη).le
  rw [amplification_log] at hh
  exact hh

theorem log_output_dimension {K n : ℕ} :
    Real.log ((K ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log (K : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow]

/-- Exact cancellation of the two-copy output dimension with the Bell entropy
upper bound; no asymptotic remainder is introduced. -/
theorem two_use_entropy_cancellation (K n : ℕ) :
    2 * Real.log ((K ^ n : ℕ) : ℝ) -
      (n : ℝ) * (2 * Real.log (K : ℝ) - Real.log (K : ℝ) / K) =
        (n : ℝ) * Real.log (K : ℝ) / K := by
  rw [log_output_dimension]
  ring

def gapCoefficient (K : ℕ) : ℝ :=
  Real.log (K : ℝ) / K - 2 * Real.log (1 + 9 / (K : ℝ))

/-- The Holevo gap after discharging the actual dimension and purity scalars. -/
theorem gap_of_converted_bounds {K n : ℕ} {χ₁ χ₂ η : ℝ}
    (hχ₁ : χ₁ ≤ (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + η)
    (hχ₂ : (n : ℝ) * Real.log (K : ℝ) / K ≤ χ₂) :
    (n : ℝ) * gapCoefficient K - 2 * η ≤ χ₂ - 2 * χ₁ := by
  have he : (n : ℝ) * gapCoefficient K - 2 * η =
      (n : ℝ) * Real.log (K : ℝ) / K -
        2 * ((n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + η) := by
    dsimp [gapCoefficient]
    ring
  rw [he]
  linarith

theorem capacity_gap_of_converted_bounds {K n : ℕ} {χ₁ χ₂ C η : ℝ}
    (hχ₁ : χ₁ ≤ (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + η)
    (hχ₂ : (n : ℝ) * Real.log (K : ℝ) / K ≤ χ₂)
    (hC : χ₂ / 2 ≤ C) :
    (n : ℝ) * gapCoefficient K / 2 - η ≤ C - χ₁ := by
  have he : (n : ℝ) * gapCoefficient K / 2 - η =
      ((n : ℝ) * Real.log (K : ℝ) / K) / 2 -
        ((n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + η) := by
    dsimp [gapCoefficient]
    ring
  rw [he]
  linarith

end Nonadditivity.BlockScalars
