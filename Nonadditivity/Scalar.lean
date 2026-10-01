/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Scalar consequences of the nonadditivity construction

All logarithms in information quantities are base two. This module proves
the real-variable inequalities in the manuscript. The channel quantities
are explicit real arguments: their quantum interpretation and the unitary
existence assertion are not asserted by this module.
-/

noncomputable section

namespace Nonadditivity.Scalar

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2
def aK (K : ℝ) : ℝ := log2 (1 + 9 / K)
def deltaK (K : ℝ) : ℝ := log2 K / K - 2 * aK K

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem aK_pos {K : ℝ} (hK : 0 < K) : 0 < aK K := by
  unfold aK log2
  have h9 : 0 < 9 / K := by positivity
  exact div_pos (Real.log_pos (by linarith)) log_two_pos

theorem aK_le {K : ℝ} (hK : 0 < K) : aK K ≤ 9 / (K * Real.log 2) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 9 / K by positivity)
  have h' : Real.log (1 + 9 / K) ≤ 9 / K := by linarith
  calc
    aK K ≤ (9 / K) / Real.log 2 :=
      (div_le_div_of_nonneg_right h' log_two_pos.le)
    _ = 9 / (K * Real.log 2) := by ring

theorem deltaK_lower {K : ℝ} (hK : 0 < K) :
    (Real.log K - 18) / (K * Real.log 2) ≤ deltaK K := by
  have h := aK_le hK
  unfold deltaK log2
  have heq : (Real.log K - 18) / (K * Real.log 2) =
      (Real.log K / Real.log 2) / K - 2 * (9 / (K * Real.log 2)) := by ring
  rw [heq]
  linarith

theorem deltaK_pos {K : ℝ} (hK : 0 < K) (hlog : 18 < Real.log K) :
    0 < deltaK K := by
  exact lt_of_lt_of_le (div_pos (sub_pos.mpr hlog) (mul_pos hK log_two_pos))
    (deltaK_lower hK)

theorem ratio_identity {K : ℝ} (hK : 0 < K) :
    1 + deltaK K / (2 * aK K) = log2 K / (2 * K * aK K) := by
  have ha := ne_of_gt (aK_pos hK)
  unfold deltaK
  field_simp
  ring

theorem ratio_lower {K : ℝ} (hK : 1 < K) :
    Real.log K / 18 ≤ log2 K / (2 * K * aK K) := by
  have hK0 : 0 < K := by linarith
  have ha := aK_pos hK0
  have hlog := (Real.log_pos hK).le
  have haBound := aK_le hK0
  have hd : 0 < 2 * K * aK K := by positivity
  apply (le_div_iff₀ hd).mpr
  unfold log2
  apply (le_div_iff₀ log_two_pos).mpr
  have hden : 2 * K * aK K * Real.log 2 ≤ 18 := by
    have h := (le_div_iff₀ (mul_pos hK0 log_two_pos)).mp haBound
    nlinarith
  nlinarith

/-- Equation (certificate-gap), conditional only on the two stated
Holevo estimates. This is also the last algebraic step of the main theorem. -/
theorem holevo_gap {K n η χ₁ χ₂ : ℝ}
    (hχ₁ : χ₁ ≤ n * aK K + η)
    (hχ₂ : n * (log2 K / K) ≤ χ₂) :
    n * deltaK K - 2 * η ≤ χ₂ - 2 * χ₁ := by
  unfold deltaK
  nlinarith

/-- Equation (capacity-gap), using the two-use coding lower bound. -/
theorem capacity_gap {K n η χ₁ χ₂ C : ℝ}
    (hχ₁ : χ₁ ≤ n * aK K + η)
    (hχ₂ : n * (log2 K / K) ≤ χ₂)
    (hC : χ₂ / 2 ≤ C) :
    n * deltaK K / 2 - η ≤ C - χ₁ := by
  have h := holevo_gap hχ₁ hχ₂
  linarith

/-- The scalar final step of the switch and Weyl conversion, equations
(certificate-holevo). It states exactly which entropy identities are needed. -/
theorem conversion {K n κ s₁ s₂ χ₁ χ₂ : ℝ}
    (hs₁ : n * (log2 K - aK K) - 2 * log2 κ ≤ s₁)
    (hs₂ : s₂ ≤ n * (2 * log2 K - log2 K / K))
    (hχ₁ : χ₁ = n * log2 K - s₁)
    (hχ₂ : 2 * n * log2 K - s₂ ≤ χ₂) :
    χ₁ ≤ n * aK K + 2 * log2 κ ∧
      n * (log2 K / K) ≤ χ₂ := by
  constructor <;> nlinarith

theorem purity_inflation {L r κ : ℝ} (hL : 0 < L) (hκ : 1 ≤ κ) :
    1 + L * (κ ^ 2 * ((r - 1) / L)) ≤ κ ^ 2 * r := by
  have hκsq : 1 ≤ κ ^ 2 := by nlinarith
  have hid : L * (κ ^ 2 * ((r - 1) / L)) = κ ^ 2 * (r - 1) := by
    field_simp
  rw [hid]
  nlinarith

/-- The basic implication used in Lemma (purity), including the zero case. -/
theorem norm_bound_of_square {x t : ℝ} (ht : 0 ≤ t)
    (h : x ^ 2 ≤ t * x) : x ≤ t := by
  nlinarith

end Nonadditivity.Scalar
