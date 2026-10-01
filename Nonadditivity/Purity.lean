/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Adjoint certificate to centered purity

This formalizes the Hilbert-space argument in Lemma `purity`: the output
space carries its Hilbert--Schmidt geometry, the center is I/L, and a state
expectation is a norm-at-most-one functional on input observables. The trace
identification and the quantum channel adjoint are not constructed here;
they enter through the explicit pairing and normalization hypotheses.
-/

noncomputable section

namespace Nonadditivity.Purity

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The centered output is bounded by t whenever the channel adjoint is
bounded by t on the hyperplane orthogonal to the maximally mixed center. -/
theorem centered_norm_le (T : E →L[ℝ] F) (φ : F →L[ℝ] ℝ)
    (center Y : E) {t : ℝ} (ht : 0 ≤ t) (hφ : ‖φ‖ ≤ 1)
    (hnormalized : ⟪Y, center⟫_ℝ = ‖center‖ ^ 2)
    (hduality : ∀ A : E, ⟪center, A⟫_ℝ = 0 → ⟪Y, A⟫_ℝ = φ (T A))
    (hcertificate : ∀ A : E, ⟪center, A⟫_ℝ = 0 → ‖T A‖ ≤ t * ‖A‖) :
    ‖Y - center‖ ≤ t := by
  have horth : ⟪center, Y - center⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_comm Y center, hnormalized,
      real_inner_self_eq_norm_sq]
    exact sub_self _
  have hpair : ⟪Y, Y - center⟫_ℝ = ‖Y - center‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hnormalized,
      norm_sub_sq_real, hnormalized]
    ring
  have hnorm : ‖Y - center‖ ^ 2 ≤ t * ‖Y - center‖ := by
    calc
      ‖Y - center‖ ^ 2 = φ (T (Y - center)) := by
        rw [← hduality _ horth, hpair]
      _ ≤ ‖φ (T (Y - center))‖ := le_abs_self _
      _ ≤ ‖φ‖ * ‖T (Y - center)‖ := φ.le_opNorm _
      _ ≤ ‖T (Y - center)‖ := by
        simpa using mul_le_mul_of_nonneg_right hφ (norm_nonneg (T (Y - center)))
      _ ≤ t * ‖Y - center‖ := hcertificate _ horth
  nlinarith [norm_nonneg (Y - center)]

/-- The uncentered purity is at most the maximally mixed purity plus t². -/
theorem purity_le (T : E →L[ℝ] F) (φ : F →L[ℝ] ℝ)
    (center Y : E) {t : ℝ} (ht : 0 ≤ t) (hφ : ‖φ‖ ≤ 1)
    (hnormalized : ⟪Y, center⟫_ℝ = ‖center‖ ^ 2)
    (hduality : ∀ A : E, ⟪center, A⟫_ℝ = 0 → ⟪Y, A⟫_ℝ = φ (T A))
    (hcertificate : ∀ A : E, ⟪center, A⟫_ℝ = 0 → ‖T A‖ ≤ t * ‖A‖) :
    ‖Y‖ ^ 2 ≤ ‖center‖ ^ 2 + t ^ 2 := by
  have h := centered_norm_le T φ center Y ht hφ hnormalized hduality hcertificate
  have hsq := norm_sub_sq_real Y center
  rw [hnormalized] at hsq
  nlinarith [norm_nonneg (Y - center)]

end Nonadditivity.Purity
