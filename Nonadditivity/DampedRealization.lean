/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DampingNet
import Nonadditivity.SpectralDamping

/-! Deterministic realization of a channel norm certificate from finite even moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Nonadditivity.DampedRealization
open Channels Channels.KrausChannel AdjointPurity FiniteRealization
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {ο : Type} [Fintype ο] [DecidableEq ο] [Nonempty ο]

/-- The moment order is selected before the finite input space or channel.
Every model with these moments yields an actual invertible damping with the
prescribed certificate and arbitrarily small normalized discarded mass. -/
theorem exists_moment_order {a c η : ℝ} (ha : 1 < a) (hc : 0 < c) (hη : 0 < η) :
    ∃ p : ℕ, 1 ≤ p ∧
      ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
      (T : KrausChannel ι ο κ),
      (∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 → hsLength A=1 →
        ((T.adjointMap A)^(2*p)).trace.re / (Fintype.card ι : ℝ) ≤ c^(2*p)) →
      ∃ F G : Matrix ι ι ℂ, ∃ hF : F.IsHermitian, ∃ hres : (1-F*F).PosSemidef,
        G*F=1 ∧
        (∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 →
          ‖(DampedChannel.damped T F hF hres).adjointMap A‖ ≤ a*c*hsLength A) ∧
        (1-F*F).trace.re / (Fintype.card ι : ℝ) < η := by
  classical
  let δ : ℝ := (a-1)/(a+1)
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  let L : ℝ := (1+δ)*c
  have hL : 0 < L := mul_pos (by linarith) hc
  have hcL : c < L := by dsimp [L]; nlinarith
  have hr0 : 0 ≤ c/L := div_nonneg hc.le hL.le
  have hr1 : c/L < 1 := (div_lt_one hL).mpr hcL
  obtain ⟨tests, hunit, hnet⟩ := exists_unitSphereNet (E := ObservableSpace ο) hδ
  obtain ⟨p, hp, hsmall⟩ := DampingNet.exists_even_moment_small hr0 hr1 tests.card hη
  refine ⟨p, hp, ?_⟩
  intro ι κ _ _ _ _ T hmom
  let X : tests → Matrix ι ι ℂ := fun y => T.adjointMap (observableMatrix y.val)
  have hX (y : tests) : (X y).IsHermitian :=
    T.adjointMap_isHermitian _ (observableMatrix_isHermitian y.val)
  obtain ⟨F,G,hF,hres,hGF,hbound,hloss⟩ := SpectralDamping.exists_damping X hX L hL p hp
  refine ⟨F,G,hF,hres,hGF,?_,?_⟩
  · apply DampingNet.damped_certificate T F hF hres ha hc.le hnet
    intro y hy
    exact hbound ⟨y,hy⟩
  · have hdim : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    have hterm (y : tests) :
        L⁻¹^(2*p) * (X y^(2*p)).trace.re / (Fintype.card ι : ℝ) ≤ (c/L)^(2*p) := by
      have h := hmom (observableMatrix y.val) (observableMatrix_isHermitian _)
        (observableMatrix_trace_zero _)
        (by rw [← observable_norm_eq_hsLength]; exact hunit y.val y.property)
      have h' := mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hL.le) (2*p))
      convert h' using 1 <;> dsimp only [X]
      · ring
      · rw [div_eq_mul_inv, mul_pow]; ring
    calc
      (1-F*F).trace.re / (Fintype.card ι : ℝ) ≤
          (2 * ∑ y : tests, L⁻¹^(2*p) * (X y^(2*p)).trace.re) /
            (Fintype.card ι : ℝ) := div_le_div_of_nonneg_right hloss hdim.le
      _ = 2 * ∑ y : tests, L⁻¹^(2*p) * (X y^(2*p)).trace.re /
            (Fintype.card ι : ℝ) := by rw [← Finset.sum_div]; ring
      _ ≤ 2 * ∑ _y : tests, (c/L)^(2*p) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => hterm y)) (by norm_num)
      _ = 2 * (tests.card : ℝ) * (c/L)^(2*p) := by simp; ring
      _ < η := hsmall

end Nonadditivity.DampedRealization
