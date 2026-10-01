/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.SmallEnvironment
import Nonadditivity.ActualConsequences

/-! # Information bounds from a normalized rectangular Gaussian certificate

This deterministic layer turns the concrete adjoint estimate into positive
single-use Holevo information and a lower bound on the two-use ratio.
-/

noncomputable section
set_option maxHeartbeats 600000

namespace Nonadditivity.GaussianChannelBounds

open Channels ActualConsequences
open scoped Matrix.Norms.L2Operator

theorem natural_bounds {K N : ℕ} [NeZero K] [NeZero N] (hK : 2 ≤ K)
    (T : KrausChannel (Fin N) (ZMod K) (Fin N))
    (hcert : ∀ A : Matrix (ZMod K) (ZMod K) ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ (512 / (K : ℝ)) * AdjointPurity.hsLength A) :
    0 < (Conversion.converted T).holevo ∧
    (Conversion.converted T).holevo ≤ 512^2 / (K : ℝ) ∧
    (Real.log (K : ℝ) - 1) / K ≤
      ((Conversion.converted T).tensor (Conversion.converted T)).holevo := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  obtain ⟨hu, hl, _⟩ := GeneralBell.converted_bounds T le_rfl
    (show 0 ≤ 512 / (K : ℝ) by positivity) hcert
  refine ⟨SmallEnvironment.converted_holevo_pos hK T, hu.trans ?_, hl⟩
  have he : (K : ℝ) * (512 / (K : ℝ))^2 = 512^2 / (K : ℝ) := by
    field_simp
  rw [he]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < 1 + 512^2 / (K : ℝ) by positivity)
  linarith

/-- Positive Holevo information makes the ratio an actual quotient with
a nonzero denominator. All information quantities here are in bits. -/
theorem converted_bounds {K N : ℕ} [NeZero K] [NeZero N] (hK : 2 ≤ K)
    (hlog : 0 ≤ Real.log (K : ℝ) - 1)
    (T : KrausChannel (Fin N) (ZMod K) (Fin N))
    (hcert : ∀ A : Matrix (ZMod K) (ZMod K) ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ (512 / (K : ℝ)) * AdjointPurity.hsLength A) :
    let Q := FiniteQuantumChannel.ofKraus (Conversion.converted T)
    0 < Q.chi ∧ Q.chi ≤ 512^2 / ((K : ℝ) * Real.log 2) ∧
      (Real.log (K : ℝ) - 1) / (2 * 512^2) ≤ Q.twoUseRatio ∧
      Fintype.card Q.Input = 2 * N * K^2 ∧ Fintype.card Q.Output = K := by
  dsimp only
  obtain ⟨hp, hu, hl⟩ := natural_bounds hK T hcert
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hratio : (Real.log (K : ℝ) - 1) / (2 * 512^2) ≤
      ((Conversion.converted T).tensor (Conversion.converted T)).holevo /
        (2 * (Conversion.converted T).holevo) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ((Real.log (K : ℝ) - 1) / (2 * 512^2)) * (2 * (512^2 / K)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (Real.log (K : ℝ) - 1) / K := by ring
      _ ≤ _ := hl
  refine ⟨div_pos hp Scalar.log_two_pos, ?_, ?_, ?_, ?_⟩
  · change (Conversion.converted T).holevo / Real.log 2 ≤ _
    convert div_le_div_of_nonneg_right hu Scalar.log_two_pos.le using 1
    ring
  · change _ ≤ (((Conversion.converted T).tensor (Conversion.converted T)).holevo /
      Real.log 2) / (2 * ((Conversion.converted T).holevo / Real.log 2))
    convert hratio using 1
    field_simp [hp.ne']
  · change Fintype.card ((ZMod K × ZMod K) × (Bool × Fin N)) = _
    simpa using (Conversion.converted_input_dimension (ι := Fin N) (d := K))
  · exact ZMod.card K

end Nonadditivity.GaussianChannelBounds
