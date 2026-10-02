/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeylPowersEntropy

/-! # Exact all-use regularized Weyl-extension identity -/

noncomputable section

namespace Nonadditivity.WeylPowers

open Entropy Channels Channels.KrausChannel RegularizedHolevo

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- The minimum output entropy per channel use, measured in bits. -/
def normalizedMinimumEntropy (T : KrausChannel ι ο κ) (n : ℕ) : ℝ :=
  (positiveTensorPower T n).minimumEntropy / Real.log 2 / ((n + 1 : ℕ) : ℝ)

theorem normalizedMinimumEntropy_nonneg (T : KrausChannel ι ο κ) (n : ℕ) :
    0 ≤ normalizedMinimumEntropy T n := by
  have h : 0 ≤ (positiveTensorPower T n).minimumEntropy := by
    apply le_csInf ((positiveTensorPower T n).outputs_nonempty.image _)
    rintro _ ⟨ρ, _, rfl⟩
    exact ρ.vonNeumann_nonneg
  exact div_nonneg (div_nonneg h Scalar.log_two_pos.le) (by positivity)

theorem normalizedMinimumEntropy_bddBelow (T : KrausChannel ι ο κ) :
    BddBelow (Set.range (normalizedMinimumEntropy T)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact normalizedMinimumEntropy_nonneg T n

variable {d : ℕ} [NeZero d]

theorem normalizedPowerHolevo_weylExtension (T : KrausChannel ι (ZMod d) κ) (n : ℕ) :
    normalizedPowerHolevo T.weylExtension n =
      Scalar.log2 d - normalizedMinimumEntropy T n := by
  unfold normalizedPowerHolevo normalizedMinimumEntropy
  rw [positiveTensorPower_weylExtension_holevoBits, sub_div]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hn]

/-- The regularized Holevo supremum of the actual Weyl-extension powers is
exactly the output log dimension minus the regularized minimum output entropy.
Both extrema range over every positive number of actual channel uses. -/
theorem regularized_weylExtension_holevo (T : KrausChannel ι (ZMod d) κ) :
    sSup (Set.range (normalizedPowerHolevo T.weylExtension)) =
      Scalar.log2 d - sInf (Set.range (normalizedMinimumEntropy T)) := by
  have hb : BddAbove (Set.range (normalizedPowerHolevo T.weylExtension)) := by
    refine ⟨Scalar.log2 d, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [normalizedPowerHolevo_weylExtension]
    exact sub_le_self _ (normalizedMinimumEntropy_nonneg T n)
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    rw [normalizedPowerHolevo_weylExtension]
    exact sub_le_sub_left (csInf_le (normalizedMinimumEntropy_bddBelow T) ⟨n, rfl⟩) _
  · have h : Scalar.log2 d - sSup (Set.range (normalizedPowerHolevo T.weylExtension)) ≤
        sInf (Set.range (normalizedMinimumEntropy T)) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨n, rfl⟩
      have hn := le_csSup hb (show normalizedPowerHolevo T.weylExtension n ∈
        Set.range (normalizedPowerHolevo T.weylExtension) from ⟨n, rfl⟩)
      rw [normalizedPowerHolevo_weylExtension] at hn
      linarith
    linarith

end Nonadditivity.WeylPowers
