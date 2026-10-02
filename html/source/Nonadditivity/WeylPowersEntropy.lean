/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeylPowersChannels
import Nonadditivity.WeylPowersTwirl

/-! # Minimum output entropy of arbitrary tensor powers of measured extensions -/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Entropy RegularizedHolevo WeylPowers

variable {ι ο κ ζ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype ζ] [DecidableEq ζ]

/-- Measuring a finite register and applying branch-dependent output unitaries
preserves the exact minimum output entropy. No minimizing state is assumed. -/
theorem covariantExtension_minimumEntropy [Nonempty ι] [Nonempty ζ]
    (T : KrausChannel ι ο κ) (U : ζ → unitary (Matrix ο ο ℂ)) :
    (T.covariantExtension U).minimumEntropy = T.minimumEntropy := by
  apply le_antisymm
  · apply le_csInf (T.outputs_nonempty.image _)
    rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    let z : ζ := Classical.arbitrary ζ
    have h := StateEnsembles.minimumEntropy_le
      (outputs := (T.covariantExtension U).outputs)
      (ρ := (T.covariantExtension U).output (labelledState z ρ)) ⟨_, rfl⟩
    change (T.covariantExtension U).minimumEntropy ≤ _ at h
    simpa only [covariantExtension, controlled_output_labelled, outputUnitary_entropy] using h
  · apply le_csInf ((T.covariantExtension U).outputs_nonempty.image _)
    rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    exact T.covariantExtension_entropy_lower U
      (fun σ => StateEnsembles.minimumEntropy_le (outputs := T.outputs) ⟨σ, rfl⟩) ρ

end Nonadditivity.Channels.KrausChannel

namespace Nonadditivity.WeylPowers

open Entropy Channels Channels.KrausChannel RegularizedHolevo

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
variable {d : ℕ} [NeZero d]

/-- Full local Weyl randomization yields the exact Holevo/minimum-entropy
identity on any joint channel, including channels with entangled optimal inputs. -/
theorem tensorWeylExtension_holevo (n : ℕ)
    (T : KrausChannel ι (PositiveTensorIndex (ZMod d) n) κ) :
    (T.covariantExtension (positiveUnitaryPower Weyl.family n)).holevo =
      ((n + 1 : ℕ) : ℝ) * Real.log d - T.minimumEntropy := by
  apply le_antisymm
  · have h := (T.covariantExtension (positiveUnitaryPower Weyl.family n)).holevo_le_of_output_entropy
      (T.covariantExtension_entropy_lower (positiveUnitaryPower Weyl.family n)
        (fun ρ => StateEnsembles.minimumEntropy_le (outputs := T.outputs) ⟨ρ, rfl⟩))
    simpa only [positiveTensorIndex_card, ZMod.card, Nat.cast_pow, Real.log_pow] using h
  · have hglb : ((n + 1 : ℕ) : ℝ) * Real.log d -
        (T.covariantExtension (positiveUnitaryPower Weyl.family n)).holevo ≤ T.minimumEntropy := by
      apply le_csInf (T.outputs_nonempty.image _)
      rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
      have h := WeylPowersTwirl.orbit_information_lower_bound_log n
        (T.covariantExtension (positiveUnitaryPower Weyl.family n)).outputs (T.output ρ)
        (fun q => ?_)
      · change ((n + 1 : ℕ) : ℝ) * Real.log d - (T.output ρ).vonNeumann ≤
          (T.covariantExtension (positiveUnitaryPower Weyl.family n)).holevo at h
        linarith
      · refine ⟨labelledState q ρ, ?_⟩
        change (controlled (fun q => T.outputUnitary (positiveUnitaryPower Weyl.family n q))).output
          (labelledState q ρ) = _
        rw [controlled_output_labelled, outputUnitary_output]
    linarith

/-- The all-use Shor/Weyl equality for the actual tensor powers of one fixed
Weyl extension. Index `n` means `n+1` uses. -/
theorem positiveTensorPower_weylExtension_holevo (T : KrausChannel ι (ZMod d) κ) (n : ℕ) :
    (positiveTensorPower T.weylExtension n).holevo =
      ((n + 1 : ℕ) : ℝ) * Real.log d - (positiveTensorPower T n).minimumEntropy := by
  change (positiveTensorPower (T.covariantExtension Weyl.family) n).holevo = _
  rw [positiveTensorPower_covariant_holevo, tensorWeylExtension_holevo]

/-- The same complete equality in bits, suitable for the all-use regularized rate. -/
theorem positiveTensorPower_weylExtension_holevoBits (T : KrausChannel ι (ZMod d) κ) (n : ℕ) :
    (positiveTensorPower T.weylExtension n).holevoBits =
      ((n + 1 : ℕ) : ℝ) * Scalar.log2 d -
        (positiveTensorPower T n).minimumEntropy / Real.log 2 := by
  rw [holevoBits, positiveTensorPower_weylExtension_holevo]
  unfold Scalar.log2
  ring

end Nonadditivity.WeylPowers
