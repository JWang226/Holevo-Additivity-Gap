import Nonadditivity.WeylPowersEntropy
/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

/-! Expected statement only. Index `n` denotes `n+1` actual channel uses.
The intentional `sorry` is confined to the challenge side. -/
noncomputable section
namespace Nonadditivity.WeylPowers
open Entropy Channels Channels.KrausChannel RegularizedHolevo

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
variable {d : ℕ} [NeZero d]

theorem checked_positiveTensorPower_weylExtension_holevoBits (T : KrausChannel ι (ZMod d) κ)
    (n : ℕ) :
    (positiveTensorPower T.weylExtension n).holevoBits =
      ((n + 1 : ℕ) : ℝ) * Scalar.log2 d -
        (positiveTensorPower T n).minimumEntropy / Real.log 2 := by
  exact Nonadditivity.WeylPowers.positiveTensorPower_weylExtension_holevoBits T n

end Nonadditivity.WeylPowers
