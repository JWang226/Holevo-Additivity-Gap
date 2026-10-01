/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ChannelEntropy
import Nonadditivity.ConjugateChannel

/-!
# The actual two-branch switch channel

The classical input bit is measured and discarded. Its branches are a
concrete Kraus channel and its entrywise conjugate. The original outputs
remain reachable, and entropy concavity prevents arbitrary switch inputs
from lowering the minimum output entropy. Weyl extension then turns this
actual minimum output entropy into the single-use Holevo quantity.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity Entropy
open scoped BigOperators Matrix ComplexOrder

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- Measure a bit, apply the original or conjugate channel, discard the bit. -/
def switch (T : KrausChannel ι ο κ) : KrausChannel (Bool × ι) ο (Bool × κ) :=
  controlled (fun b : Bool => if b then T.conjugate else T)

/-- The original channel is the false-labelled branch of the actual switch. -/
@[simp] theorem switch_output_false (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    T.switch.output (labelledState false ρ) = T.output ρ := by
  simp [switch]

/-- The conjugate channel is the true-labelled branch of the actual switch. -/
@[simp] theorem switch_output_true (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    T.switch.output (labelledState true ρ) = T.conjugate.output ρ := by
  simp [switch]

theorem outputs_subset_switch (T : KrausChannel ι ο κ) : T.outputs ⊆ T.switch.outputs := by
  rintro _ ⟨ρ, rfl⟩
  exact ⟨labelledState false ρ, T.switch_output_false ρ⟩

/-- Arbitrary switch inputs retain every uniform entropy lower bound of the
original channel, including superpositions and entangled control inputs. -/
theorem switch_output_entropy_lower [Nonempty ι]
    (T : KrausChannel ι ο κ) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann)
    (ρ : DensityMatrix (Bool × ι)) : s ≤ (T.switch.output ρ).vonNeumann := by
  unfold switch
  apply controlled_output_entropy_lower
  intro b σ
  cases b
  · exact hentropy σ
  · change s ≤ (T.conjugate.output σ).vonNeumann
    rw [T.conjugate_output_entropy_all]
    exact hentropy σ.conjugate

/-- Uniform entropy lower bounds are equivalent for the original and switch
channels; reachability proves the reverse implication. -/
theorem output_entropy_lower_bound_switch [Nonempty ι]
    (T : KrausChannel ι ο κ) (s : ℝ) :
    (∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann) ↔
      (∀ ρ : DensityMatrix (Bool × ι), s ≤ (T.switch.output ρ).vonNeumann) := by
  constructor
  · exact T.switch_output_entropy_lower
  · intro h ρ
    have hh := h (labelledState false ρ)
    simpa only [switch_output_false] using hh

/-- The switch has exactly the original channel's minimum output entropy.
The argument uses infima and does not assume existence of a minimizing input. -/
theorem switch_minimumEntropy [Nonempty ι] (T : KrausChannel ι ο κ) :
    T.switch.minimumEntropy = T.minimumEntropy := by
  apply le_antisymm
  · unfold minimumEntropy
    apply le_csInf (T.outputs_nonempty.image _)
    rintro _ ⟨σ, ⟨ρ, rfl⟩, rfl⟩
    exact StateEnsembles.minimumEntropy_le
      (outputs := T.switch.outputs) ⟨labelledState false ρ, T.switch_output_false ρ⟩
  · unfold minimumEntropy
    apply le_csInf (T.switch.outputs_nonempty.image _)
    rintro _ ⟨σ, ⟨ρ, rfl⟩, rfl⟩
    apply T.switch_output_entropy_lower
    intro τ
    exact StateEnsembles.minimumEntropy_le (outputs := T.outputs) ⟨τ, rfl⟩

/-- The concrete switch followed by a concrete Weyl extension has the exact
Holevo/minimum-output-entropy relation used in the manuscript. -/
theorem switch_weylExtension_holevo {d : ℕ} [NeZero d] [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) :
    T.switch.weylExtension.holevo = Real.log d - T.minimumEntropy := by
  rw [weylExtension_holevo, switch_minimumEntropy]

end Nonadditivity.Channels.KrausChannel
