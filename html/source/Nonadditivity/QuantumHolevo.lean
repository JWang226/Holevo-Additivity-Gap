/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Channels
import Nonadditivity.StateEnsembles
import Nonadditivity.AdjointPurity

/-! # Holevo information of concrete Kraus channels

The quantity below is defined by all finite ensembles of actual channel
outputs. The adjoint certificate theorem supplies its entropy hypotheses
from the Kraus formula, without assuming trace duality or positivity.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity Entropy AdjointPurity
open scoped Matrix.Norms.L2Operator

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

def outputs (T : KrausChannel ι ο κ) : Set (DensityMatrix ο) := Set.range T.output

def minimumEntropy (T : KrausChannel ι ο κ) : ℝ :=
  StateEnsembles.minimumEntropy T.outputs

def holevo (T : KrausChannel ι ο κ) : ℝ := StateEnsembles.quantity T.outputs

theorem outputs_nonempty [Nonempty ι] (T : KrausChannel ι ο κ) : T.outputs.Nonempty :=
  ⟨T.output (maximallyMixed ι), maximallyMixed ι, rfl⟩

theorem holevo_nonneg [Nonempty ι] [Nonempty ο] (T : KrausChannel ι ο κ) :
    0 ≤ T.holevo := StateEnsembles.quantity_nonneg T.outputs_nonempty

theorem holevo_le_of_output_entropy [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann) :
    T.holevo ≤ Real.log (Fintype.card ο) - s := by
  apply StateEnsembles.quantity_le T.outputs_nonempty
  rintro _ ⟨ρ, rfl⟩
  exact hentropy ρ

theorem holevo_le_log_dim_sub_minimumEntropy [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) :
    T.holevo ≤ Real.log (Fintype.card ο) - T.minimumEntropy :=
  StateEnsembles.quantity_le_log_dim_sub_minimumEntropy T.outputs_nonempty

/-- A norm certificate for the concrete Kraus adjoint controls every output
purity and von Neumann entropy. All matrix duality conditions are discharged. -/
theorem output_purity_and_entropy_of_certificate [Nonempty ο]
    (T : KrausChannel ι ο κ) {t : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ t * hsLength A) (ρ : DensityMatrix ι) :
    (T.output ρ).purity ≤ 1 / (Fintype.card ο : ℝ) + t ^ 2 ∧
      Real.log (Fintype.card ο) - Real.log (1 + (Fintype.card ο : ℝ) * t ^ 2) ≤
        (T.output ρ).vonNeumann := by
  apply purity_and_entropy_of_adjoint_certificate ρ (T.output ρ)
    T.adjointLinearMap ht
  · exact T.adjointMap_isHermitian
  · intro A _ _
    exact T.trace_duality ρ.matrix A
  · exact hcertificate

/-- The actual single-use Holevo bound from an adjoint norm certificate. -/
theorem holevo_le_of_adjoint_certificate [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) {t : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ t * hsLength A) :
    T.holevo ≤ Real.log (1 + (Fintype.card ο : ℝ) * t ^ 2) := by
  have h := T.holevo_le_of_output_entropy
    (fun ρ => (T.output_purity_and_entropy_of_certificate ht hcertificate ρ).2)
  linarith

end Nonadditivity.Channels.KrausChannel
