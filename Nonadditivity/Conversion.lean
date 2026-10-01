/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.SwitchChannel
import Nonadditivity.ChannelTensorControl
import Nonadditivity.WeylTensor

/-! # Concrete entropy-gap to Holevo-gap conversion

This file applies the checked switch and Weyl constructions to actual
Kraus channels. Its analytic norm-certificate premise remains explicit.
-/

noncomputable section

namespace Nonadditivity.Conversion

open Entropy Channels Channels.KrausChannel AdjointPurity
open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {d : ℕ} [NeZero d]

/-- The manuscript's switch followed by its `d²`-label Weyl extension. -/
def converted (T : KrausChannel ι (ZMod d) κ) := T.switch.weylExtension

theorem converted_holevo [Nonempty ι] (T : KrausChannel ι (ZMod d) κ) :
    (converted T).holevo = Real.log d - T.minimumEntropy :=
  T.switch_weylExtension_holevo

theorem converted_holevo_le_of_output_entropy [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann) :
    (converted T).holevo ≤ Real.log d - s := by
  rw [converted_holevo]
  have hmin : s ≤ T.minimumEntropy := by
    apply le_csInf (T.outputs_nonempty.image _)
    rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    exact hentropy ρ
  linarith

/-- A genuine finite-dimensional channel with the required small single-use
Holevo information, from an adjoint operator/HS certificate for its base. -/
theorem converted_holevo_le_of_adjoint_certificate [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) {t : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix (ZMod d) (ZMod d) ℂ,
      A.IsHermitian → A.trace = 0 → ‖T.adjointMap A‖ ≤ t * hsLength A) :
    (converted T).holevo ≤ Real.log (1 + (d : ℝ) * t ^ 2) := by
  have h := converted_holevo_le_of_output_entropy T
    (fun ρ => (T.output_purity_and_entropy_of_certificate ht hcertificate ρ).2)
  simp only [ZMod.card] at h
  linarith

omit [DecidableEq ι] in
/-- The final classical registers have exactly the claimed size `2d²`. -/
theorem converted_input_dimension :
    Fintype.card ((ZMod d × ZMod d) × (Bool × ι)) =
      2 * Fintype.card ι * d ^ 2 := by
  simp [pow_two]
  ring

/-- Independent Weyl labels turn any joint output into a real finite coding
ensemble, even when the underlying input is entangled. -/
theorem weyl_tensor_holevo_lower {μ η : Type*} [Fintype μ] [DecidableEq μ] [Fintype η]
    (T : KrausChannel ι (ZMod d) κ) (S : KrausChannel μ (ZMod d) η)
    (ρ : DensityMatrix (ι × μ)) :
    2 * Real.log d - ((T.tensor S).output ρ).vonNeumann ≤
      (T.weylExtension.tensor S.weylExtension).holevo := by
  apply WeylTensor.orbit_information_lower_bound
    (T.weylExtension.tensor S.weylExtension).outputs ((T.tensor S).output ρ)
  intro q r
  refine ⟨jointLabelledState q r ρ, ?_⟩
  change ((controlled (fun q => T.outputUnitary (Weyl.family q))).tensor
    (controlled (fun r => S.outputUnitary (Weyl.family r)))).output
      (jointLabelledState q r ρ) = _
  rw [controlled_tensor_output_labelled, tensor_outputUnitary_output]
  rfl

/-- The two switches reproduce the original/conjugate pair on an arbitrary
entangled input; independent Weyl ensembles then give the two-use lower bound. -/
theorem converted_tensor_holevo_lower (T : KrausChannel ι (ZMod d) κ)
    (ρ : DensityMatrix (ι × ι)) :
    2 * Real.log d - ((T.tensor T.conjugate).output ρ).vonNeumann ≤
      ((converted T).tensor (converted T)).holevo := by
  have h := weyl_tensor_holevo_lower T.switch T.switch (jointLabelledState false true ρ)
  have ho : (T.switch.tensor T.switch).output (jointLabelledState false true ρ) =
      (T.tensor T.conjugate).output ρ := by
    change ((controlled (fun b : Bool => if b then T.conjugate else T)).tensor
      (controlled (fun b : Bool => if b then T.conjugate else T))).output _ = _
    rw [controlled_tensor_output_labelled]
    rfl
  rw [ho] at h
  exact h

/-- A proved minimum-output entropy gap becomes a Holevo gap for a single
explicit CPTP channel, without assuming either Holevo estimate. -/
theorem converted_gap_lower [Nonempty ι] (T : KrausChannel ι (ZMod d) κ)
    (ρ : DensityMatrix (ι × ι)) :
    2 * T.minimumEntropy - ((T.tensor T.conjugate).output ρ).vonNeumann ≤
      ((converted T).tensor (converted T)).holevo - 2 * (converted T).holevo := by
  have h := converted_tensor_holevo_lower T ρ
  rw [converted_holevo]
  linarith

/-- The remaining premises are the base adjoint norm certificate and a joint
entropy witness. Positivity, all entropy inequalities, switch, and Weyl
conversion are proved internally. -/
theorem converted_bounds_of_certificate [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) {t B : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix (ZMod d) (ZMod d) ℂ,
      A.IsHermitian → A.trace = 0 → ‖T.adjointMap A‖ ≤ t * hsLength A)
    (ρ : DensityMatrix (ι × ι))
    (hjoint : ((T.tensor T.conjugate).output ρ).vonNeumann ≤ B) :
    (converted T).holevo ≤ Real.log (1 + (d : ℝ) * t ^ 2) ∧
    2 * Real.log d - B ≤ ((converted T).tensor (converted T)).holevo ∧
    2 * Real.log d - B - 2 * Real.log (1 + (d : ℝ) * t ^ 2) ≤
      ((converted T).tensor (converted T)).holevo - 2 * (converted T).holevo := by
  have h₁ := converted_holevo_le_of_adjoint_certificate T ht hcertificate
  have h₂ := converted_tensor_holevo_lower T ρ
  exact ⟨h₁, by linarith, by linarith⟩

end Nonadditivity.Conversion
