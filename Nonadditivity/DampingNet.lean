/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DampedChannel
import Nonadditivity.FiniteRealization
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite observable tests and the elementary moment choice for deterministic damping. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.DampingNet
open Channels Channels.KrausChannel AdjointPurity FiniteRealization
open Filter Topology
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- A fixed finite number of normalized even moments can be made arbitrarily small. -/
theorem exists_even_moment_small {r η : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (M : ℕ) (hη : 0 < η) :
    ∃ p : ℕ, 1 ≤ p ∧ 2 * (M : ℝ) * r ^ (2*p) < η := by
  have hr2 : r^2 < 1 := by nlinarith
  have ht : Tendsto (fun p : ℕ => 2 * (M : ℝ) * (r^2)^p) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg r) hr2).const_mul
      (2 * (M : ℝ))
  have hs : ∀ᶠ p : ℕ in atTop, 2 * (M : ℝ) * (r^2)^p < η :=
    ht.eventually (gt_mem_nhds hη)
  obtain ⟨p, hp, hsmall⟩ := ((eventually_ge_atTop 1).and hs).exists
  exact ⟨p, hp, by simpa only [pow_mul] using hsmall⟩

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- Compression bounds on a finite net give the full actual damped-channel certificate. -/
theorem damped_certificate (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef)
    {tests : Finset (ObservableSpace ο)} {a c : ℝ}
    (ha : 1 < a) (hc : 0 ≤ c)
    (hnet : UnitSphereNet tests ((a-1)/(a+1)))
    (htests : ∀ y ∈ tests,
      ‖F * T.adjointMap (observableMatrix y) * F‖ ≤ (1+(a-1)/(a+1))*c) :
    ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 →
      ‖(DampedChannel.damped T F hF hres).adjointMap A‖ ≤ a*c*hsLength A := by
  apply matrix_certificate_of_observable_bound
  apply kappa_net_certificate _ ha hc hnet
  intro y hy
  change ‖(DampedChannel.damped T F hF hres).adjointMap (observableMatrix y)‖ ≤ _
  rw [DampedChannel.damped_adjointMap_traceless _ _ _ _ _
    (observableMatrix_trace_zero y)]
  exact htests y hy

end Nonadditivity.DampingNet
