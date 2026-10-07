/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.BlockScalars
import Nonadditivity.FiniteChannelRealization
import Nonadditivity.FreeBridge

/-! # Qualitative realization by actual finite quantum channels

All Bell, entropy, finite-net, switch, and Weyl steps are proved. The
remaining premises are an upper bound on the limiting observable norm and
convergence in probability of the concrete finite block adjoints. There is
no assumed finite-matrix norm certificate or assumed Holevo inequality.

The entropies and Holevo quantities in this module use natural logarithms.
-/

noncomputable section

namespace Nonadditivity.Qualitative

open Entropy Channels Channels.KrausChannel AdjointPurity
open BlockConstruction Conversion BlockScalars
open scoped Matrix.Norms.L2Operator

variable {K : ℕ} [NeZero K]

/-- The exact input dimension of the constructed channel, before any
quantitative choice of the local matrix dimension is made. -/
theorem constructed_input_dimension (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype.card ((ZMod (K ^ n) × ZMod (K ^ n)) × (Bool × TensorChainIndex ι n)) =
      2 * Fintype.card ι ^ n * K ^ (2 * n) := by
  simp only [Fintype.card_prod, ZMod.card, Fintype.card_bool, tensorChainIndex_card]
  rw [show 2 * n = n * 2 by omega, pow_mul]
  ring

/-- The actual constructed output space has exactly dimension `K^n`. -/
theorem constructed_output_dimension (n : ℕ) : Fintype.card (ZMod (K ^ n)) = K ^ n :=
  ZMod.card _

/-- The qualitative channel-existence proposition, conditional only on its
specified pointwise limiting-norm estimate and probabilistic approximation.
The channels appearing in the conclusions are the actual constructed CPTP maps. -/
theorem eventually_exists_block_channels
    (n : ℕ) (hK : 2 ≤ K) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {D : ν → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (μ : (i : ν) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (U : (i : ν) → Ω i → ℕ → Fin K → unitary (Matrix (D i) (D i) ℂ))
    (l : Filter ν) (limitNorm : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ → ℝ)
    (hlimit : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      limitNorm A ≤ collinsYounConstant K n)
    (hconvergence : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      ∀ δ : ℝ, 0 < δ → Filter.Tendsto
      (fun i => μ i {ω | δ ≤ |‖(blockChannel (U i ω) n).adjointMap A‖ - limitNorm A|})
        l (nhds 0)) :
    Filter.Eventually (fun i => ∃ ω,
      (converted (blockChannel (U i ω) n)).holevo ≤
        (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + ε ∧
      (n : ℝ) * Real.log K / (K : ℝ) ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevo ∧
      (n : ℝ) * gapCoefficient K - 2 * ε ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevo -
            2 * (converted (blockChannel (U i ω) n)).holevo) l := by
  have hcert := FiniteRealization.eventually_exists_kraus_certificate
    μ (fun i ω => blockChannel (U i ω) n) l limitNorm
    (amplification_gt_one hε) (collinsYounConstant_pos hK hn) hlimit hconvergence
  apply hcert.mono
  rintro i ⟨ω, hω⟩
  have h := block_converted_bounds_of_certificate (U i ω) n
    (amplification_times_constant_pos (η := ε) hK hn).le hω
  have hsmall := h.1.trans (log_purity_factor_le_eta hK hε)
  refine ⟨ω, hsmall, h.2.1, ?_⟩
  exact gap_of_converted_bounds hsmall h.2.1

/-- The eventual statement gives an actual finite witness on every nontrivial
filter; a vacuous bottom-filter convergence cannot produce this conclusion. -/
theorem exists_block_channels
    (n : ℕ) (hK : 2 ≤ K) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {D : ν → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (μ : (i : ν) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (U : (i : ν) → Ω i → ℕ → Fin K → unitary (Matrix (D i) (D i) ℂ))
    (l : Filter ν) [l.NeBot]
    (limitNorm : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ → ℝ)
    (hlimit : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      limitNorm A ≤ collinsYounConstant K n)
    (hconvergence : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      ∀ δ : ℝ, 0 < δ → Filter.Tendsto
      (fun i => μ i {ω | δ ≤ |‖(blockChannel (U i ω) n).adjointMap A‖ - limitNorm A|})
        l (nhds 0)) :
    ∃ i ω,
      (converted (blockChannel (U i ω) n)).holevo ≤
        (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + ε ∧
      (n : ℝ) * Real.log K / (K : ℝ) ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevo ∧
      (n : ℝ) * gapCoefficient K - 2 * ε ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevo -
            2 * (converted (blockChannel (U i ω) n)).holevo :=
  (eventually_exists_block_channels n hK hn hε μ U l limitNorm hlimit hconvergence).exists

/-- The qualitative realization with the exact free-group comparison model.
The only analytic premises are the explicit Collins--Youn bound and
pointwise strong convergence in probability for the sampled block adjoints.
Every state, channel, entropy, ensemble and conversion in the conclusion is
concrete; no finite realization or entropy inequality is assumed. -/
theorem qualitative_realization_of_CY_and_strong_convergence
    (n : ℕ) (hK : 2 ≤ K) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {D : ν → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (μ : (i : ν) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (U : (i : ν) → Ω i → ℕ → Fin K → unitary (Matrix (D i) (D i) ℂ))
    (l : Filter ν) [l.NeBot]
    (hCY : FreeModel.CollinsYounBound K n)
    (hBC : ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
      A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      ∀ δ : ℝ, 0 < δ → Filter.Tendsto
      (fun i => μ i {ω | δ ≤
        |‖(blockChannel (U i ω) n).adjointMap A‖ - FreeBridge.outputFreeNorm K n A|})
        l (nhds 0)) :
    ∃ i ω,
      (converted (blockChannel (U i ω) n)).holevo ≤
        (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + ε ∧
      (n : ℝ) * Real.log K / (K : ℝ) ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevo ∧
      (n : ℝ) * gapCoefficient K - 2 * ε ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevo -
            2 * (converted (blockChannel (U i ω) n)).holevo := by
  apply exists_block_channels n hK hn hε μ U l (FreeBridge.outputFreeNorm K n)
  · exact FreeBridge.outputFreeNorm_unit_bound hCY
  · exact hBC

end Nonadditivity.Qualitative
