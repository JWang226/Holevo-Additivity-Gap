/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Qualitative
import Nonadditivity.Scalar

/-!
# The actual channel bounds in the manuscript's base-two convention

The underlying Holevo information is defined on finite ensembles of genuine
quantum output states.  Division by the positive constant `log 2` converts
the proved natural-logarithm results without changing any channel or model.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

def holevoBits (T : KrausChannel ι ο κ) : ℝ := T.holevo / Real.log 2

@[simp] theorem holevoBits_def (T : KrausChannel ι ο κ) :
    T.holevoBits = T.holevo / Real.log 2 := rfl

theorem holevoBits_nonneg [Nonempty ι] [Nonempty ο] (T : KrausChannel ι ο κ) :
    0 ≤ T.holevoBits :=
  div_nonneg T.holevo_nonneg Scalar.log_two_pos.le

theorem holevoBits_gap (T : KrausChannel ι ο κ) :
    (T.tensor T).holevoBits - 2 * T.holevoBits =
      ((T.tensor T).holevo - 2 * T.holevo) / Real.log 2 := by
  dsimp [holevoBits]
  ring

end Nonadditivity.Channels.KrausChannel

namespace Nonadditivity.HolevoBits

open Entropy Channels Channels.KrausChannel AdjointPurity BlockConstruction Conversion Scalar
open scoped Matrix.Norms.L2Operator

theorem natural_upper_to_bits {K χ η : ℝ} (n : ℕ)
    (h : χ ≤ (n : ℝ) * Real.log (1 + 9 / K) + η * Real.log 2) :
    χ / Real.log 2 ≤ (n : ℝ) * aK K + η := by
  apply (div_le_iff₀ log_two_pos).mpr
  have he : ((n : ℝ) * aK K + η) * Real.log 2 =
      (n : ℝ) * Real.log (1 + 9 / K) + η * Real.log 2 := by
    dsimp [aK, log2]
    field_simp
  rw [he]
  exact h

theorem natural_lower_to_bits {K χ : ℝ} (n : ℕ)
    (h : (n : ℝ) * Real.log K / K ≤ χ) :
    (n : ℝ) * log2 K / K ≤ χ / Real.log 2 := by
  have hd := div_le_div_of_nonneg_right h log_two_pos.le
  convert hd using 1
  dsimp [log2]
  ring

variable {K : ℕ} [NeZero K]

/-- Actual finite channels with all three manuscript bounds in bits.
The only analytic premises are the pointwise limiting observable norm
bound and convergence in probability of the concrete finite block adjoint. -/
theorem exists_block_channels_bits
    (n : ℕ) (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η)
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
      (converted (blockChannel (U i ω) n)).holevoBits ≤ (n : ℝ) * aK K + η ∧
      (n : ℝ) * log2 K / (K : ℝ) ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevoBits ∧
      (n : ℝ) * deltaK K - 2 * η ≤
        ((converted (blockChannel (U i ω) n)).tensor
          (converted (blockChannel (U i ω) n))).holevoBits -
            2 * (converted (blockChannel (U i ω) n)).holevoBits := by
  have hε : 0 < η * Real.log 2 := mul_pos hη log_two_pos
  obtain ⟨i, ω, h₁, h₂, _⟩ := Qualitative.exists_block_channels n hK hn hε
    μ U l limitNorm hlimit hconvergence
  have hb₁ := natural_upper_to_bits n h₁
  have hb₂ := natural_lower_to_bits n h₂
  refine ⟨i, ω, hb₁, hb₂, ?_⟩
  have hb₂' : (n : ℝ) * (log2 K / (K : ℝ)) ≤
      ((converted (blockChannel (U i ω) n)).tensor
        (converted (blockChannel (U i ω) n))).holevoBits := by
    convert hb₂ using 1
    dsimp [holevoBits]
    ring
  exact Scalar.holevo_gap hb₁ hb₂'

end Nonadditivity.HolevoBits
