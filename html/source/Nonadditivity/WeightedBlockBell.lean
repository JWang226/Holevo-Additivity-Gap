/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeightedBlock
import Nonadditivity.WeightedBell

/-! The weighted block has a strict Bell entropy margin at the canonical input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.WeightedBlock
open Entropy Channels Channels.KrausChannel BlockConstruction BlockBell
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {K : ℕ} [NeZero K]

/-- Tensorization and output-basis transport preserve the strict weighted Bell budget. -/
theorem weightedBlock_canonical_entropy_le
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ) :
    (((weightedBlock U p hp hsum n).tensor (weightedBlock U p hp hsum n).conjugate).output
      (BellOutput.bellState (ι := TensorChainIndex ι n))).vonNeumann ≤
        (n:ℝ)*(2*Real.log K-(∑ a, p a^2)*Real.log K) := by
  unfold weightedBlock
  rw [reindex_tensor_conjugate_entropy,←CanonicalBlockBell.blockBellState_eq_canonical]
  let T (j : ℕ) := (randomUnitary p hp hsum (U j)).complementary
  have he := pairedTensorChain_output_entropy T (fun j => (T j).conjugate)
    (fun _ => BellOutput.bellState (ι := ι)) n
  rw [←tensorChain_conjugate T n] at he
  calc
    _ = ∑ j ∈ Finset.range n,
        (((T j).tensor (T j).conjugate).output (BellOutput.bellState (ι := ι))).vonNeumann := he
    _ ≤ ∑ j ∈ Finset.range n,
        (2*Real.log K-(∑ a, p a^2)*Real.log K) :=
      Finset.sum_le_sum (fun j _ => by
        simpa only [Fintype.card_fin] using WeightedBell.complementary_bell_entropy_le p hp hsum (U j))
    _ = _ := by simp; ring

alias weightedBlock_bell_entropy_le := weightedBlock_canonical_entropy_le

/-- The positive excess of the collision probability is an explicit entropy reserve. -/
theorem weightedBlock_canonical_entropy_le_with_margin
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ) :
    (((weightedBlock U p hp hsum n).tensor (weightedBlock U p hp hsum n).conjugate).output
      (BellOutput.bellState (ι := TensorChainIndex ι n))).vonNeumann ≤
        (n:ℝ)*(2*Real.log K-Real.log K/(K:ℝ)) -
          (n:ℝ)*((∑ a, p a^2)-1/(K:ℝ))*Real.log K := by
  convert weightedBlock_canonical_entropy_le U p hp hsum n using 1
  ring

end Nonadditivity.WeightedBlock
