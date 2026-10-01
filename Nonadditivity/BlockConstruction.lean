/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.BlockBell
import Nonadditivity.Conversion
import Mathlib.Data.Fintype.EquivFin

/-!
# The concrete block channel with standard output coordinates

The tensor block is made from the complementary channels of the actual
uniform random-unitary families. Its output basis alone is relabelled to
`ZMod (K^n)`, with the dimension equality proved here. The Bell witness is
transported from the checked block construction, not supplied as a premise.
-/

noncomputable section

namespace Nonadditivity

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

namespace Entropy

/-- The empty block has dimension one; each tensor step multiplies dimension. -/
theorem tensorChainIndex_card (ι : Type*) [Fintype ι] (n : ℕ) :
    Fintype.card (TensorChainIndex ι n) = Fintype.card ι ^ n := by
  induction n with
  | zero => simp [TensorChainIndex]
  | succ n ih =>
    change Fintype.card (TensorChainIndex ι n × ι) = _
    simp [ih, pow_succ]

/-- Every finite tensor block of a nonempty index type is nonempty. -/
instance tensorChainIndexNonempty (ι : Type*) [Nonempty ι] :
    (n : ℕ) → Nonempty (TensorChainIndex ι n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n + 1 => by
    change Nonempty (TensorChainIndex ι n × ι)
    letI := tensorChainIndexNonempty ι n
    infer_instance

@[simp] theorem DensityMatrix.reindex_refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ρ.reindex (Equiv.refl ι) = ρ := by
  apply DensityMatrix.ext
  rfl

end Entropy

namespace Channels.KrausChannel

open Entropy

variable {ι ο κ μ ν η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]

omit [DecidableEq ο] in
/-- Relabeling matrix entries commutes with entrywise complex conjugation. -/
theorem reindex_conjugate_eq [Fintype μ] [DecidableEq μ] [Fintype ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    (T.reindex ei eo).conjugate = T.conjugate.reindex ei eo := by
  apply ext
  funext k
  ext a b
  rfl

omit [DecidableEq ο] in
/-- Relabeling the two tensor factors is relabeling by the product equivalence. -/
theorem reindex_tensor_eq [Fintype μ] [DecidableEq μ] [Fintype ν] [Fintype η]
    {ι' ο' μ' ν' : Type*}
    [Fintype ι'] [DecidableEq ι'] [Fintype ο']
    [Fintype μ'] [DecidableEq μ'] [Fintype ν']
    (T : Channels.KrausChannel ι ο κ) (S : Channels.KrausChannel μ ν η)
    (ei : ι ≃ ι') (eo : ο ≃ ο') (em : μ ≃ μ') (en : ν ≃ ν') :
    (T.reindex ei eo).tensor (S.reindex em en) =
      (T.tensor S).reindex (ei.prodCongr em) (eo.prodCongr en) := by
  apply ext
  funext k
  ext a b
  rfl

/-- Relabel the actual output state together with the actual channel. -/
theorem reindex_output_eq [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) (ρ : DensityMatrix ι) :
    (T.reindex ei eo).output (ρ.reindex ei) = (T.output ρ).reindex eo := by
  apply DensityMatrix.ext
  exact T.reindex_map ei eo ρ.matrix

/-- A common output-basis relabeling preserves the entropy of any original/conjugate
joint output, including entangled inputs. -/
theorem reindex_tensor_conjugate_entropy [Fintype ν] [DecidableEq ν]
    (T : Channels.KrausChannel ι ο κ) (e : ο ≃ ν) (ρ : DensityMatrix (ι × ι)) :
    (((T.reindex (Equiv.refl ι) e).tensor
      (T.reindex (Equiv.refl ι) e).conjugate).output ρ).vonNeumann =
      ((T.tensor T.conjugate).output ρ).vonNeumann := by
  have hi : (Equiv.refl ι).prodCongr (Equiv.refl ι) = Equiv.refl (ι × ι) := by
    ext a <;> rfl
  rw [reindex_conjugate_eq, reindex_tensor_eq, hi]
  have ho := reindex_output_eq (T.tensor T.conjugate) (Equiv.refl (ι × ι)) (e.prodCongr e) ρ
  rw [DensityMatrix.reindex_refl] at ho
  rw [ho, DensityMatrix.reindex_entropy]

end Channels.KrausChannel

namespace BlockConstruction

open Entropy Channels Channels.KrausChannel Conversion
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : ℕ} [NeZero K]

/-- A basis equivalence justified by the actual block's dimension count. -/
def blockOutputEquiv (K n : ℕ) [NeZero K] :
    TensorChainIndex (Fin K) n ≃ ZMod (K ^ n) :=
  Fintype.equivOfCardEq (by simp [tensorChainIndex_card])

/-- The actual tensor block, with the standard `K^n`-dimensional output basis. -/
def blockChannel (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    KrausChannel (TensorChainIndex ι n) (ZMod (K ^ n)) (TensorChainIndex ι n) :=
  (BlockBell.blockComplementary U n).reindex (Equiv.refl _) (blockOutputEquiv K n)

omit [DecidableEq ι] in
/-- The base block has precisely the manuscript's input dimension. -/
theorem blockChannel_input_dimension (n : ℕ) :
    Fintype.card (TensorChainIndex ι n) = Fintype.card ι ^ n := tensorChainIndex_card ι n

/-- The base block has precisely the manuscript's output dimension. -/
theorem blockChannel_output_dimension (n : ℕ) : Fintype.card (ZMod (K ^ n)) = K ^ n :=
  ZMod.card _

/-- The explicit block Bell witness survives output-basis standardization.
There is no joint-output entropy assumption in this theorem. -/
theorem block_channel_bell_entropy_le [Nonempty ι]
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ) :
    ∃ ρ : DensityMatrix (TensorChainIndex ι n × TensorChainIndex ι n),
      (((blockChannel U n).tensor (blockChannel U n).conjugate).output ρ).vonNeumann ≤
        (n : ℝ) * (2 * Real.log K - Real.log K / (K : ℝ)) := by
  obtain ⟨ρ,hρ⟩ := BlockBell.block_complementary_bell_entropy_le U n
  refine ⟨ρ, ?_⟩
  unfold blockChannel
  rw [reindex_tensor_conjugate_entropy]
  simpa only [Fintype.card_fin] using hρ

/-- Actual block channels followed by the checked switch and Weyl extension
satisfy the Holevo estimates from a base adjoint norm certificate alone.
The entangled Bell witness and all channel/entropy conversions are proved. -/
theorem block_converted_bounds_of_certificate [Nonempty ι]
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
      A.IsHermitian → A.trace = 0 → ‖(blockChannel U n).adjointMap A‖ ≤ t * AdjointPurity.hsLength A) :
    (converted (blockChannel U n)).holevo ≤ Real.log (1 + (K ^ n : ℝ) * t ^ 2) ∧
    (n : ℝ) * Real.log K / (K : ℝ) ≤
      ((converted (blockChannel U n)).tensor (converted (blockChannel U n))).holevo ∧
    (n : ℝ) * Real.log K / (K : ℝ) - 2 * Real.log (1 + (K ^ n : ℝ) * t ^ 2) ≤
      ((converted (blockChannel U n)).tensor (converted (blockChannel U n))).holevo -
        2 * (converted (blockChannel U n)).holevo := by
  obtain ⟨ρ,hρ⟩ := block_channel_bell_entropy_le U n
  have h := converted_bounds_of_certificate (blockChannel U n) ht hcertificate ρ hρ
  have hl : Real.log ((K ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log K := by
    rw [Nat.cast_pow, Real.log_pow]
  simp only [Nat.cast_pow] at h hl
  have hs : 2 * ((n : ℝ) * Real.log K) -
      (n : ℝ) * (2 * Real.log K - Real.log K / (K : ℝ)) =
      (n : ℝ) * Real.log K / (K : ℝ) := by ring
  rw [hl, hs] at h
  exact h

end BlockConstruction
end Nonadditivity
