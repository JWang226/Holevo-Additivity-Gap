/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalHolevoConverse
import Nonadditivity.OperationalFlaggedEntropy

/-! # Orthogonal comparison ensemble of an actual POVM decoder -/

noncomputable section

namespace Nonadditivity.Operational

open Entropy Channels OperationalFlaggedEntropy
open scoped BigOperators ComplexOrder

namespace POVM

variable {ο μ : Type*} [Fintype ο] [DecidableEq ο] [Nonempty ο]
  [Fintype μ] [DecidableEq μ]

/-- The normalized successful output in its actual orthogonal label block.
The zero-probability fallback is a genuine state in the same label block. -/
def projectedState (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) : DensityMatrix (μ × ο) :=
  flag m (P.normalizedBlockState ρ m)

/-- The comparison state is exactly the normalized projection of the
Naimark state, whenever the probability is nonzero; this identity also
holds at zero probability after multiplication by that probability. -/
theorem probability_smul_projectedState (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    (P.probability ρ m : ℂ) • (P.projectedState ρ m).matrix =
      labelProjection m * (P.dilate ρ).matrix * labelProjection m := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [Matrix.smul_apply, smul_eq_mul, projectedState, flag_matrix_apply,
    labelProjection_compress_apply]
  by_cases h : a = m ∧ b = m
  · obtain ⟨ha, hb⟩ := h
    subst a
    subst b
    simp only [and_self, ite_true]
    have he := congrArg (fun A : Matrix ο ο ℂ => A i j)
      (P.probability_smul_normalizedBlockState ρ m)
    exact he
  · simp [h]

theorem projectedState_matrix_of_pos (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ)
    (h : 0 < P.probability ρ m) :
    (P.projectedState ρ m).matrix = ((P.probability ρ m)⁻¹ : ℂ) •
      (labelProjection m * (P.dilate ρ).matrix * labelProjection m) := by
  rw [← P.probability_smul_projectedState, smul_smul]
  simp [h.ne']

end POVM

theorem shannon_uniformWeight {M : ℕ} (hM : 0 < M) :
    shannon (uniformWeight M) = Real.log M := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  simp only [shannon, uniformWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  simp [one_div, Real.log_inv]

/-- The orthogonal comparison ensemble carries exactly `log M` nats.
The conditional states may be arbitrary, mixed, or zero-probability
fallbacks. -/
theorem uniformInformation_flags {ο : Type*} [Fintype ο] [DecidableEq ο]
    {M : ℕ} (hM : 0 < M) (ρ : Fin M → DensityMatrix ο) :
    uniformInformation hM (fun m => flag m (ρ m)) = Real.log M := by
  have ha := flaggedState_entropy (uniformWeight M) (uniformWeight_nonneg M)
    (uniformWeight_sum hM) ρ
  change (uniformAverage hM (fun m => flag m (ρ m))).vonNeumann = _ at ha
  unfold uniformInformation
  rw [ha, shannon_uniformWeight hM]
  simp only [flag_entropy]
  have hs : (∑ m, uniformWeight M m * (ρ m).vonNeumann) =
      (∑ m, (ρ m).vonNeumann) / M := by
    simp only [uniformWeight, ← Finset.mul_sum, div_eq_mul_inv]
    ring
  rw [hs]
  ring

end Nonadditivity.Operational
