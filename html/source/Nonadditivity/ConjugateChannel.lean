/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Channels
import Nonadditivity.StateEnsembles

/-!
# Conjugate channels and minimum output entropy

The conjugate input operation is a proved involution on actual density
matrices. Conjugate channels have identical output entropy ranges, so their
minimum output entropies agree. No entropy-preservation condition is assumed.
-/

noncomputable section

namespace Nonadditivity.Entropy

open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a Hermitian state, transpose equals entrywise conjugation. -/
theorem DensityMatrix.conjugate_matrix_eq_map_star (ρ : DensityMatrix ι) :
    ρ.conjugate.matrix = ρ.matrix.map star := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M j i) ρ.positive.isHermitian.eq
  simpa [DensityMatrix.conjugate, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.star_apply] using h.symm

@[simp] theorem DensityMatrix.conjugate_conjugate (ρ : DensityMatrix ι) :
    ρ.conjugate.conjugate = ρ := by
  apply DensityMatrix.ext
  simp [DensityMatrix.conjugate]

end Nonadditivity.Entropy

namespace Nonadditivity.Channels.KrausChannel

open scoped Matrix ComplexOrder
open Nonadditivity.Entropy

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype ο] [DecidableEq ο] [Fintype κ]

omit [DecidableEq ο] in
@[ext] theorem ext {T S : KrausChannel ι ο κ} (h : T.kraus = S.kraus) : T = S := by
  cases T
  cases S
  cases h
  rfl

omit [DecidableEq ο] in
@[simp] theorem conjugate_conjugate (T : KrausChannel ι ο κ) :
    T.conjugate.conjugate = T := by
  apply ext
  funext k
  ext i j
  simp [conjugate, Matrix.map_apply]

/-- The concrete conjugate-channel map acts on actual conjugate states. -/
@[simp] theorem conjugate_output (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    T.conjugate.output ρ.conjugate = (T.output ρ).conjugate := by
  apply DensityMatrix.ext
  rw [output_matrix, ρ.conjugate_matrix_eq_map_star, conjugate_map,
    (T.output ρ).conjugate_matrix_eq_map_star, output_matrix]

/-- The conjugate channel and original channel have equal entropy on
corresponding conjugate inputs. -/
@[simp] theorem conjugate_output_entropy (T : KrausChannel ι ο κ)
    (ρ : DensityMatrix ι) :
    (T.conjugate.output ρ.conjugate).vonNeumann = (T.output ρ).vonNeumann := by
  rw [conjugate_output, DensityMatrix.conjugate_entropy]

/-- Every input of the conjugate channel corresponds to a conjugate input
of the original channel; conjugation is surjective rather than an assumption. -/
theorem conjugate_output_entropy_all (T : KrausChannel ι ο κ)
    (ρ : DensityMatrix ι) :
    (T.conjugate.output ρ).vonNeumann = (T.output ρ.conjugate).vonNeumann := by
  simpa only [DensityMatrix.conjugate_conjugate] using
    conjugate_output_entropy T ρ.conjugate

/-- Any uniform output entropy lower bound transfers to the conjugate channel. -/
theorem output_entropy_lower_bound_conjugate (T : KrausChannel ι ο κ) (s : ℝ) :
    (∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann) ↔
      (∀ ρ : DensityMatrix ι, s ≤ (T.conjugate.output ρ).vonNeumann) := by
  constructor
  · intro h ρ
    rw [conjugate_output_entropy_all]
    exact h ρ.conjugate
  · intro h ρ
    have hh := h ρ.conjugate
    simpa only [conjugate_output_entropy] using hh

/-- Equality of the actual sets of attainable output entropy values. -/
theorem output_entropy_range_conjugate (T : KrausChannel ι ο κ) :
    Set.range (fun ρ : DensityMatrix ι => (T.conjugate.output ρ).vonNeumann) =
      Set.range (fun ρ : DensityMatrix ι => (T.output ρ).vonNeumann) := by
  ext s
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ.conjugate, (conjugate_output_entropy_all T ρ).symm⟩
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ.conjugate, conjugate_output_entropy T ρ⟩

/-- Conjugate concrete channels have the same minimum output entropy. -/
theorem minimumEntropy_conjugate (T : KrausChannel ι ο κ) :
    Nonadditivity.StateEnsembles.minimumEntropy (Set.range T.conjugate.output) =
      Nonadditivity.StateEnsembles.minimumEntropy (Set.range T.output) := by
  simp only [Nonadditivity.StateEnsembles.minimumEntropy, ← Set.range_comp']
  rw [output_entropy_range_conjugate]

end Nonadditivity.Channels.KrausChannel
