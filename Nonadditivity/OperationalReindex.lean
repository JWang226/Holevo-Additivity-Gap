/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalConverse
import Nonadditivity.ChannelReindex

/-! # Basis relabeling of physical quantum codes -/
noncomputable section
namespace Nonadditivity.Operational
open Entropy Channels
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false

namespace POVM
variable {ι ο μ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype μ]

def reindex (P : POVM ι μ) (e : ι ≃ ο) : POVM ο μ where
  effect := fun m => Matrix.reindex e e (P.effect m)
  positive := fun m => (P.positive m).submatrix e.symm
  complete := by
    ext i j
    have h := congrArg (fun A : Matrix ι ι ℂ => A (e.symm i) (e.symm j)) P.complete
    simpa [Matrix.sum_apply,Matrix.reindex_apply,Matrix.one_apply] using h

theorem probability_reindex (P : POVM ι μ) (e : ι ≃ ο)
    (ρ : DensityMatrix ι) (m : μ) :
    (P.reindex e).probability (ρ.reindex e) m = P.probability ρ m := by
  unfold probability reindex DensityMatrix.reindex
  simp only [Matrix.reindex_apply,Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (e.symm.sum_comp (fun j => (ρ.matrix*P.effect m) j j))

end POVM

namespace Code
variable {ι ο κ ι' ο' : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]
  [Fintype ι'] [DecidableEq ι'] [Fintype ο'] [DecidableEq ο']
  {T : KrausChannel ι ο κ} {M : ℕ}

def reindex (C : Code T M) (ei : ι ≃ ι') (eo : ο ≃ ο') :
    Code (T.reindex ei eo) M where
  encode := fun m => (C.encode m).reindex ei
  decode := C.decode.reindex eo

theorem reindex_success (C : Code T M) (ei : ι ≃ ι') (eo : ο ≃ ο') :
    (C.reindex ei eo).success = C.success := by
  unfold success reindex
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  change (C.decode.reindex eo).probability
    ((T.reindex ei eo).output ((C.encode m).reindex ei)) m = _
  have h : (T.reindex ei eo).output ((C.encode m).reindex ei) =
      (T.output (C.encode m)).reindex eo := by
    apply DensityMatrix.ext
    exact T.reindex_map ei eo (C.encode m).matrix
  rw [h,POVM.probability_reindex]

theorem reindex_error (C : Code T M) (ei : ι ≃ ι') (eo : ο ≃ ο') :
    (C.reindex ei eo).error = C.error := by
  simp only [error,reindex_success]

end Code
end Nonadditivity.Operational
