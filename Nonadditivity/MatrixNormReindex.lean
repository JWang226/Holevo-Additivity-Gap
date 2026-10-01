/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PositiveLinearization
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Euclidean operator norms under finite matrix reindexing -/

namespace Nonadditivity.MatrixNormReindex

open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- A basis permutation is an actual star-algebra equivalence. -/
def reindexStarAlgEquiv (e : ι ≃ κ) :
    Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := fun _ _ => rfl
    map_star' := fun _ => rfl }

/-- The Euclidean operator norm is invariant under any finite basis permutation. -/
theorem reindex_norm (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  letI : CStarAlgebra (Matrix κ κ ℂ) := { }
  exact NonUnitalStarAlgHom.norm_map (reindexStarAlgEquiv e)
    (reindexStarAlgEquiv e).injective A

theorem submatrix_equiv_norm (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    ‖A.submatrix e e‖ = ‖A‖ := reindex_norm e.symm A

end Nonadditivity.MatrixNormReindex
