/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularizedHolevo
import Nonadditivity.HolevoTensorSuperadditivity

/-! # Actual finite tensor powers of unitary families and control registers -/

noncomputable section

namespace Nonadditivity.WeylPowers

open Entropy Channels Channels.KrausChannel RegularizedHolevo
open scoped Kronecker Matrix

universe u v

/-- Regroup the control and quantum coordinates of a positive tensor block. -/
def positivePairEquiv (ι : Type u) (μ : Type v) : (n : ℕ) →
    PositiveTensorIndex (ι × μ) n ≃ PositiveTensorIndex ι n × PositiveTensorIndex μ n
  | 0 => Equiv.refl _
  | n + 1 => ((positivePairEquiv ι μ n).prodCongr (Equiv.refl (ι × μ))).trans
      (Equiv.prodProdProdComm _ _ _ _)

@[simp] theorem positivePairEquiv_succ_apply (ι : Type u) (μ : Type v) (n : ℕ)
    (a : PositiveTensorIndex (ι × μ) n) (i : ι) (j : μ) :
    positivePairEquiv ι μ (n + 1) (a, (i,j)) =
      (((positivePairEquiv ι μ n a).1, i), ((positivePairEquiv ι μ n a).2, j)) := rfl

@[simp] theorem positivePairEquiv_succ_symm_apply (ι : Type u) (μ : Type v) (n : ℕ)
    (a : PositiveTensorIndex ι n) (b : PositiveTensorIndex μ n) (i : ι) (j : μ) :
    (positivePairEquiv ι μ (n + 1)).symm ((a,i),(b,j)) =
      ((positivePairEquiv ι μ n).symm (a,b), (i,j)) := rfl

/-- The actual independent local unitary conjugations on every positive number of uses. -/
def positiveUnitaryPower {ζ ο : Type*} [Fintype ο] [DecidableEq ο]
    (U : ζ → unitary (Matrix ο ο ℂ)) : (n : ℕ) →
    PositiveTensorIndex ζ n → unitary
      (Matrix (PositiveTensorIndex ο n) (PositiveTensorIndex ο n) ℂ)
  | 0 => U
  | n + 1 => fun z => tensorUnitary (positiveUnitaryPower U n z.1) (U z.2)

end Nonadditivity.WeylPowers
