/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalReindex
import Nonadditivity.OperationalCapacity
import Nonadditivity.HolevoRateLimit

/-! # Physical code padding and exact channel transport -/
noncomputable section
namespace Nonadditivity.Operational
open Entropy Channels RegularizedHolevo
open scoped BigOperators Matrix ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace POVM
variable {ι ο μ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype μ]

/-- Ignore the second output register of an actual product channel. -/
def ignoreRight (P : POVM ι μ) : POVM (ι × ο) μ where
  effect := fun m => P.effect m ⊗ₖ (1 : Matrix ο ο ℂ)
  positive := fun m => (P.positive m).kronecker Matrix.PosSemidef.one
  complete := by
    calc
      (∑m, P.effect m ⊗ₖ (1 : Matrix ο ο ℂ)) =
          (∑m, P.effect m) ⊗ₖ (1 : Matrix ο ο ℂ) := by
        ext a b
        simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
      _ = 1 := by rw [P.complete,Matrix.one_kronecker_one]

@[simp] theorem ignoreRight_probability (P : POVM ι μ)
    (ρ : DensityMatrix ι) (σ : DensityMatrix ο) (m : μ) :
    P.ignoreRight.probability (ρ.tensor σ) m = P.probability ρ m := by
  unfold probability ignoreRight
  rw [DensityMatrix.tensor_matrix, ←Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, σ.normalized, mul_one]

end POVM

namespace Code
variable {ι ο κ μ ν η ι' ο' κ' : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] [Fintype η]
  [Fintype ι'] [DecidableEq ι'] [Fintype ο'] [DecidableEq ο'] [Fintype κ']
  {T : KrausChannel ι ο κ} {M : ℕ}

/-- Append an independently prepared input and ignore its output. -/
def padRight (C : Code T M) (S : KrausChannel μ ν η) (σ : DensityMatrix μ) :
    Code (T.tensor S) M where
  encode := fun m => (C.encode m).tensor σ
  decode := C.decode.ignoreRight

@[simp] theorem padRight_success (C : Code T M) (S : KrausChannel μ ν η)
    (σ : DensityMatrix μ) : (C.padRight S σ).success=C.success := by
  have ho (m : Fin M) : (T.tensor S).output ((C.encode m).tensor σ) =
      (T.output (C.encode m)).tensor (S.output σ) := by
    apply Entropy.DensityMatrix.ext
    exact T.tensor_map S _ _
  unfold success padRight
  simp only [ho,POVM.ignoreRight_probability]

@[simp] theorem padRight_error (C : Code T M) (S : KrausChannel μ ν η)
    (σ : DensityMatrix μ) : (C.padRight S σ).error=C.error := by
  simp only [error,padRight_success]

/-- Transport a physical code along input/output basis changes whose channel
map identity has been proved independently. -/
def transport (C : Code T M) (S : KrausChannel ι' ο' κ')
    (ei : ι ≃ ι') (eo : ο ≃ ο') : Code S M where
  encode := fun m => (C.encode m).reindex ei
  decode := C.decode.reindex eo

theorem transport_success (C : Code T M) (S : KrausChannel ι' ο' κ')
    (ei : ι ≃ ι') (eo : ο ≃ ο')
    (hmap : ∀X, S.map (Matrix.reindex ei ei X)=Matrix.reindex eo eo (T.map X)) :
    (C.transport S ei eo).success=C.success := by
  have ho (m : Fin M) : S.output ((C.encode m).reindex ei) =
      (T.output (C.encode m)).reindex eo := by
    apply Entropy.DensityMatrix.ext
    exact hmap _
  unfold success transport
  simp only [ho,POVM.probability_reindex]

theorem transport_error (C : Code T M) (S : KrausChannel ι' ο' κ')
    (ei : ι ≃ ι') (eo : ο ≃ ο')
    (hmap : ∀X, S.map (Matrix.reindex ei ei X)=Matrix.reindex eo eo (T.map X)) :
    (C.transport S ei eo).error=C.error := by
  simp only [error,transport_success C S ei eo hmap]

variable [Nonempty ι]

/-- Append any number of unused channel inputs. -/
def pad (T : KrausChannel ι ο κ) {m : ℕ} (C : Code (positiveTensorPower T m) M) :
    (r : ℕ) → Code (positiveTensorPower T (m+r)) M
  | 0 => C
  | r+1 => (pad T C r).padRight T (maximallyMixed ι)

@[simp] theorem pad_error (T : KrausChannel ι ο κ) {m : ℕ}
    (C : Code (positiveTensorPower T m) M) (r : ℕ) : (pad T C r).error=C.error := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ((pad T C r).padRight T (maximallyMixed ι)).error=C.error
    exact (padRight_error (pad T C r) T (maximallyMixed ι)).trans ih

/-- A code at a shorter positive block length is a code at every longer length. -/
def padTo (T : KrausChannel ι ο κ) {m n : ℕ} (C : Code (positiveTensorPower T m) M)
    (h : m≤n) : Code (positiveTensorPower T n) M :=
  Nat.leRecOn (C := fun l => Code (positiveTensorPower T l) M) h
    (fun D => D.padRight T (maximallyMixed ι)) C

@[simp] theorem padTo_error (T : KrausChannel ι ο κ) {m n : ℕ}
    (C : Code (positiveTensorPower T m) M) (h : m≤n) : (padTo T C h).error=C.error := by
  induction h using Nat.leRec with
  | refl => simp only [padTo,Nat.leRecOn_self]
  | le_succ_of_le h ih =>
    unfold padTo
    rw [Nat.leRecOn_succ h]
    exact (padRight_error _ T (maximallyMixed ι)).trans ih

end Code
end Nonadditivity.Operational
