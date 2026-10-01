/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FreeModel
import Nonadditivity.TensorPowers
import Nonadditivity.Net
import Nonadditivity.BlockConstruction
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact observable-basis transport for the product free model

The nested block labels are canonically converted into ordered branch tuples.
Trace, Hermitian symmetry, and Hilbert--Schmidt length are preserved by the
actual matrix reindexing. Thus the Collins--Youn hypothesis supplies the
finite-net comparison bound after output coordinates have been specified.
-/

noncomputable section

namespace Nonadditivity.FreeBridge

open Nonadditivity.Entropy Nonadditivity.AdjointPurity
open scoped BigOperators Matrix

universe u

/-- The canonical ordered tuple associated with a recursively nested tensor label.
The last local tensor coordinate is the last coordinate of the finite tuple. -/
def chainTupleEquiv (α : Type u) : (n : ℕ) → TensorChainIndex α n ≃ (Fin n → α)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    { toFun := fun x => Fin.snoc (chainTupleEquiv α n x.1) x.2
      invFun := fun x => ((chainTupleEquiv α n).symm (Fin.init x), x (Fin.last n))
      left_inv := fun x => by rcases x with ⟨a,b⟩; simp
      right_inv := fun x => by simp [Fin.snoc_init_self] }

@[simp] theorem chainTupleEquiv_succ (α : Type u) (n : ℕ)
    (a : TensorChainIndex α n) (b : α) :
    chainTupleEquiv α (n + 1) (a,b) = Fin.snoc (chainTupleEquiv α n a) b := rfl

@[simp] theorem chainTupleEquiv_succ_symm (α : Type u) (n : ℕ) (a : Fin (n + 1) → α) :
    (chainTupleEquiv α (n + 1)).symm a =
      ((chainTupleEquiv α n).symm (Fin.init a), a (Fin.last n)) := rfl

def chainBranchEquiv (K n : ℕ) :
    TensorChainIndex (Fin K) n ≃ FreeModel.Branch K n := chainTupleEquiv (Fin K) n

section Reindex

variable {ι ο : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο]

omit [DecidableEq ι] [DecidableEq ο] in
/-- Trace is preserved by a bijective change of matrix basis labels. -/
theorem trace_submatrix_equiv (e : ι ≃ ο) (A : Matrix ο ο ℂ) :
    (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)

omit [DecidableEq ι] [DecidableEq ο] in
/-- The matrix trace definition of Hilbert--Schmidt length is invariant under reindexing. -/
theorem hsLength_submatrix_equiv (e : ι ≃ ο) (A : Matrix ο ο ℂ) :
    hsLength (A.submatrix e e) = hsLength A := by
  unfold hsLength
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    trace_submatrix_equiv]

omit [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] in
/-- Hermitian observables stay Hermitian under the same concrete basis transport. -/
theorem isHermitian_submatrix_equiv (e : ι ≃ ο) (A : Matrix ο ο ℂ)
    (hA : A.IsHermitian) : (A.submatrix e e).IsHermitian := hA.submatrix e

end Reindex

section Comparison

variable {K n : ℕ} {ο : Type*} [Fintype ο] [DecidableEq ο]

/-- The actual free comparison norm after an explicitly specified output-basis relabeling. -/
def reindexedFreeNorm (e : FreeModel.Branch K n ≃ ο) (A : Matrix ο ο ℂ) : ℝ :=
  FreeModel.freeNorm (A.submatrix e e)

theorem freeConstant_eq : FreeModel.c K n = Nonadditivity.collinsYounConstant K n := rfl

omit [DecidableEq ο] in
/-- The exact unit-HS test bound needed by the finite-realization theorem.
Its sole analytic premise is the concrete Collins--Youn operator bound. -/
theorem reindexedFreeNorm_le (e : FreeModel.Branch K n ≃ ο)
    (hCY : FreeModel.CollinsYounBound K n) (A : Matrix ο ο ℂ)
    (htrace : A.trace = 0) (hunit : hsLength A = 1) :
    reindexedFreeNorm e A ≤ Nonadditivity.collinsYounConstant K n := by
  have ht : (A.submatrix e e).trace = 0 := (trace_submatrix_equiv e A).trans htrace
  have hu : hsLength (A.submatrix e e) = 1 := (hsLength_submatrix_equiv e A).trans hunit
  exact (FreeModel.freeNorm_le_of_collinsYoun hCY (A.submatrix e e) ht hu).trans_eq
    freeConstant_eq

end Comparison

section Block

variable {K n : ℕ} [NeZero K]

/-- Ordered free-generator branches in the very output coordinates used by
`BlockConstruction.blockChannel`. The tuple conversion fixes the order of
the local tensor legs before applying the block's output basis equivalence. -/
def branchToOutput (K n : ℕ) [NeZero K] :
    FreeModel.Branch K n ≃ ZMod (K ^ n) :=
  (chainBranchEquiv K n).symm.trans (BlockConstruction.blockOutputEquiv K n)

@[simp] theorem branchToOutput_chain (a : TensorChainIndex (Fin K) n) :
    branchToOutput K n (chainBranchEquiv K n a) =
      BlockConstruction.blockOutputEquiv K n a := by
  simp [branchToOutput]

/-- The exact infinite-dimensional free operator norm for an observable on
the output of the concrete block channel. -/
def outputFreeNorm (K n : ℕ) [NeZero K]
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) : ℝ :=
  reindexedFreeNorm (branchToOutput K n) A

theorem outputFreeNorm_nonneg
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    0 ≤ outputFreeNorm K n A := FreeModel.freeNorm_nonneg _

theorem outputObservable_trace
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    (A.submatrix (branchToOutput K n) (branchToOutput K n)).trace = A.trace :=
  trace_submatrix_equiv _ _

theorem outputObservable_hsLength
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    hsLength (A.submatrix (branchToOutput K n) (branchToOutput K n)) = hsLength A :=
  hsLength_submatrix_equiv _ _

theorem outputObservable_isHermitian
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) (hA : A.IsHermitian) :
    (A.submatrix (branchToOutput K n) (branchToOutput K n)).IsHermitian :=
  isHermitian_submatrix_equiv _ _ hA

/-- The published operator inequality, expressed on the output coordinates
of the actual block channel, supplies exactly the unit-HS bound needed by
finite realization. -/
theorem outputFreeNorm_le_of_collinsYoun
    (hCY : FreeModel.CollinsYounBound K n)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ)
    (htrace : A.trace = 0) (hunit : hsLength A = 1) :
    outputFreeNorm K n A ≤ Nonadditivity.collinsYounConstant K n :=
  reindexedFreeNorm_le (branchToOutput K n) hCY A htrace hunit

/-- The full finite-realization test predicate, including its Hermitian
condition, follows from Collins--Youn for this concrete free model. -/
theorem outputFreeNorm_unit_bound
    (hCY : FreeModel.CollinsYounBound K n) :
    ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
      A.IsHermitian → A.trace = 0 → hsLength A = 1 →
        outputFreeNorm K n A ≤ Nonadditivity.collinsYounConstant K n := by
  intro A _ htrace hunit
  exact outputFreeNorm_le_of_collinsYoun hCY A htrace hunit

end Block

end Nonadditivity.FreeBridge
