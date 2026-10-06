/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.InitialNetReduction

/-! # From the actual paired net polynomial to the actual block channel

The branch and standardized output indices are explicitly transported. A finite
polynomial norm bound therefore gives the concrete adjoint certificate used by
the entropy and channel-conversion theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

namespace Nonadditivity.StructuredFiniteChannel
open Entropy Channels Channels.KrausChannel FreeModel FreeBridge FiniteRealization
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K n : ℕ} [NeZero K]

/-- An observable in branch coordinates, expressed in the output basis of the
concrete block channel. -/
def outputMatrix (A : Matrix (Branch K n) (Branch K n) ℂ) :
    Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ :=
  A.submatrix (branchToOutput K n).symm (branchToOutput K n).symm

@[simp] theorem branchToOutput_symm_output (a : TensorChainIndex (Fin K) n) :
    (branchToOutput K n).symm (BlockConstruction.blockOutputEquiv K n a) =
      chainBranchEquiv K n a := by
  apply (branchToOutput K n).injective
  simp

/-- The exact matrix identity, including the factor `1/K^n` and the orientation
`U_aᴴ U_b`, after conversion from nested tensor indices to branch tuples. -/
theorem block_adjoint_eq_branch_polynomial
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    (BlockConstruction.blockChannel U n).adjointMap (outputMatrix A) =
      ∑ a : Branch K n, ∑ b : Branch K n,
        ((Fintype.card (Branch K n) : ℂ)⁻¹ * A a b) •
          ((tensorWord U n ((chainBranchEquiv K n).symm a)).conjTranspose *
            tensorWord U n ((chainBranchEquiv K n).symm b)) := by
  rw [blockChannel_adjoint_eq_tensor_polynomial]
  simp only [Finset.smul_sum, smul_smul]
  apply Fintype.sum_equiv (chainBranchEquiv K n)
  intro a
  apply Fintype.sum_equiv (chainBranchEquiv K n)
  intro b
  simp [outputMatrix, Branch, one_div]

section Families
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The literal polynomial norm is the maximum of actual channel adjoint norms.
The word-evaluation premise is purely algebraic and is supplied by the concrete
tensor representation. -/
theorem finitePaired_norm_eq_block_adjoints
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (W : Branch K n → unitary (Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ))
    (hW : ∀ b, (W b : Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ) =
      tensorWord U n ((chainBranchEquiv K n).symm b))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) :
    ‖InitialNetReduction.finitePaired W A‖ =
      ‖fun j => (BlockConstruction.blockChannel U n).adjointMap (outputMatrix (A j))‖ := by
  rw [InitialNetReduction.finitePaired_norm]
  congr 1
  funext j
  rw [block_adjoint_eq_branch_polynomial]
  simp only [hW]

end Families

section Certificates
local instance (tests : Finset (ObservableSpace (Branch K n))) : DecidableEq tests := Classical.decEq _

/-- A verified norm bound on the combined net polynomial gives a uniform
Hilbert--Schmidt to operator-norm certificate for the actual block channel. -/
theorem certificate_of_finitePaired_bound
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (W : Branch K n → unitary (Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ))
    (hW : ∀ b, (W b : Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ) =
      tensorWord U n ((chainBranchEquiv K n).symm b))
    (tests : Finset (ObservableSpace (Branch K n)))
    (δ C : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    (hnet : UnitSphereNet tests δ)
    (hbound : ‖InitialNetReduction.finitePaired W (fun j : tests => observableMatrix j.val)‖ ≤ C) :
    ∀ A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ, A.IsHermitian → A.trace = 0 →
      ‖(BlockConstruction.blockChannel U n).adjointMap A‖ ≤
        (C / (1-δ)) * AdjointPurity.hsLength A := by
  classical
  let T := (BlockConstruction.blockChannel U n).reindex
    (Equiv.refl (TensorChainIndex ι n)) (branchToOutput K n).symm
  have hnorm : ‖fun j : tests => (BlockConstruction.blockChannel U n).adjointMap
      (outputMatrix (observableMatrix j.val))‖ ≤ C := by
    rw [← finitePaired_norm_eq_block_adjoints U W hW]
    exact hbound
  have htest : ∀ x ∈ tests, ‖adjointOnObservables T x‖ ≤ C := by
    intro x hx
    have hh := (norm_le_pi_norm (fun j : tests => (BlockConstruction.blockChannel U n).adjointMap
      (outputMatrix (observableMatrix j.val))) ⟨x,hx⟩).trans hnorm
    change ‖T.adjointMap (observableMatrix x)‖ ≤ C
    simpa only [T, reindex_output_adjointMap, outputMatrix] using hh
  have hall := matrix_certificate_of_observable_bound T (C/(1-δ)) (fun x =>
    norm_apply_le_of_unitSphereNet (adjointOnObservables T) hδ hδ1 hC hnet htest x)
  intro A hA htrace
  have ht : (A.submatrix (branchToOutput K n) (branchToOutput K n)).trace = 0 := by
    rw [trace_submatrix_equiv, htrace]
  have hh := hall (A.submatrix (branchToOutput K n) (branchToOutput K n))
    (hA.submatrix _) ht
  dsimp only [T] at hh
  rw [reindex_output_adjointMap, hsLength_submatrix_equiv] at hh
  have he : (A.submatrix (branchToOutput K n) (branchToOutput K n)).submatrix
      (branchToOutput K n).symm (branchToOutput K n).symm = A := by
    ext a b
    simp
  rwa [he] at hh

end Certificates
end Nonadditivity.StructuredFiniteChannel
