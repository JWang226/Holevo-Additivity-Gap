/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.EntropyMixtures
import Nonadditivity.PureChannelEntropy
import Mathlib.Data.Matrix.Block

/-! # Entropy of actual classical-quantum flagged states

Flags occupy the first tensor coordinate. The entropy identity is proved by
constructing a block unitary diagonalization of the literal state matrix.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.OperationalFlaggedEntropy
open Entropy EntropyMixtures Channels
open scoped BigOperators ComplexOrder Matrix Kronecker
variable {μ ο : Type*} [Fintype μ] [DecidableEq μ] [Fintype ο] [DecidableEq ο]

def basisVector (m : μ) : μ → ℂ := fun a => if a=m then 1 else 0

theorem basisVector_normalized (m : μ) : ∑ a, Complex.normSq (basisVector m a) = 1 := by
  simp [basisVector]

def basisState (m : μ) : DensityMatrix μ := pureState (basisVector m) (basisVector_normalized m)

/-- A state embedded in the block carrying the actual classical label `m`. -/
def flag (m : μ) (ρ : DensityMatrix ο) : DensityMatrix (μ × ο) := (basisState m).tensor ρ

theorem flag_matrix_apply (m : μ) (ρ : DensityMatrix ο) (a b : μ) (i j : ο) :
    (flag m ρ).matrix (a,i) (b,j) = if a=m ∧ b=m then ρ.matrix i j else 0 := by
  by_cases ha : a=m <;> by_cases hb : b=m <;>
    simp [flag, DensityMatrix.tensor_matrix, basisState, pureState, basisVector,
      Matrix.vecMulVec_apply, Matrix.kroneckerMap_apply, Pi.star_apply, ha, hb]

theorem flag_entropy (m : μ) (ρ : DensityMatrix ο) : (flag m ρ).vonNeumann = ρ.vonNeumann := by
  rw [flag, DensityMatrix.tensor_entropy]
  have h := pureState_entropy_zero (basisVector m) (basisVector_normalized m)
  change (basisState m).vonNeumann=0 at h
  rw [h, zero_add]

/-- The actual mixture of mutually orthogonal flags. -/
def flaggedState (p : μ → ℝ) (hp : ∀ m, 0 ≤ p m) (hs : ∑ m, p m=1)
    (ρ : μ → DensityMatrix ο) : DensityMatrix (μ × ο) :=
  DensityMatrix.mixture p hp hs (fun m => flag m (ρ m))

theorem mixture_flags_eq (p : μ → ℝ) (hp : ∀ m, 0 ≤ p m) (hs : ∑ m, p m=1)
    (ρ : μ → DensityMatrix ο) :
    DensityMatrix.mixture p hp hs (fun m => flag m (ρ m)) = flaggedState p hp hs ρ := rfl

theorem flaggedState_matrix_apply (p : μ → ℝ) (hp : ∀ m, 0 ≤ p m) (hs : ∑ m, p m=1)
    (ρ : μ → DensityMatrix ο) (a b : μ) (i j : ο) :
    (flaggedState p hp hs ρ).matrix (a,i) (b,j) =
      if a=b then (p a:ℂ)*(ρ a).matrix i j else 0 := by
  simp only [flaggedState, DensityMatrix.mixture_matrix, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, flag_matrix_apply]
  by_cases hab : a=b
  · subst b
    simp [mul_ite]
  · have hfalse (m : μ) : ¬(a=m ∧ b=m) := by rintro ⟨rfl,rfl⟩; exact hab rfl
    simp [hfalse,hab]

/-- Block diagonal matrices with the classical index first. -/
def blockMatrix (A : μ → Matrix ο ο ℂ) : Matrix (μ × ο) (μ × ο) ℂ :=
  (Matrix.blockDiagonal A).submatrix (Equiv.prodComm μ ο) (Equiv.prodComm μ ο)

omit [Fintype μ] [Fintype ο] [DecidableEq ο] in
@[simp] theorem blockMatrix_apply (A : μ → Matrix ο ο ℂ) (a b : μ) (i j : ο) :
    blockMatrix A (a,i) (b,j) = if a=b then A a i j else 0 := rfl

omit [DecidableEq ο] in
theorem blockMatrix_mul (A B : μ → Matrix ο ο ℂ) :
    blockMatrix A * blockMatrix B = blockMatrix (fun m => A m * B m) := by
  simp only [blockMatrix, Matrix.submatrix_mul_equiv, Matrix.blockDiagonal_mul]

omit [Fintype μ] [Fintype ο] in
@[simp] theorem blockMatrix_one : blockMatrix (fun _ : μ => (1 : Matrix ο ο ℂ)) = 1 := by
  change (Matrix.blockDiagonal (1 : μ → Matrix ο ο ℂ)).submatrix
    (Equiv.prodComm μ ο) (Equiv.prodComm μ ο) = 1
  rw [Matrix.blockDiagonal_one]
  exact Matrix.submatrix_one_equiv (Equiv.prodComm μ ο)

omit [Fintype μ] [Fintype ο] [DecidableEq ο] in
theorem blockMatrix_star (A : μ → Matrix ο ο ℂ) :
    star (blockMatrix A) = blockMatrix (fun m => star (A m)) := by
  simp only [blockMatrix, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.blockDiagonal_conjTranspose]

omit [Fintype μ] [Fintype ο] in
theorem blockMatrix_diagonal (d : μ → ο → ℂ) :
    blockMatrix (fun m => Matrix.diagonal (d m)) = Matrix.diagonal (fun mi : μ × ο => d mi.1 mi.2) := by
  simp only [blockMatrix, Matrix.blockDiagonal_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

def blockUnitary (U : μ → unitary (Matrix ο ο ℂ)) : unitary (Matrix (μ × ο) (μ × ο) ℂ) :=
  ⟨blockMatrix (fun m => (U m : Matrix ο ο ℂ)), by
    rw [Unitary.mem_iff]
    constructor
    · rw [blockMatrix_star, blockMatrix_mul]
      have hU (m : μ) : star (U m : Matrix ο ο ℂ) * (U m : Matrix ο ο ℂ) = 1 := (U m).property.1
      simp only [hU, blockMatrix_one]
    · rw [blockMatrix_star, blockMatrix_mul]
      have hU (m : μ) : (U m : Matrix ο ο ℂ) * star (U m : Matrix ο ο ℂ) = 1 := (U m).property.2
      simp only [hU, blockMatrix_one]⟩

theorem flaggedState_eq_blockMatrix (p : μ → ℝ) (hp : ∀ m, 0 ≤ p m) (hs : ∑ m, p m=1)
    (ρ : μ → DensityMatrix ο) :
    (flaggedState p hp hs ρ).matrix = blockMatrix (fun m => (p m:ℂ) • (ρ m).matrix) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [flaggedState_matrix_apply, blockMatrix_apply, Matrix.smul_apply, smul_eq_mul]

theorem flaggedState_diagonalization (p : μ → ℝ) (hp : ∀ m, 0 ≤ p m) (hs : ∑ m, p m=1)
    (ρ : μ → DensityMatrix ο) :
    (flaggedState p hp hs ρ).matrix =
      (blockUnitary (fun m => (ρ m).positive.isHermitian.eigenvectorUnitary) : Matrix _ _ ℂ) *
        Matrix.diagonal (fun mi : μ × ο => ((p mi.1*(ρ mi.1).weights mi.2 : ℝ):ℂ)) *
          (star (blockUnitary (fun m => (ρ m).positive.isHermitian.eigenvectorUnitary)) : Matrix _ _ ℂ) := by
  let U (m : μ) := (ρ m).positive.isHermitian.eigenvectorUnitary
  have hm (m : μ) : (p m:ℂ) • (ρ m).matrix =
      (U m : Matrix ο ο ℂ) * Matrix.diagonal (fun i => ((p m*(ρ m).weights i:ℝ):ℂ)) *
        (star (U m) : Matrix ο ο ℂ) := by
    have he : (ρ m).matrix = (U m : Matrix ο ο ℂ) *
        Matrix.diagonal (fun i => ((ρ m).weights i:ℂ)) * (star (U m) : Matrix ο ο ℂ) :=
      (ρ m).positive.isHermitian.spectral_theorem
    rw [he]
    have hd : Matrix.diagonal (fun i => ((p m*(ρ m).weights i:ℝ):ℂ)) =
        (p m:ℂ) • Matrix.diagonal (fun i => ((ρ m).weights i:ℂ)) := by
      rw [←Matrix.diagonal_smul]
      apply congrArg Matrix.diagonal
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul]
  rw [flaggedState_eq_blockMatrix]
  simp_rw [hm]
  rw [←blockMatrix_mul, ←blockMatrix_mul, blockMatrix_diagonal]
  simp only [blockUnitary, ←blockMatrix_star]
  rfl

/-- Exact entropy of a genuine finite classical-quantum state, with arbitrary
zero probabilities and arbitrary mixed conditional states. -/
theorem flaggedState_entropy (p : μ → ℝ) (hp : ∀ m, 0 ≤ p m) (hs : ∑ m, p m=1)
    (ρ : μ → DensityMatrix ο) :
    (flaggedState p hp hs ρ).vonNeumann = shannon p + ∑ m, p m*(ρ m).vonNeumann := by
  rw [(flaggedState p hp hs ρ).entropy_eq_shannon_of_diagonalization
    (fun mi : μ × ο => p mi.1*(ρ mi.1).weights mi.2)
    (blockUnitary (fun m => (ρ m).positive.isHermitian.eigenvectorUnitary))
    (flaggedState_diagonalization p hp hs ρ)]
  exact shannon_joint p (fun m => (ρ m).weights) (fun m => (ρ m).weights_sum)

end Nonadditivity.OperationalFlaggedEntropy
