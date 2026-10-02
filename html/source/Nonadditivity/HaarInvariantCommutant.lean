/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarInvariantTensor
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Swap

/-! # The tensor-power commutant of the unitary group

Commutation with every unitary tensor power implies commutation with every
matrix tensor power.  Phase weights give diagonal matrices, the spectral
theorem gives Hermitian matrices, and elementary matrices finish the proof.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarInvariantCommutant
open HaarModel HaarInvariantTensor HaarFourthMoments
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {N p : ℕ}

theorem power_diagonal (d : Fin (N+1) → ℂ) :
    power p (Matrix.diagonal d) = Matrix.diagonal (fun x : Tuple N p => ∏ r, d (x r)) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [power]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])

theorem commute_diagonal_of_unitary (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ U : LocalUnitary N, Commute T (power p (U : Mat N)))
    (d : Fin (N+1) → ℂ) : Commute T (power p (Matrix.diagonal d)) := by
  classical
  have hv : ∀ U : LocalUnitary N, mixed N p U *ᵥ vectorize T = vectorize T :=
    fun U => (mixed_fixed_iff_commute U T).mpr (hT U).eq.symm
  rw [power_diagonal]
  change T * Matrix.diagonal _ = Matrix.diagonal _ * T
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hzero : T x y = 0
  · simp [hzero]
  · have hm (r : Fin (N+1)) : HaarMixedMoments.multiplicity x r =
        HaarMixedMoments.multiplicity y r := by
      by_contra hne
      exact hzero (invariant_eq_zero_of_multiplicity_ne (vectorize T) hv x y r hne)
    obtain ⟨σ, hσ⟩ := exists_perm_of_multiplicity_eq x y hm
    have he : (∏ r, d (x r)) = ∏ r, d (y r) := by
      rw [hσ]
      exact Equiv.prod_comp σ (fun r => d (y r))
    rw [he, mul_comm]

theorem commute_hermitian_of_unitary (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ U : LocalUnitary N, Commute T (power p (U : Mat N)))
    (A : Mat N) (hA : A.IsHermitian) : Commute T (power p A) := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, power_mul, power_mul]
  exact ((hT hA.eigenvectorUnitary).mul_right
    (commute_diagonal_of_unitary T hT _)).mul_right (hT (star hA.eigenvectorUnitary))

theorem commute_transvection_one_of_unitary (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ U : LocalUnitary N, Commute T (power p (U : Mat N)))
    (i j : Fin (N+1)) : Commute T (power p (Matrix.transvection i j 1)) := by
  let S : Mat N := Matrix.swap ℂ i j
  have hS : S.IsHermitian := Matrix.conjTranspose_swap i j
  have hD : (Matrix.single j j (1 : ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  have he : S * Matrix.single j j (1 : ℂ) = Matrix.single i j 1 := by
    ext a b
    have hs : (j = Equiv.swap i j a) ↔ i = a := by
      constructor
      · intro h
        simpa using congrArg (Equiv.swap i j) h
      · intro h
        simp [← h]
    simp [S, Matrix.swap, PEquiv.toMatrix_toPEquiv_mul,
      Matrix.single_apply, hs]
  have hprod : S * (S + Matrix.single j j 1) = Matrix.transvection i j 1 := by
    rw [Matrix.mul_add, he]
    simp [S, Matrix.swap_mul_self, Matrix.transvection]
  rw [← hprod, power_mul]
  exact (commute_hermitian_of_unitary T hT S hS).mul_right
    (commute_hermitian_of_unitary T hT _ (hS.add hD))

theorem commute_transvection_of_unitary (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ U : LocalUnitary N, Commute T (power p (U : Mat N)))
    (i j : Fin (N+1)) (hij : i ≠ j) (c : ℂ) :
    Commute T (power p (Matrix.transvection i j c)) := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [power_one]
  · let d : Fin (N+1) → ℂ := fun r => if r=i then c else 1
    let e : Fin (N+1) → ℂ := fun r => if r=i then c⁻¹ else 1
    have he : Matrix.diagonal d * Matrix.transvection i j 1 * Matrix.diagonal e =
        Matrix.transvection i j c := by
      ext a b
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transvection,
        Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      by_cases hab : a=b
      · subst b
        by_cases hai : a=i <;> by_cases haj : a=j <;>
          simp_all [d, e, eq_comm]
      · by_cases hai : a=i <;> by_cases hbj : b=j <;>
          simp_all [d, e, eq_comm]
    rw [← he, power_mul, power_mul]
    exact ((commute_diagonal_of_unitary T hT d).mul_right
      (commute_transvection_one_of_unitary T hT i j)).mul_right
        (commute_diagonal_of_unitary T hT e)

/-- The unitary and full-matrix tensor powers have the same commutant. -/
theorem commute_all_matrices_of_unitary (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ U : LocalUnitary N, Commute T (power p (U : Mat N)))
    (A : Mat N) : Commute T (power p A) := by
  apply Matrix.diagonal_transvection_induction (fun A => Commute T (power p A)) A
  · intro d _
    exact commute_diagonal_of_unitary T hT d
  · intro t
    exact commute_transvection_of_unitary T hT t.i t.j t.hij t.c
  · intro A B hA hB
    rw [power_mul]
    exact hA.mul_right hB

theorem commute_power_of_unitary (T : Matrix (Tuple N p) (Tuple N p) ℂ)
    (hT : ∀ U : LocalUnitary N, power p (U : Mat N) * T = T * power p (U : Mat N))
    (A : Mat N) : power p A * T = T * power p A :=
  (commute_all_matrices_of_unitary T (fun U => (hT U).symm) A).eq.symm

end Nonadditivity.HaarInvariantCommutant
