/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ShiftNorm
import Nonadditivity.FreeBridge
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # The prescribed observable and its exact free norm

The first tensor factor exchanges two distinct basis vectors, and all remaining
factors are scalar identities. Its free polynomial is an actual bilateral shift
plus its inverse. No spectral or norm hypothesis is assumed.
-/

noncomputable section

namespace Nonadditivity.PrescribedTest

open FreeModel
open scoped BigOperators Matrix Kronecker

variable {K : ℕ}

def core (i j : Fin K) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.single i j 1 + Matrix.single j i 1

theorem core_isHermitian (i j : Fin K) : (core i j).IsHermitian := by
  change (core i j).conjTranspose = core i j
  simp [core, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

theorem core_trace (i j : Fin K) (hij : i ≠ j) : (core i j).trace = 0 := by
  simp [core, Matrix.trace_add, hij, hij.symm]

theorem core_square_trace (i j : Fin K) (hij : i ≠ j) :
    (core i j * core i j).trace = 2 := by
  norm_num [core, add_mul, mul_add, Matrix.single_mul_single_of_ne, hij, hij.symm,
    Matrix.trace_add]

def branchEquiv (K m : ℕ) : Fin K × Branch K m ≃ Branch K (m + 1) :=
  Fin.consEquiv (fun _ => Fin K)

def unnormalized (i j : Fin K) (m : ℕ) :
    Matrix (Branch K (m + 1)) (Branch K (m + 1)) ℂ :=
  ((core i j) ⊗ₖ (1 : Matrix (Branch K m) (Branch K m) ℂ)).submatrix
    (branchEquiv K m).symm (branchEquiv K m).symm

theorem unnormalized_isHermitian (i j : Fin K) (m : ℕ) :
    (unnormalized i j m).IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  change ((core i j) ⊗ₖ (1 : Matrix (Branch K m) (Branch K m) ℂ)).conjTranspose = _
  rw [Matrix.conjTranspose_kronecker, (core_isHermitian i j).eq,
    Matrix.conjTranspose_one]

theorem unnormalized_trace (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    (unnormalized i j m).trace = 0 := by
  rw [unnormalized, FreeBridge.trace_submatrix_equiv, Matrix.trace_kronecker,
    core_trace i j hij, zero_mul]

theorem unnormalized_square_trace (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    (unnormalized i j m * unnormalized i j m).trace = 2 * (K : ℂ)^m := by
  rw [unnormalized, Matrix.submatrix_mul_equiv, FreeBridge.trace_submatrix_equiv,
    ← Matrix.mul_kronecker_mul, one_mul, Matrix.trace_kronecker,
    core_square_trace i j hij]
  simp

def testScale (K m : ℕ) : ℝ := (Real.sqrt (2 * (K : ℝ)^m))⁻¹

def test (i j : Fin K) (m : ℕ) :
    Matrix (Branch K (m + 1)) (Branch K (m + 1)) ℂ :=
  (testScale K m : ℂ) • unnormalized i j m

theorem test_isHermitian (i j : Fin K) (m : ℕ) :
    (test i j m).IsHermitian := by
  change ((testScale K m : ℂ) • unnormalized i j m).conjTranspose = _
  rw [Matrix.conjTranspose_smul, (unnormalized_isHermitian i j m).eq]
  simp [test]

theorem test_trace (i j : Fin K) (hij : i ≠ j) (m : ℕ) : (test i j m).trace = 0 := by
  simp [test, Matrix.trace_smul, unnormalized_trace i j hij]

theorem test_hsLength (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    AdjointPurity.hsLength (test i j m) = 1 := by
  have hk : 0 < K := i.isLt.trans_le (Nat.le_refl K) |> Nat.zero_lt_of_lt
  have hkr : (0 : ℝ) < K := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (2 * (K : ℝ)^m) := Real.sqrt_pos.mpr (by positivity)
  have hsq := AdjointPurity.hsLength_sq_of_isHermitian (test i j m) (test_isHermitian i j m)
  simp only [test, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    unnormalized_square_trace i j hij m] at hsq
  have hreal : ((testScale K m : ℂ) • ((testScale K m : ℂ) • (2 * (K : ℂ)^m))).re =
      testScale K m ^ 2 * (2 * (K : ℝ)^m) := by
    simp only [smul_eq_mul]
    have hc : (2 * (K : ℂ)^m) = ((2 * (K : ℝ)^m : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hreal] at hsq
  have hv : testScale K m ^ 2 * (2 * (K : ℝ)^m) = 1 := by
    dsimp [testScale]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by positivity)
  have hsq' : AdjointPurity.hsLength (test i j m) ^ 2 = 1 := by
    exact hsq.trans hv
  nlinarith [AdjointPurity.hsLength_nonneg (test i j m)]

def shiftWord (i j : Fin K) (m : ℕ) : ProductFreeGroup K (m + 1) :=
  Fin.cons ((FreeGroup.of i)⁻¹ * FreeGroup.of j) 1

theorem shiftWord_inverse (i j : Fin K) (m : ℕ) :
    shiftWord j i m = (shiftWord i j m)⁻¹ := by
  funext k
  cases k using Fin.cases <;> simp [shiftWord]

theorem shiftWord_powers_injective (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    Function.Injective (fun k : ℕ => shiftWord i j m ^ k) := by
  let φ := FreeGroup.lift (fun k : Fin K =>
    Multiplicative.ofAdd (if k = j then (1 : ℤ) else 0))
  intro a b hab
  have h := congrArg (fun w : ProductFreeGroup K (m + 1) =>
    Multiplicative.toAdd (φ (w 0))) hab
  simpa [φ, shiftWord, hij] using h

theorem branch_difference_same_tail (i j : Fin K) (m : ℕ) (a : Branch K m) :
    (branchWord (branchEquiv K m (i, a)))⁻¹ * branchWord (branchEquiv K m (j, a)) =
      shiftWord i j m := by
  funext k
  cases k using Fin.cases <;> simp [branchWord, branchEquiv, shiftWord]

theorem sum_core_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (i j : Fin K) (f : Fin K → Fin K → E) :
    (∑ a, ∑ b, core i j a b • f a b) = f i j + f j i := by
  classical
  simp [core, Matrix.single_apply, add_smul, Finset.sum_add_distrib,
    ite_smul, ite_and]

theorem unnormalized_polynomial (i j : Fin K) (m : ℕ) :
    (∑ a : Branch K (m + 1), ∑ b : Branch K (m + 1),
      unnormalized i j m a b • leftRegular ((branchWord a)⁻¹ * branchWord b)) =
      (K ^ m : ℂ) • (leftRegular (shiftWord i j m) + leftRegular (shiftWord i j m)⁻¹) := by
  classical
  rw [← (branchEquiv K m).sum_comp]
  simp only [Fintype.sum_prod_type]
  have hinner (a : Fin K) (t : Branch K m) :
      (∑ b : Branch K (m + 1), unnormalized i j m (branchEquiv K m (a, t)) b •
        leftRegular ((branchWord (branchEquiv K m (a, t)))⁻¹ * branchWord b)) =
      ∑ b : Fin K, core i j a b • leftRegular (shiftWord a b m) := by
    rw [← (branchEquiv K m).sum_comp]
    simp only [Fintype.sum_prod_type, unnormalized, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.kronecker_apply, Matrix.one_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
    simp [branch_difference_same_tail]
  simp only [hinner]
  rw [Finset.sum_comm]
  simp only [sum_core_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [shiftWord_inverse i j m]
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem gamma_test (i j : Fin K) (m : ℕ) :
    gamma (test i j m) =
      ((1 / (K : ℂ) ^ (m + 1)) * (testScale K m : ℂ) * (K : ℂ)^m) •
        (leftRegular (shiftWord i j m) + leftRegular (shiftWord i j m)⁻¹) := by
  simp only [gamma, test, Matrix.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum]
  rw [unnormalized_polynomial, smul_smul, smul_smul]

/-- The prescribed unit-HS observable has an exact strictly positive free norm. -/
theorem freeNorm_test (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    freeNorm (test i j m) = 2 * testScale K m / K := by
  classical
  have hk : K ≠ 0 := by omega
  have hkr : (K : ℝ) ≠ 0 := by exact_mod_cast hk
  have hs : 0 ≤ testScale K m := by unfold testScale; positivity
  simp only [freeNorm, gamma_test, norm_smul, norm_mul, norm_div, norm_one,
    norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    ShiftNorm.norm_shift_add_inverse _ (shiftWord_powers_injective i j hij m)]
  rw [pow_succ]
  field_simp

theorem freeNorm_test_pos (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    0 < freeNorm (test i j m) := by
  have hk : 0 < K := by omega
  rw [freeNorm_test i j hij m]
  unfold testScale
  positivity

/-- An equivalent square-root form of the manuscript's exact lower bound. -/
theorem freeNorm_test_eq_sqrt (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    freeNorm (test i j m) = Real.sqrt 2 / ((K : ℝ) * Real.sqrt ((K : ℝ)^m)) := by
  have hk : 0 < K := by omega
  have hkr : (0 : ℝ) < K := by exact_mod_cast hk
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt ((K : ℝ)^m) := Real.sqrt_pos.mpr (by positivity)
  rw [freeNorm_test i j hij m, testScale, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  nlinarith

/-- The exact exponent and constant displayed in the manuscript. -/
theorem freeNorm_test_eq_rpow (i j : Fin K) (hij : i ≠ j) (m : ℕ) :
    freeNorm (test i j m) = Real.sqrt 2 * (K : ℝ) ^ (-((m : ℝ) + 2) / 2) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  rw [freeNorm_test_eq_sqrt i j hij m]
  have hs : Real.sqrt ((K : ℝ)^m) = (K : ℝ)^((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk.le]
    congr 1
    ring
  rw [hs]
  have he : -((m : ℝ) + 2) / 2 = -(1 + (m : ℝ) / 2) := by ring
  rw [he, Real.rpow_neg hk.le, Real.rpow_add hk, Real.rpow_one, div_eq_mul_inv]

/-- Every block length admits the specific traceless Hermitian unit test
whose free norm supplies the first quantitative error-factor lower bound. -/
theorem exists_prescribed_test {n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) :
    ∃ A : Matrix (Branch K n) (Branch K n) ℂ,
      A.IsHermitian ∧ A.trace = 0 ∧ AdjointPurity.hsLength A = 1 ∧
      freeNorm A = Real.sqrt 2 * (K : ℝ)^(-((n : ℝ) + 1) / 2) := by
  cases n with
  | zero => omega
  | succ m =>
      let i : Fin K := ⟨0, by omega⟩
      let j : Fin K := ⟨1, by omega⟩
      have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
      refine ⟨test i j m, test_isHermitian i j m, test_trace i j hij m,
        test_hsLength i j hij m, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        freeNorm_test_eq_rpow i j hij m

end Nonadditivity.PrescribedTest
