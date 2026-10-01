/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Linearization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Dimension-free noncommutative Cauchy--Schwarz operators

These are actual row, column, and diagonal operators on finite Hilbert direct
sums. Their bounds have no factor depending on the dimension of the coefficient
Hilbert space. In particular the coefficients may already contain free regular
representations, as required in tensor-factor iteration of Haar estimates.
-/

noncomputable section

namespace Nonadditivity.NoncommutativeCS

open scoped BigOperators InnerProduct

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev DirectSum (I E : Type*) [Fintype I] [NormedAddCommGroup E] :=
  PiLp 2 (fun _ : I => E)

def columnGram (A : I → E →L[𝕜] F) : E →L[𝕜] E :=
  ∑ i, (A i).adjoint ∘L A i

def rowGram (A : I → E →L[𝕜] F) : F →L[𝕜] F :=
  ∑ i, A i ∘L (A i).adjoint

/-- Column amplification keeps the sharp Gram bound, without a cardinal loss. -/
theorem column_apply_norm_le (A : I → E →L[𝕜] F) (x : E) :
    ‖(WithLp.toLp 2 (fun i => A i x) : DirectSum I F)‖ ≤
      Real.sqrt ‖columnGram A‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  exact Linearization.coefficient_energy_le_of_gram_norm Finset.univ A
    (Real.sqrt ‖columnGram A‖) (by rw [Real.sq_sqrt (norm_nonneg _)]; exact le_rfl) x
    |>.trans_eq (by rw [Real.sq_sqrt (norm_nonneg _)])

def column (A : I → E →L[𝕜] F) : E →L[𝕜] DirectSum I F :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 (fun i => A i x)
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp }
    (Real.sqrt ‖columnGram A‖) (column_apply_norm_le A)

@[simp] theorem column_apply (A : I → E →L[𝕜] F) (x : E) (i : I) :
    column A x i = A i x := rfl

theorem column_norm_le (A : I → E →L[𝕜] F) :
    ‖column A‖ ≤ Real.sqrt ‖columnGram A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (column_apply_norm_le A)

def row (A : I → E →L[𝕜] F) : DirectSum I E →L[𝕜] F :=
  (column (fun i => (A i).adjoint)).adjoint

@[simp] theorem row_apply (A : I → E →L[𝕜] F) (x : DirectSum I E) :
    row A x = ∑ i, A i (x i) := by
  apply ext_inner_right 𝕜
  intro y
  simp only [row, ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply,
    column_apply, sum_inner, ContinuousLinearMap.adjoint_inner_right]

theorem row_norm_le (A : I → E →L[𝕜] F) :
    ‖row A‖ ≤ Real.sqrt ‖rowGram A‖ := by
  simpa only [row, LinearIsometryEquiv.norm_map, columnGram,
    ContinuousLinearMap.adjoint_adjoint, rowGram] using
    column_norm_le (fun i => (A i).adjoint)

/-- The operator Cauchy--Schwarz inequality for rectangular coefficients. -/
theorem sum_comp_norm_le (A : I → F →L[𝕜] G) (B : I → E →L[𝕜] F) :
    ‖∑ i, A i ∘L B i‖ ≤ Real.sqrt ‖rowGram A‖ * Real.sqrt ‖columnGram B‖ := by
  have hid : ∑ i, A i ∘L B i = row A ∘L column B := by
    ext x
    simp
  rw [hid]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (row_norm_le A) (column_norm_le B) (norm_nonneg _) (Real.sqrt_nonneg _))

omit [CompleteSpace E] [CompleteSpace F] in
theorem diagonal_apply_norm_le (A : I → E →L[𝕜] F) (q : ℝ) (hq : 0 ≤ q)
    (hA : ∀ i, ‖A i‖ ≤ q) (x : DirectSum I E) :
    ‖(WithLp.toLp 2 (fun i => A i (x i)) : DirectSum I F)‖ ≤ q * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (show ‖A i (x i)‖ ≤ q * ‖x i‖ from
    ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))) 2

/-- The diagonal factor permits dependence on every currently open index. -/
def diagonal (A : I → E →L[𝕜] F) : DirectSum I E →L[𝕜] DirectSum I F :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 (fun i => A i (x i))
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp }
    (∑ i, ‖A i‖) (diagonal_apply_norm_le A _ (Finset.sum_nonneg (fun i _ => norm_nonneg _))
      (fun i => Finset.single_le_sum (fun j _ => norm_nonneg (A j)) (Finset.mem_univ i)))

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem diagonal_apply (A : I → E →L[𝕜] F) (x : DirectSum I E) (i : I) :
    diagonal A x i = A i (x i) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem diagonal_norm_le (A : I → E →L[𝕜] F) (q : ℝ) (hq : 0 ≤ q)
    (hA : ∀ i, ‖A i‖ ≤ q) : ‖diagonal A‖ ≤ q :=
  ContinuousLinearMap.opNorm_le_bound _ hq (diagonal_apply_norm_le A q hq hA)

/-- Applying a coefficient operator while retaining arbitrary open indices is
contractive at exactly the original operator norm. -/
def amplify (A : E →L[𝕜] F) : DirectSum I E →L[𝕜] DirectSum I F :=
  diagonal (fun _ => A)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem amplify_apply (A : E →L[𝕜] F) (x : DirectSum I E) (i : I) :
    amplify A x i = A (x i) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem amplify_norm_le (A : E →L[𝕜] F) : ‖amplify (I := I) A‖ ≤ ‖A‖ :=
  diagonal_norm_le _ _ (norm_nonneg _) (fun _ => le_rfl)

/-- Insertion of arbitrary open-index dependent factors costs only their
uniform norm. -/
theorem sum_comp_diagonal_norm_le (A : I → F →L[𝕜] G) (B : I → E →L[𝕜] F)
    (D : I → F →L[𝕜] F) (q : ℝ) (hq : 0 ≤ q) (hD : ∀ i, ‖D i‖ ≤ q) :
    ‖∑ i, A i ∘L D i ∘L B i‖ ≤
      Real.sqrt ‖rowGram A‖ * q * Real.sqrt ‖columnGram B‖ := by
  have hid : ∑ i, A i ∘L D i ∘L B i = row A ∘L diagonal D ∘L column B := by
    ext x
    simp
  rw [hid]
  calc
    _ ≤ ‖row A‖ * (‖diagonal D‖ * ‖column B‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ Real.sqrt ‖rowGram A‖ * (q * Real.sqrt ‖columnGram B‖) :=
      mul_le_mul (row_norm_le A)
        (mul_le_mul (diagonal_norm_le D q hq hD) (column_norm_le B)
          (norm_nonneg _) hq) (by positivity) (Real.sqrt_nonneg _)
    _ = _ := by ring

end Nonadditivity.NoncommutativeCS
