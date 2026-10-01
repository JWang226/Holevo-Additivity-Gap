/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCS
import Mathlib.Data.Fin.Tuple.Basic

/-! # Arbitrary open-memory contractions

A register is created at one occurrence of a paired index, retained across
arbitrary diagonal factors, and summed out at its other occurrence. Registers
can be removed in any order, so the construction includes crossing partitions.
The norm bound is proved for the literal recursively evaluated finite sums.
-/

noncomputable section

namespace Nonadditivity.NoncommutativeCS

open scoped BigOperators InnerProduct

variable {𝕜 E J : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [Fintype J]

abbrev Memory (J E : Type*) [Fintype J] [NormedAddCommGroup E] (n : ℕ) :=
  DirectSum (Fin n → J) E

/-- Separate any chosen register, not only the most recently created one. -/
def splitRegister {n : ℕ} (p : Fin (n + 1)) :
    Memory J E (n + 1) ≃ₗᵢ[𝕜] DirectSum (Fin n → J) (DirectSum J E) where
  toFun x := WithLp.toLp 2 (fun s => WithLp.toLp 2 (fun j => x (p.insertNth j s)))
  invFun x := WithLp.toLp 2 (fun s => x (p.removeNth s) (s p))
  left_inv := by intro x; ext s; simp
  right_inv := by intro x; ext s j; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    change (∑ s : Fin n → J, ∑ j : J, ‖x (p.insertNth j s)‖ ^ 2) = _
    rw [Finset.sum_comm, ← Fintype.sum_prod_type
      (fun z : J × (Fin n → J) => ‖x (p.insertNth z.1 z.2)‖ ^ 2)]
    exact Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => J) p)
      (fun z => ‖x (p.insertNth z.1 z.2)‖ ^ 2) (fun s => ‖x s‖ ^ 2) (fun _ => rfl)

omit [CompleteSpace E] in
@[simp] theorem splitRegister_apply {n : ℕ} (p : Fin (n + 1))
    (x : Memory J E (n + 1)) (s : Fin n → J) (j : J) :
    splitRegister (𝕜 := 𝕜) p x s j = x (p.insertNth j s) := rfl

omit [CompleteSpace E] in
@[simp] theorem splitRegister_symm_apply {n : ℕ} (p : Fin (n + 1))
    (x : DirectSum (Fin n → J) (DirectSum J E)) (s : Fin (n + 1) → J) :
    (splitRegister (𝕜 := 𝕜) p).symm x s = x (p.removeNth s) (s p) := rfl

def openRegister {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E) :
    Memory J E n →L[𝕜] Memory J E (n + 1) :=
  (splitRegister (𝕜 := 𝕜) p).symm.toLinearIsometry.toContinuousLinearMap ∘L
    amplify (column A)

def closeRegister {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E) :
    Memory J E (n + 1) →L[𝕜] Memory J E n :=
  amplify (row A) ∘L (splitRegister (𝕜 := 𝕜) p).toLinearIsometry.toContinuousLinearMap

@[simp] theorem openRegister_apply {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (x : Memory J E n) (s : Fin (n + 1) → J) :
    openRegister p A x s = A (s p) (x (p.removeNth s)) := rfl

@[simp] theorem closeRegister_apply {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (x : Memory J E (n + 1)) (s : Fin n → J) :
    closeRegister p A x s = ∑ j, A j (x (p.insertNth j s)) := by
  simp [closeRegister]

theorem openRegister_norm_le {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E) :
    ‖openRegister p A‖ ≤ Real.sqrt ‖columnGram A‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ 1 * Real.sqrt ‖columnGram A‖ :=
      mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _)
        ((amplify_norm_le _).trans (column_norm_le A)) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem closeRegister_norm_le {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E) :
    ‖closeRegister p A‖ ≤ Real.sqrt ‖rowGram A‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ Real.sqrt ‖rowGram A‖ * 1 :=
      mul_le_mul ((amplify_norm_le _).trans (row_norm_le A))
        (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

/-- A finite contraction with explicit active registers. Each middle factor
depends only on the registers that are currently open. -/
inductive Contraction (𝕜 E J : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : ℕ → ℕ → Type _
  | identity (n : ℕ) : Contraction 𝕜 E J n n
  | openReg {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E) :
      Contraction 𝕜 E J n (n + 1)
  | closeReg {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E) :
      Contraction 𝕜 E J (n + 1) n
  | diagonalReg (n : ℕ) (A : (Fin n → J) → E →L[𝕜] E) :
      Contraction 𝕜 E J n n
  | comp {l m n : ℕ} (Q : Contraction 𝕜 E J m n) (P : Contraction 𝕜 E J l m) :
      Contraction 𝕜 E J l n

namespace Contraction

def operator {m n : ℕ} : Contraction 𝕜 E J m n → Memory J E m →L[𝕜] Memory J E n
  | .identity _ => ContinuousLinearMap.id 𝕜 _
  | .openReg p A => openRegister p A
  | .closeReg p A => closeRegister p A
  | .diagonalReg _ A => diagonal A
  | .comp Q P => operator Q ∘L operator P

/-- Literal sum-of-products semantics; no norm estimate occurs in this definition. -/
def evaluate {m n : ℕ} :
    Contraction 𝕜 E J m n → ((Fin m → J) → E) → (Fin n → J) → E
  | .identity _, x => x
  | .openReg p A, x => fun s => A (s p) (x (p.removeNth s))
  | .closeReg p A, x => fun s => ∑ j, A j (x (p.insertNth j s))
  | .diagonalReg _ A, x => fun s => A s (x s)
  | .comp Q P, x => evaluate Q (evaluate P x)

def cost {m n : ℕ} : Contraction 𝕜 E J m n → ℝ
  | .identity _ => 1
  | .openReg _ A => Real.sqrt ‖columnGram A‖
  | .closeReg _ A => Real.sqrt ‖rowGram A‖
  | .diagonalReg _ A => ‖A‖
  | .comp Q P => cost Q * cost P

theorem cost_nonneg {m n : ℕ} (P : Contraction 𝕜 E J m n) : 0 ≤ P.cost := by
  induction P with
  | identity => exact zero_le_one
  | openReg => exact Real.sqrt_nonneg _
  | closeReg => exact Real.sqrt_nonneg _
  | diagonalReg => exact norm_nonneg _
  | comp Q P hQ hP => exact mul_nonneg hQ hP

@[simp] theorem operator_apply {m n : ℕ} (P : Contraction 𝕜 E J m n)
    (x : Memory J E m) (s : Fin n → J) : P.operator x s = P.evaluate (fun t => x t) s := by
  induction P with
  | identity => rfl
  | openReg => rfl
  | closeReg => exact closeRegister_apply _ _ _ _
  | diagonalReg => rfl
  | comp Q P hQ hP =>
      simp only [operator, ContinuousLinearMap.comp_apply, hQ, hP, evaluate]

/-- Every finite open-memory contraction obeys its product of row, column,
and diagonal factors. Crossings cost no extra factor. -/
theorem norm_operator_le {m n : ℕ} (P : Contraction 𝕜 E J m n) : ‖P.operator‖ ≤ P.cost := by
  induction P with
  | identity => exact ContinuousLinearMap.norm_id_le
  | openReg => exact openRegister_norm_le _ _
  | closeReg => exact closeRegister_norm_le _ _
  | diagonalReg n A => exact diagonal_norm_le A ‖A‖ (norm_nonneg _) (norm_le_pi_norm A)
  | comp Q P hQ hP =>
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hQ hP (norm_nonneg _) Q.cost_nonneg)

/-- The same estimate, directly on the recursively evaluated sum of products. -/
theorem evaluate_norm_le {m n : ℕ} (P : Contraction 𝕜 E J m n) (x : Memory J E m) :
    ‖(WithLp.toLp 2 (P.evaluate (fun s => x s)) : Memory J E n)‖ ≤ P.cost * ‖x‖ := by
  have h : (WithLp.toLp 2 (P.evaluate (fun s => x s)) : Memory J E n) = P.operator x := by
    ext s
    exact (P.operator_apply x s).symm
  rw [h]
  exact (P.operator.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right P.norm_operator_le (norm_nonneg _))

end Contraction

end Nonadditivity.NoncommutativeCS
