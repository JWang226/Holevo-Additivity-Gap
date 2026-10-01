/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSMemory

/-! # Literal path-sum identity for open-register contractions

The kernels below are explicit finite sums of coefficient products with equality
constraints on retained indices. Their norm estimate is derived from the actual
operators, rather than assumed as an identity or a matrix norm hypothesis.
-/

noncomputable section

namespace Nonadditivity.NoncommutativeCS

open scoped BigOperators InnerProduct

variable {𝕜 E J : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [Fintype J] [DecidableEq J]

def insertState {n : ℕ} (s : Fin n → J) : E →L[𝕜] Memory J E n :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 (Pi.single s x)
      map_add' := by intros; ext t; simp [Pi.single_apply]; split_ifs <;> simp
      map_smul' := by intros; ext t; simp [Pi.single_apply] }
    1 (fun x => by simp [PiLp.norm_toLp_single])

def extractState {n : ℕ} (s : Fin n → J) : Memory J E n →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun x => x s
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa only [one_mul] using PiLp.norm_apply_le x s)

omit [CompleteSpace E] in
@[simp] theorem insertState_apply {n : ℕ} (s : Fin n → J) (x : E) (t : Fin n → J) :
    insertState (𝕜 := 𝕜) s x t = if t = s then x else 0 := by
  simp [insertState, Pi.single_apply]

omit [CompleteSpace E] [DecidableEq J] in
@[simp] theorem extractState_apply {n : ℕ} (s : Fin n → J) (x : Memory J E n) :
    extractState (𝕜 := 𝕜) s x = x s := rfl

omit [CompleteSpace E] in
theorem insertState_norm_le {n : ℕ} (s : Fin n → J) :
    ‖insertState (𝕜 := 𝕜) (E := E) s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [insertState, PiLp.norm_toLp_single]

omit [CompleteSpace E] [DecidableEq J] in
theorem extractState_norm_le {n : ℕ} (s : Fin n → J) :
    ‖extractState (𝕜 := 𝕜) (E := E) s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using PiLp.norm_apply_le x s

omit [CompleteSpace E] in
/-- The retained registers form an actual orthogonal resolution of identity. -/
theorem state_resolution (n : ℕ) :
    (∑ s : Fin n → J, insertState (𝕜 := 𝕜) (E := E) s ∘L extractState s) =
      ContinuousLinearMap.id 𝕜 (Memory J E n) := by
  ext x t
  simp

namespace Contraction

/-- Literal coefficient matrix of a contraction between prescribed memory states. -/
def kernel {m n : ℕ} (P : Contraction 𝕜 E J m n) (s : Fin n → J) (t : Fin m → J) :
    E →L[𝕜] E := extractState s ∘L P.operator ∘L insertState t

/-- Every individual coefficient has the same product bound as the contraction. -/
theorem kernel_norm_le {m n : ℕ} (P : Contraction 𝕜 E J m n)
    (s : Fin n → J) (t : Fin m → J) : ‖P.kernel s t‖ ≤ P.cost := by
  calc
    _ ≤ ‖extractState (𝕜 := 𝕜) (E := E) s‖ *
        (‖P.operator‖ * ‖insertState (𝕜 := 𝕜) (E := E) t‖) := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (P.cost * 1) :=
      mul_le_mul (extractState_norm_le s)
        (mul_le_mul P.norm_operator_le (insertState_norm_le t) (norm_nonneg _) P.cost_nonneg)
        (by positivity) (by norm_num)
    _ = _ := by ring

@[simp] theorem kernel_identity (n : ℕ) (s t : Fin n → J) :
    (Contraction.identity (𝕜 := 𝕜) (E := E) (J := J) n).kernel s t =
      if s = t then ContinuousLinearMap.id 𝕜 E else 0 := by
  ext x
  by_cases h : s = t <;> simp [kernel, operator, h]

@[simp] theorem kernel_open {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (s : Fin (n + 1) → J) (t : Fin n → J) :
    (Contraction.openReg p A).kernel s t = if p.removeNth s = t then A (s p) else 0 := by
  ext x
  by_cases h : p.removeNth s = t <;> simp [kernel, operator, h]

@[simp] theorem kernel_close {n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (s : Fin n → J) (t : Fin (n + 1) → J) :
    (Contraction.closeReg p A).kernel s t = if p.removeNth t = s then A (t p) else 0 := by
  ext x
  simp only [kernel, operator, ContinuousLinearMap.comp_apply, extractState_apply,
    closeRegister_apply, insertState_apply, apply_ite, map_zero]
  have hmatch (j : J) : p.insertNth j s = t ↔ j = t p ∧ s = p.removeNth t := by
    rw [Fin.insertNth_eq_iff]
  simp only [hmatch]
  by_cases hs : p.removeNth t = s
  · subst s
    simp
  · simp [hs, Ne.symm hs]

@[simp] theorem kernel_diagonal (n : ℕ) (A : (Fin n → J) → E →L[𝕜] E)
    (s t : Fin n → J) :
    (Contraction.diagonalReg n A).kernel s t = if s = t then A s else 0 := by
  ext x
  by_cases h : s = t <;> simp [kernel, operator, h]

/-- Composition is exactly the sum over all intermediate register assignments. -/
theorem kernel_comp {l m n : ℕ} (Q : Contraction 𝕜 E J m n) (P : Contraction 𝕜 E J l m)
    (s : Fin n → J) (t : Fin l → J) :
    (Q.comp P).kernel s t = ∑ u : Fin m → J, Q.kernel s u ∘L P.kernel u t := by
  have h := state_resolution (𝕜 := 𝕜) (E := E) (J := J) m
  ext x
  have h' := congrArg (fun R : Memory J E m →L[𝕜] Memory J E m =>
    extractState (𝕜 := 𝕜) s (Q.operator (R (P.operator (insertState (𝕜 := 𝕜) t x))))) h
  simpa [kernel, operator, map_sum] using h'.symm

/-- A fully expanded path-sum definition with explicit open/close constraints. -/
def pathSum {m n : ℕ} :
    Contraction 𝕜 E J m n → (Fin n → J) → (Fin m → J) → E →L[𝕜] E
  | .identity _, s, t => if s = t then ContinuousLinearMap.id 𝕜 E else 0
  | .openReg p A, s, t => if p.removeNth s = t then A (s p) else 0
  | .closeReg p A, s, t => if p.removeNth t = s then A (t p) else 0
  | .diagonalReg _ A, s, t => if s = t then A s else 0
  | .comp Q P, s, t => ∑ u, pathSum Q s u ∘L pathSum P u t

/-- The path-to-contraction identity is proved, not supplied as a premise. -/
theorem pathSum_eq_kernel {m n : ℕ} (P : Contraction 𝕜 E J m n)
    (s : Fin n → J) (t : Fin m → J) : P.pathSum s t = P.kernel s t := by
  induction P with
  | identity => exact (kernel_identity _ _ _).symm
  | openReg => exact (kernel_open _ _ _ _).symm
  | closeReg => exact (kernel_close _ _ _ _).symm
  | diagonalReg => exact (kernel_diagonal _ _ _ _).symm
  | comp Q P hQ hP => simp only [pathSum, hQ, hP, kernel_comp]

/-- An unconditional bound on the literal constrained coefficient path sum. -/
theorem pathSum_norm_le {m n : ℕ} (P : Contraction 𝕜 E J m n)
    (s : Fin n → J) (t : Fin m → J) : ‖P.pathSum s t‖ ≤ P.cost := by
  rw [pathSum_eq_kernel]
  exact P.kernel_norm_le s t

end Contraction

end Nonadditivity.NoncommutativeCS
