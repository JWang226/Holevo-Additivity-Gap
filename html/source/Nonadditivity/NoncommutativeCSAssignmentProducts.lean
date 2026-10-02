/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSAssignments

/-! # Ordered products over named global assignments

For a closed register program the boundary condition disappears. Its global
assignment sum is literally a sum of list products of the original factors.
The profile variables may be indexed by any equivalent finite label type.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.NoncommutativeCS.AssignmentProgram
open scoped BigOperators InnerProduct

variable {𝕜 E J : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [Fintype J] [DecidableEq J]

/-- The final active assignment under one fixed global profile choice. -/
def finalState {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n) :
    (Fin P.variableCount → J) → (Fin m → J) → (Fin n → J) :=
  match P with
  | .done _ => fun _ t => t
  | .openReg p _ P => fun σ t =>
      P.finalState (Fin.tail σ) (p.insertNth (σ (0 : Fin (P.variableCount + 1))) t)
  | .closeReg p _ P => fun σ t => P.finalState σ (p.removeNth t)
  | .middle _ P => fun σ t => P.finalState σ t
  | .singleton _ P => fun σ t => P.finalState (Fin.tail σ) t

/-- The original factors, in their operator multiplication order. -/
def factors {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n) :
    (Fin P.variableCount → J) → (Fin m → J) → List (E →L[𝕜] E) :=
  match P with
  | .done _ => fun _ _ => []
  | .openReg p A P => fun σ t =>
      P.factors (Fin.tail σ) (p.insertNth (σ (0 : Fin (P.variableCount + 1))) t) ++
        [A (σ (0 : Fin (P.variableCount + 1)))]
  | .closeReg p A P => fun σ t => P.factors σ (p.removeNth t) ++ [A (t p)]
  | .middle A P => fun σ t => P.factors σ t ++ [A t]
  | .singleton A P => fun σ t => P.factors (Fin.tail σ) t ++
      [A (σ (0 : Fin (P.variableCount + 1)))]

/-- The only constraint remaining after a global profile is chosen is that
the final register state agrees with the requested output state. -/
theorem coefficient_eq_product {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n)
    (σ : Fin P.variableCount → J) (s : Fin n → J) (t : Fin m → J) :
    P.coefficient σ s t =
      if s = P.finalState σ t then (P.factors σ t).prod else 0 := by
  induction P with
  | done n => rfl
  | openReg p A P ih =>
      simp only [coefficient, finalState, factors, List.prod_append, List.prod_singleton, ih]
      split_ifs <;> rfl
  | closeReg p A P ih =>
      simp only [coefficient, finalState, factors, List.prod_append, List.prod_singleton, ih]
      split_ifs <;> rfl
  | middle A P ih =>
      simp only [coefficient, finalState, factors, List.prod_append, List.prod_singleton, ih]
      split_ifs <;> rfl
  | singleton A P ih =>
      simp only [coefficient, finalState, factors, List.prod_append, List.prod_singleton, ih]
      split_ifs <;> rfl

/-- With no remaining open register, every global assignment contributes
its full ordered product, without a boundary indicator. -/
theorem coefficient_closed_eq_product {m : ℕ} (P : AssignmentProgram 𝕜 E J m 0)
    (σ : Fin P.variableCount → J) (s : Fin 0 → J) (t : Fin m → J) :
    P.coefficient σ s t = (P.factors σ t).prod := by
  rw [coefficient_eq_product, if_pos (Subsingleton.elim _ _)]

/-- The exact endpoint/middle cost. Singleton variables incur the norm of
their actual sum, rather than a gratuitous cardinality factor. -/
def cost {m n : ℕ} : AssignmentProgram 𝕜 E J m n → ℝ
  | .done _ => 1
  | .openReg _ A P => P.cost * Real.sqrt ‖columnGram A‖
  | .closeReg _ A P => P.cost * Real.sqrt ‖rowGram A‖
  | .middle A P => P.cost * ‖A‖
  | .singleton A P => P.cost * ‖∑ j, A j‖

theorem cost_nonneg {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n) : 0 ≤ P.cost := by
  induction P <;> simp only [cost] <;> positivity

theorem compile_cost_le {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n) :
    P.compile.cost ≤ P.cost := by
  induction P with
  | done n => rfl
  | openReg p A P ih =>
      exact mul_le_mul_of_nonneg_right ih (Real.sqrt_nonneg _)
  | closeReg p A P ih =>
      exact mul_le_mul_of_nonneg_right ih (Real.sqrt_nonneg _)
  | middle A P ih =>
      exact mul_le_mul_of_nonneg_right ih (norm_nonneg _)
  | singleton A P ih =>
      exact mul_le_mul ih (pi_norm_le_iff_of_nonneg (norm_nonneg (∑ j, A j)) |>.mpr
        (fun _ => le_rfl)) (norm_nonneg _) P.cost_nonneg

/-- The BC global profile sum, as an actual finite sum of ordered products. -/
theorem sum_products_norm_le (P : AssignmentProgram 𝕜 E J 0 0) :
    ‖∑ σ : Fin P.variableCount → J, (P.factors σ Fin.elim0).prod‖ ≤ P.cost := by
  have h := P.assignmentSum_norm_le (s := Fin.elim0) (t := Fin.elim0)
  simp only [coefficient_closed_eq_product] at h
  exact h.trans P.compile_cost_le

/-- The same theorem with profiles indexed by any finite set of edge labels.
The label enumeration is an equivalence, so no profile is lost or repeated. -/
theorem named_sum_products_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    (P : AssignmentProgram 𝕜 E J 0 0) (e : Fin P.variableCount ≃ I) :
    ‖∑ σ : I → J, (P.factors (fun k => σ (e k)) Fin.elim0).prod‖ ≤ P.cost := by
  let E : (I → J) ≃ (Fin P.variableCount → J) :=
    { toFun := fun σ k => σ (e k)
      invFun := fun σ i => σ (e.symm i)
      left_inv := by intro σ; funext i; simp
      right_inv := by intro σ; funext i; simp }
  have he := Fintype.sum_equiv E
    (fun σ : I → J => (P.factors (fun k => σ (e k)) Fin.elim0).prod)
    (fun σ : Fin P.variableCount → J => (P.factors σ Fin.elim0).prod) (fun _ => rfl)
  rw [he]
  exact P.sum_products_norm_le

end Nonadditivity.NoncommutativeCS.AssignmentProgram
