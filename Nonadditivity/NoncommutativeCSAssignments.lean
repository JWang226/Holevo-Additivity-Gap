/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSPaths

/-! # Global profile assignments and arbitrary register crossings

A program introduces one independent profile variable at every first or
singleton occurrence. Closing a register may select any still open variable.
The coefficient of a global assignment is a single ordered operator product,
with no intermediate summation. Summing those coefficients is proved equal
to the compiled register contraction, including arbitrary crossing patterns.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.NoncommutativeCS
open scoped BigOperators InnerProduct

variable {𝕜 E J : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [Fintype J] [DecidableEq J]

/-- Reindex a sum over all profiles by one distinguished register. -/
theorem sum_assignment_insert {M : Type*} [AddCommMonoid M] {n : ℕ}
    (p : Fin (n + 1)) (f : (Fin (n + 1) → J) → M) :
    (∑ s, f s) = ∑ j, ∑ t : Fin n → J, f (p.insertNth j t) := by
  calc
    _ = ∑ z : J × (Fin n → J), f (p.insertNth z.1 z.2) :=
      (Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => J) p)
        (fun z : J × (Fin n → J) => f (p.insertNth z.1 z.2)) f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

theorem sum_assignment_cons {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n + 1) → J) → M) :
    (∑ s, f s) = ∑ j, ∑ t : Fin n → J, f (Fin.cons j t) := by
  simpa only [Fin.insertNth_zero'] using sum_assignment_insert (0 : Fin (n + 1)) f

/-- A chronological sequence of first, last, middle, and singleton factors.
The source and target indices are the exact numbers of active registers. -/
inductive AssignmentProgram (𝕜 E J : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : ℕ → ℕ → Type _
  | done (n : ℕ) : AssignmentProgram 𝕜 E J n n
  | openReg {n m : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
      (rest : AssignmentProgram 𝕜 E J (n + 1) m) : AssignmentProgram 𝕜 E J n m
  | closeReg {n m : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
      (rest : AssignmentProgram 𝕜 E J n m) : AssignmentProgram 𝕜 E J (n + 1) m
  | middle {n m : ℕ} (A : (Fin n → J) → E →L[𝕜] E)
      (rest : AssignmentProgram 𝕜 E J n m) : AssignmentProgram 𝕜 E J n m
  | singleton {n m : ℕ} (A : J → E →L[𝕜] E)
      (rest : AssignmentProgram 𝕜 E J n m) : AssignmentProgram 𝕜 E J n m

namespace AssignmentProgram

def variableCount {m n : ℕ} : AssignmentProgram 𝕜 E J m n → ℕ
  | .done _ => 0
  | .openReg _ _ P => P.variableCount + 1
  | .closeReg _ _ P => P.variableCount
  | .middle _ P => P.variableCount
  | .singleton _ P => P.variableCount + 1

def compile {m n : ℕ} : AssignmentProgram 𝕜 E J m n → Contraction 𝕜 E J m n
  | .done n => .identity n
  | .openReg p A P => P.compile.comp (.openReg p A)
  | .closeReg p A P => P.compile.comp (.closeReg p A)
  | .middle A P => P.compile.comp (.diagonalReg _ A)
  | .singleton A P => P.compile.comp (.diagonalReg _ (fun _ => ∑ j, A j))

/-- The literal ordered coefficient product at one global assignment.
Every variable is read once when introduced and retained until its last visit. -/
def coefficient {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n) :
    (Fin P.variableCount → J) → (Fin n → J) → (Fin m → J) → E →L[𝕜] E :=
  match P with
  | .done _ => fun _ s t => if s = t then ContinuousLinearMap.id 𝕜 E else 0
  | .openReg p A P => fun σ s t =>
      P.coefficient (Fin.tail σ) s (p.insertNth (σ (0 : Fin (P.variableCount + 1))) t) ∘L
        A (σ (0 : Fin (P.variableCount + 1)))
  | .closeReg p A P => fun σ s t =>
      P.coefficient σ s (p.removeNth t) ∘L A (t p)
  | .middle A P => fun σ s t => P.coefficient σ s t ∘L A t
  | .singleton A P => fun σ s t =>
      P.coefficient (Fin.tail σ) s t ∘L A (σ (0 : Fin (P.variableCount + 1)))

/-- A single sum over all global profile assignments. -/
def assignmentSum {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n)
    (s : Fin n → J) (t : Fin m → J) : E →L[𝕜] E :=
  ∑ σ : Fin P.variableCount → J, P.coefficient σ s t

theorem assignmentSum_open {m n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J (n + 1) m) (s : Fin m → J) (t : Fin n → J) :
    (openReg p A P).assignmentSum s t =
      ∑ j, P.assignmentSum s (p.insertNth j t) ∘L A j := by
  unfold assignmentSum
  change (∑ σ : Fin (P.variableCount + 1) → J, _) = _
  rw [sum_assignment_cons]
  ext x
  simp [coefficient, variableCount]

theorem assignmentSum_close {m n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J n m) (s : Fin m → J) (t : Fin (n + 1) → J) :
    (closeReg p A P).assignmentSum s t =
      P.assignmentSum s (p.removeNth t) ∘L A (t p) := by
  ext x
  simp [assignmentSum, coefficient, variableCount]

theorem assignmentSum_middle {m n : ℕ} (A : (Fin n → J) → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J n m) (s : Fin m → J) (t : Fin n → J) :
    (middle A P).assignmentSum s t = P.assignmentSum s t ∘L A t := by
  ext x
  simp [assignmentSum, coefficient, variableCount]

theorem assignmentSum_singleton {m n : ℕ} (A : J → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J n m) (s : Fin m → J) (t : Fin n → J) :
    (singleton A P).assignmentSum s t = ∑ j, P.assignmentSum s t ∘L A j := by
  unfold assignmentSum
  change (∑ σ : Fin (P.variableCount + 1) → J, _) = _
  rw [sum_assignment_cons]
  ext x
  simp [coefficient, variableCount]

theorem kernel_compile_open {m n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J (n + 1) m) (s : Fin m → J) (t : Fin n → J) :
    (openReg p A P).compile.kernel s t =
      ∑ j, P.compile.kernel s (p.insertNth j t) ∘L A j := by
  rw [compile, Contraction.kernel_comp, sum_assignment_insert p]
  ext x
  simp [Contraction.kernel_open, Fin.removeNth_insertNth, ite_apply, apply_ite]

theorem kernel_compile_close {m n : ℕ} (p : Fin (n + 1)) (A : J → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J n m) (s : Fin m → J) (t : Fin (n + 1) → J) :
    (closeReg p A P).compile.kernel s t =
      P.compile.kernel s (p.removeNth t) ∘L A (t p) := by
  rw [compile, Contraction.kernel_comp]
  ext x
  simp [Contraction.kernel_close, ite_apply, apply_ite]

theorem kernel_compile_middle {m n : ℕ} (A : (Fin n → J) → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J n m) (s : Fin m → J) (t : Fin n → J) :
    (middle A P).compile.kernel s t = P.compile.kernel s t ∘L A t := by
  rw [compile, Contraction.kernel_comp]
  ext x
  simp [Contraction.kernel_diagonal, ite_apply, apply_ite]

theorem kernel_compile_singleton {m n : ℕ} (A : J → E →L[𝕜] E)
    (P : AssignmentProgram 𝕜 E J n m) (s : Fin m → J) (t : Fin n → J) :
    (singleton A P).compile.kernel s t = ∑ j, P.compile.kernel s t ∘L A j := by
  rw [compile, Contraction.kernel_comp]
  ext x
  simp [Contraction.kernel_diagonal, ite_apply, apply_ite, map_sum]

/-- The actual single global assignment sum equals the compiled memory
operator coefficient. No path-sum identity is supplied as a hypothesis. -/
theorem assignmentSum_eq_kernel {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n)
    (s : Fin n → J) (t : Fin m → J) :
    P.assignmentSum s t = P.compile.kernel s t := by
  induction P with
  | done n => simp [assignmentSum, coefficient, compile, variableCount]
  | openReg p A P ih =>
      simp only [assignmentSum_open, kernel_compile_open, ih]
  | closeReg p A P ih =>
      simp only [assignmentSum_close, kernel_compile_close, ih]
  | middle A P ih =>
      simp only [assignmentSum_middle, kernel_compile_middle, ih]
  | singleton A P ih =>
      simp only [assignmentSum_singleton, kernel_compile_singleton, ih]

/-- A dimension-free norm bound for the literal global profile sum.
All crossings are represented by the arbitrary `Fin` chosen at each close. -/
theorem assignmentSum_norm_le {m n : ℕ} (P : AssignmentProgram 𝕜 E J m n)
    (s : Fin n → J) (t : Fin m → J) :
    ‖∑ σ : Fin P.variableCount → J, P.coefficient σ s t‖ ≤ P.compile.cost := by
  change ‖P.assignmentSum s t‖ ≤ _
  rw [assignmentSum_eq_kernel]
  exact P.compile.kernel_norm_le s t

end AssignmentProgram
end Nonadditivity.NoncommutativeCS
