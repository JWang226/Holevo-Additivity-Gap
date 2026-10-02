/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSAssignmentProducts

/-! # Compile named first/last endpoint traces

The input trace records the names of all active labels. Its literal factors
are evaluated from a single global assignment of profiles to those names.
The compiler inserts or removes the corresponding memory register. Closing
any register is allowed, so the theorem imposes no noncrossing restriction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.NoncommutativeCS
open scoped BigOperators InnerProduct

variable {𝕜 E I J : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [Fintype J] [DecidableEq J]

/-- A named endpoint trace with its exact active-label layout at both ends.
Middle coefficients see only currently active labels. -/
inductive EndpointTrace (𝕜 E I J : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : {m n : ℕ} → (Fin m → I) → (Fin n → I) → Type _
  | done {n : ℕ} (layout : Fin n → I) : EndpointTrace 𝕜 E I J layout layout
  | first {m n : ℕ} {layout : Fin m → I} {out : Fin n → I}
      (i : I) (A : J → E →L[𝕜] E)
      (rest : EndpointTrace 𝕜 E I J (Fin.cons i layout) out) :
      EndpointTrace 𝕜 E I J layout out
  | last {m n : ℕ} {layout : Fin (m + 1) → I} {out : Fin n → I}
      (p : Fin (m + 1)) (A : J → E →L[𝕜] E)
      (rest : EndpointTrace 𝕜 E I J (p.removeNth layout) out) :
      EndpointTrace 𝕜 E I J layout out
  | middle {m n : ℕ} {layout : Fin m → I} {out : Fin n → I}
      (A : (Fin m → J) → E →L[𝕜] E)
      (rest : EndpointTrace 𝕜 E I J layout out) : EndpointTrace 𝕜 E I J layout out
  | singleton {m n : ℕ} {layout : Fin m → I} {out : Fin n → I}
      (i : I) (A : J → E →L[𝕜] E)
      (rest : EndpointTrace 𝕜 E I J layout out) : EndpointTrace 𝕜 E I J layout out

namespace EndpointTrace

def compile {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointTrace 𝕜 E I J a b → AssignmentProgram 𝕜 E J m n
  | .done _ => .done _
  | .first _ A P => .openReg 0 A P.compile
  | .last p A P => .closeReg p A P.compile
  | .middle A P => .middle A P.compile
  | .singleton _ A P => .singleton A P.compile

/-- The name of each independent variable introduced by the trace. -/
def labels {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointTrace 𝕜 E I J a b) : Fin P.compile.variableCount → I :=
  match P with
  | .done _ => Fin.elim0
  | .first i _ P => Fin.cons i P.labels
  | .last _ _ P => P.labels
  | .middle _ P => P.labels
  | .singleton i _ P => Fin.cons i P.labels

/-- Literal ordered factors, read directly from the global named assignment. -/
def factors {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointTrace 𝕜 E I J a b) (σ : I → J) : List (E →L[𝕜] E) :=
  match P with
  | .done _ => []
  | .first i A P => P.factors σ ++ [A (σ i)]
  | .last (layout := a) p A P => P.factors σ ++ [A (σ (a p))]
  | .middle (layout := a) A P => P.factors σ ++ [A (σ ∘ a)]
  | .singleton i A P => P.factors σ ++ [A (σ i)]

def markedFlags {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointTrace 𝕜 E I J a b → List Bool
  | .done _ => []
  | .first _ _ P => true :: P.markedFlags
  | .last _ _ P => true :: P.markedFlags
  | .middle _ P => false :: P.markedFlags
  | .singleton _ _ P => true :: P.markedFlags

theorem factors_length {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointTrace 𝕜 E I J a b) (σ : I → J) :
    (P.factors σ).length = P.markedFlags.length := by
  induction P <;> simp_all [factors, markedFlags]

/-- The compiler preserves every literal coefficient product. -/
theorem compile_factors {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointTrace 𝕜 E I J a b) (σ : I → J) :
    P.compile.factors (σ ∘ P.labels) (σ ∘ a) = P.factors σ := by
  induction P with
  | done => rfl
  | first i A P ih =>
      simpa only [compile, labels, AssignmentProgram.factors, Fin.comp_cons,
        Fin.tail_cons, Fin.cons_zero, Fin.insertNth_zero', factors] using
        congrArg (fun l => l ++ [A (σ i)]) ih
  | @last m n a b p A P ih =>
      simpa only [compile, labels, AssignmentProgram.factors, factors,
        Fin.removeNth, Function.comp_def] using
        congrArg (fun l => l ++ [A (σ (a p))]) ih
  | @middle m n a b A P ih =>
      simpa only [compile, labels, AssignmentProgram.factors, factors] using
        congrArg (fun l => l ++ [A (σ ∘ a)]) ih
  | singleton i A P ih =>
      simpa only [compile, labels, AssignmentProgram.factors, factors,
        Fin.comp_cons, Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun l => l ++ [A (σ i)]) ih

/-- Every named label is introduced exactly once. This is the elementary
coverage condition on the first/singleton occurrences, independent of norms. -/
def CoversLabels {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointTrace 𝕜 E I J a b) : Prop := Function.Bijective P.labels

/-- The literal named global sum obeys the compiled endpoint/middle cost.
All memory identities have been proved by the compiler. -/
theorem sum_products_norm_le [Fintype I] [DecidableEq I]
    (P : EndpointTrace 𝕜 E I J (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.CoversLabels) :
    ‖∑ σ : I → J, (P.factors σ).prod‖ ≤ P.compile.cost := by
  let e : Fin P.compile.variableCount ≃ I := Equiv.ofBijective P.labels hP
  have h := P.compile.named_sum_products_norm_le e
  have hi : ∀ σ : I → J,
      P.compile.factors (fun k => σ (e k)) Fin.elim0 = P.factors σ := by
    intro σ
    have hempty : σ ∘ (Fin.elim0 : Fin 0 → I) = Fin.elim0 := Subsingleton.elim _ _
    simpa only [e, Equiv.ofBijective_apply, hempty] using P.compile_factors σ
  simpa only [hi] using h

end EndpointTrace
end Nonadditivity.NoncommutativeCS
