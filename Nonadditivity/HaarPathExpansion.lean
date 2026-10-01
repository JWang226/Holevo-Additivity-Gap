/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathWeights

/-! # Exact matrix-word expansion into closed Haar paths

The finite matrix trace is expanded into the literal path products bounded
in `HaarPathWeights`; no probabilistic estimate is assumed in this expansion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathExpansion
open HaarModel HaarFourthMoments HaarPathWeights MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

def chainProduct {m : ℕ} (A : Fin m → Matrix V V ℂ) (x : Fin (m+1) → V) : ℂ :=
  ∏ i, A i (x i.castSucc) (x i.succ)

omit [DecidableEq V] in
lemma sum_functions_succ {m : ℕ} (f : (Fin (m+1) → V) → ℂ) :
    ∑ x, f x = ∑ a, ∑ y : Fin m → V, f (Fin.cons a y) := by
  have h := (Fin.consEquiv (fun _ : Fin (m+1) => V)).sum_comp f
  simpa only [Fintype.sum_prod_type, Fin.consEquiv_apply] using h.symm

omit [Fintype V] [DecidableEq V] in
lemma chainProduct_cons {m : ℕ} (A : Fin (m+1) → Matrix V V ℂ)
    (a b : V) (x : Fin m → V) :
    chainProduct A (Fin.cons a (Fin.cons b x)) =
      A 0 a b * chainProduct (fun i => A i.succ) (Fin.cons b x) := by
  simp [chainProduct, Fin.prod_univ_succ, Fin.castSucc_succ]

/-- Exact endpoint expansion of an arbitrary finite ordered matrix product. -/
theorem matrixProduct_entry {m : ℕ} (A : Fin m → Matrix V V ℂ) (a b : V) :
    (List.ofFn A).prod a b =
      ∑ x : Fin m → V, chainProduct A (Fin.cons a x) *
        (if (Fin.cons a x : Fin (m+1) → V) (Fin.last m)=b then 1 else 0) := by
  induction m generalizing a b with
  | zero => simp [chainProduct, Matrix.one_apply]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply, sum_functions_succ]
    simp_rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro x _
    rw [chainProduct_cons]
    simp only [Fin.cons_last]
    ring

/-- The trace is the sum over precisely the closed vertex assignments. -/
theorem matrixProduct_trace {m : ℕ} (A : Fin m → Matrix V V ℂ) :
    (List.ofFn A).prod.trace =
      ∑ x : Fin (m+1) → V, if x (Fin.last m)=x 0 then chainProduct A x else 0 := by
  rw [Matrix.trace, sum_functions_succ]
  apply Finset.sum_congr rfl
  intro a _
  change (List.ofFn A).prod a a = _
  rw [matrixProduct_entry]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Fin.cons_zero]
  split_ifs <;> simp_all

/-- Closed assignments include the chosen starting vertex. -/
abbrev ClosedAssignment (V : Type*) (m : ℕ) :=
  {x : Fin (m+1) → V // x (Fin.last m)=x 0}

/-- A fixed reduced word and a closed vertex assignment form the exact path
object used by the graph estimates. -/
def assignmentPath {m : ℕ} (c : Fin m → HaarPathProfiles.Color 2)
    (hc : ∀ i j : Fin m, i.val+1=j.val → c j ≠ HaarPathGraph.flipColor (c i))
    (x : ClosedAssignment V m) : HaarPathGraph.Path V 2 m where
  vertex := x.val
  colors := c
  closed := x.property
  reduced := hc

/-- Subtype version, without a zero-valued contribution for open paths. -/
theorem matrixProduct_trace_closed {m : ℕ} (A : Fin m → Matrix V V ℂ) :
    (List.ofFn A).prod.trace = ∑ x : ClosedAssignment V m, chainProduct A x.val := by
  rw [matrixProduct_trace, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) _

def pairGenerator {N : ℕ} (U : LocalUnitary N × LocalUnitary N) (a : Fin 2) :
    LocalUnitary N := if a=0 then U.1 else U.2

def letterMatrix {N : ℕ} (U : LocalUnitary N × LocalUnitary N)
    (c : HaarPathProfiles.Color 2) : Mat N :=
  if c.2 then (pairGenerator U c.1 : Mat N) else (pairGenerator U c.1 : Mat N)ᴴ

/-- Exact equality between a free-word evaluation and its ordered letter matrices. -/
theorem word_eval_eq_matrixProduct {N : ℕ} (U : LocalUnitary N × LocalUnitary N)
    (L : List (HaarPathProfiles.Color 2)) :
    ((FreeGroup.lift (pairGenerator U) (FreeGroup.mk L) : LocalUnitary N) : Mat N) =
      (L.map (letterMatrix U)).prod := by
  induction L with
  | nil => simp [FreeGroup.lift_mk]
  | cons c L ih =>
    rw [HaarWordPhase.eval_cons, ih]
    rfl

/-- The actual Haar word trace is a sum of the actual closed path products. -/
theorem word_trace_eq_sum_pathProduct {N m : ℕ}
    (c : Fin m → HaarPathProfiles.Color 2)
    (hc : ∀ i j : Fin m, i.val+1=j.val → c j ≠ HaarPathGraph.flipColor (c i))
    (U : LocalUnitary N × LocalUnitary N) :
    (((FreeGroup.lift (pairGenerator U) (FreeGroup.mk (List.ofFn c)) : LocalUnitary N) : Mat N).trace) =
      ∑ x : ClosedAssignment (Fin (N+1)) m, pathProduct (assignmentPath c hc x) U := by
  rw [word_eval_eq_matrixProduct, List.map_ofFn, matrixProduct_trace_closed]
  simp only [chainProduct, letterMatrix, pathProduct, assignmentPath,
    pairGenerator, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> rfl

/-- Every individual path product is a continuous function of the two Haar
matrices, supplying the integrability required for the exact finite expansion. -/
theorem continuous_pathProduct {N m : ℕ}
    (P : HaarPathGraph.Path (Fin (N+1)) 2 m) : Continuous (pathProduct P) := by
  change Continuous (fun U => pathProduct P U)
  simp_rw [pathProduct_eq, signedProduct_eq, listMonomial_eq_entryMonomial]
  exact ((HaarInvariantTensor.continuous_entryMonomial _ _ _ _).comp continuous_fst).mul
    ((HaarInvariantTensor.continuous_entryMonomial _ _ _ _).comp continuous_snd)

theorem integrable_pathProduct {N m : ℕ}
    (P : HaarPathGraph.Path (Fin (N+1)) 2 m) :
    Integrable (pathProduct P) ((haar N).prod (haar N)) :=
  (continuous_pathProduct P).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact expected trace expansion. This is the analytic interface between
matrix moments and the path-class estimates. -/
theorem integral_word_trace_eq_sum_pathProduct {N m : ℕ}
    (c : Fin m → HaarPathProfiles.Color 2)
    (hc : ∀ i j : Fin m, i.val+1=j.val → c j ≠ HaarPathGraph.flipColor (c i)) :
    (∫ U : LocalUnitary N × LocalUnitary N,
      (((FreeGroup.lift (pairGenerator U) (FreeGroup.mk (List.ofFn c)) : LocalUnitary N) : Mat N).trace)
      ∂(haar N).prod (haar N)) =
      ∑ x : ClosedAssignment (Fin (N+1)) m,
        ∫ U : LocalUnitary N × LocalUnitary N,
          pathProduct (assignmentPath c hc x) U ∂(haar N).prod (haar N) := by
  simp_rw [word_trace_eq_sum_pathProduct c hc]
  exact integral_finset_sum _ (fun x _ => integrable_pathProduct (assignmentPath c hc x))

end Nonadditivity.HaarPathExpansion
