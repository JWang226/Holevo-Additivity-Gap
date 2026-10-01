/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarIteratedExpectation
import Nonadditivity.HaarTensorEvaluation
import Mathlib.MeasureTheory.Integral.Prod

/-! # The iterated integrals are finite tensor-matrix moments

This identifies repeated partial substitution with a genuine finite tensor
representation on one product probability space. Reindexing bases and Fubini
introduce no change in norms or probability laws.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarIteratedMoments
open MeasureTheory HaarModel HaarWordExpansion HaarTensorReplacement
open ProductHaagerupProduct
open scoped BigOperators Matrix Matrix.Norms.L2Operator

def TensorIndex (N : ℕ) : ℕ → Type
  | 0 => PUnit
  | j+1 => Fin (N+1) × TensorIndex N j

instance tensorIndexFintype (N : ℕ) : (j : ℕ) → Fintype (TensorIndex N j)
  | 0 => inferInstanceAs (Fintype PUnit)
  | j+1 => @instFintypeProd _ _ inferInstance (tensorIndexFintype N j)

instance tensorIndexDecidableEq (N : ℕ) : (j : ℕ) → DecidableEq (TensorIndex N j)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | j+1 => @instDecidableEqProd _ _ inferInstance (tensorIndexDecidableEq N j)

def recursiveRepresentation (N : ℕ) : (j : ℕ) → (Fin j → Pair N) →
    GroupIndex (Fin 2) j →* Matrix (TensorIndex N j) (TensorIndex N j) ℂ
  | 0, _ => 1
  | j+1, U => productRepresentation (representationMatrix (pairRepresentation N (U 0)))
      (recursiveRepresentation N j (fun r => U r.succ))

def recursiveMeasure (N j : ℕ) : Measure (Fin j → Pair N) :=
  Measure.pi (fun _ => pairMeasure N)

instance recursiveProbability (N j : ℕ) : IsProbabilityMeasure (recursiveMeasure N j) := by
  unfold recursiveMeasure
  infer_instance

theorem continuous_recursiveRepresentation (N j : ℕ) (g : GroupIndex (Fin 2) j) :
    Continuous (fun U : Fin j → Pair N => recursiveRepresentation N j U g) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    apply continuous_matrix
    intro a b
    change Continuous (fun U : Fin (j+1) → Pair N =>
      (pairRepresentation N (U 0) g.1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a.1 b.1 *
        recursiveRepresentation N j (fun r => U r.succ) g.2 a.2 b.2)
    apply Continuous.mul
    · exact ((continuous_pairRepresentation N g.1).comp (continuous_apply 0)).matrix_elem _ _
    · exact ((ih g.2).comp (continuous_pi (fun r => continuous_apply r.succ))).matrix_elem _ _

theorem continuous_finiteEval {G ι ν Ω : Type} [Group G] [DecidableEq G]
    [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] [TopologicalSpace Ω]
    (ρ : Ω → G →* Matrix ν ν ℂ) (hρ : ∀ g, Continuous (fun U => ρ U g))
    (f : MatrixPolynomial G ι) : Continuous (fun U => finiteEval (ρ U) f) := by
  simp only [finiteEval_eq_sum]
  apply continuous_finset_sum
  intro g hg
  apply continuous_matrix
  intro a b
  exact continuous_const.mul ((hρ g).matrix_elem a.2 b.2)

theorem recursive_finiteEval_cons_norm {N j : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Pair N) (V : Fin j → Pair N) (f : MatrixPolynomial (GroupIndex (Fin 2) (j+1)) ι) :
    ‖finiteEval (recursiveRepresentation N (j+1) (Fin.cons U V)) f‖ =
      ‖finiteEval (recursiveRepresentation N j V)
        (partialEval (representationMatrix (pairRepresentation N U)) f)‖ := by
  simp only [recursiveRepresentation, Fin.cons_zero, Fin.cons_succ]
  exact (finiteEval_partial_norm _ _ _).symm

theorem recursiveMoment_eq_iteratedMoment (N p j : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) j) ι) :
    (∫ U : Fin j → Pair N, ‖finiteEval (recursiveRepresentation N j U) f‖^p
      ∂recursiveMeasure N j) = iteratedMoment N p j f := by
  induction j generalizing ι with
  | zero =>
    letI : Unique (GroupIndex (Fin 2) 0) := inferInstanceAs (Unique PUnit)
    have hn : ∀ U : Fin 0 → Pair N,
        ‖finiteEval (recursiveRepresentation N 0 U) f‖ = ‖regularEval f‖ :=
      fun U => finiteEval_trivial_norm f
    simp only [hn, integral_const, measureReal_univ_eq_one, one_smul, iteratedMoment]
  | succ j ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j+1) => Pair N) 0
    have hpres : MeasurePreserving e (recursiveMeasure N (j+1))
        ((pairMeasure N).prod (recursiveMeasure N j)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (j+1) => pairMeasure N) 0
    have he : ∀ x : Pair N × (Fin j → Pair N), e.symm x = Fin.cons x.1 x.2 := by
      intro x
      ext r
      refine Fin.cases ?_ (fun s => ?_) r <;> simp [e]
    let F := fun U : Fin (j+1) → Pair N =>
      ‖finiteEval (recursiveRepresentation N (j+1) U) f‖^p
    have hcont : Continuous F :=
      ((continuous_finiteEval _ (continuous_recursiveRepresentation N (j+1)) f).norm).pow p
    have hcons : Continuous (fun x : Pair N × (Fin j → Pair N) => (Fin.cons x.1 x.2 : Fin (j+1) → Pair N)) := by
      apply continuous_pi
      intro r
      refine Fin.cases ?_ (fun s => ?_) r
      · simpa only [Fin.cons_zero] using continuous_fst
      · simpa only [Fin.cons_succ] using (continuous_apply s).comp continuous_snd
    have hint : Integrable (fun x : Pair N × (Fin j → Pair N) => F (e.symm x))
        ((pairMeasure N).prod (recursiveMeasure N j)) := by
      simp only [he]
      exact (hcont.comp hcons).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← hpres.symm.integral_comp' F, integral_prod _ hint]
    change (∫ U : Pair N, ∫ V : Fin j → Pair N, F (e.symm (U,V))
      ∂recursiveMeasure N j ∂pairMeasure N) = _
    simp only [he, F, recursive_finiteEval_cons_norm]
    simp only [ih, iteratedMoment]

end Nonadditivity.HaarIteratedMoments
