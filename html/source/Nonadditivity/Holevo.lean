/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite-ensemble variational part of the Weyl conversion

This is an actual supremum over normalized finite ensembles, rather than a
postulated Holevo equality. The ambient space can be instantiated with
Hermitian matrices. Quantum entropy bounds, output convexity, and the Weyl
orbit attaining the maximum are explicit hypotheses of the generic result;
the quantum instantiation is not proved here.
-/

noncomputable section

namespace Nonadditivity.Holevo

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure Ensemble (output : Set E) where
  size : ℕ
  weight : Fin size → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  state : Fin size → E
  state_mem : ∀ i, state i ∈ output

def Ensemble.average {output : Set E} (e : Ensemble output) : E :=
  ∑ i, e.weight i • e.state i

def Ensemble.information {output : Set E} (e : Ensemble output) (S : E → ℝ) : ℝ :=
  S e.average - ∑ i, e.weight i * S (e.state i)

def minimumEntropy (output : Set E) (S : E → ℝ) : ℝ := sInf (S '' output)

def quantity (output : Set E) (S : E → ℝ) : ℝ :=
  sSup (Set.range fun e : Ensemble output => e.information S)

theorem ensemble_information_le {output : Set E} {S : E → ℝ} {q s : ℝ}
    (e : Ensemble output) (hmin : ∀ y ∈ output, s ≤ S y)
    (hmax : S e.average ≤ q) : e.information S ≤ q - s := by
  have hsum : s ≤ ∑ i, e.weight i * S (e.state i) := by
    calc
      s = ∑ i, e.weight i * s := by rw [← Finset.sum_mul, e.weight_sum, one_mul]
      _ ≤ ∑ i, e.weight i * S (e.state i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hmin _ (e.state_mem i)) (e.weight_nonneg i)
  unfold Ensemble.information
  linarith

theorem ensemble_information_of_orbit {output : Set E} {S : E → ℝ} {q s : ℝ}
    (e : Ensemble output) (havg : S e.average = q)
    (hent : ∀ i, S (e.state i) = s) : e.information S = q - s := by
  unfold Ensemble.information
  simp_rw [hent]
  rw [← Finset.sum_mul, e.weight_sum, one_mul, havg]

/-- The variational Weyl identity. The orbit ensemble has average entropy q
and each member has the minimizing entropy s. No equality for the supremum
is assumed: the proof establishes both inequalities from finite ensembles. -/
theorem quantity_eq_of_orbit {output : Set E} {S : E → ℝ} {q s : ℝ}
    (hmin : ∀ y ∈ output, s ≤ S y)
    (hmax : ∀ e : Ensemble output, S e.average ≤ q)
    (orbit : Ensemble output) (havg : S orbit.average = q)
    (hent : ∀ i, S (orbit.state i) = s) : quantity output S = q - s := by
  have hupper : ∀ e : Ensemble output, e.information S ≤ q - s :=
    fun e => ensemble_information_le e hmin (hmax e)
  have hbound : BddAbove (Set.range fun e : Ensemble output => e.information S) :=
    ⟨q - s, by rintro _ ⟨e, rfl⟩; exact hupper e⟩
  have hattain := ensemble_information_of_orbit orbit havg hent
  apply le_antisymm
  · exact csSup_le ⟨orbit.information S, ⟨orbit, rfl⟩⟩
      (by rintro _ ⟨e, rfl⟩; exact hupper e)
  · rw [quantity, ← hattain]
    exact le_csSup hbound ⟨orbit, rfl⟩

omit [AddCommGroup E] [Module ℝ E] in
theorem minimumEntropy_le {output : Set E} {S : E → ℝ}
    (hbounded : BddBelow (S '' output)) {y : E} (hy : y ∈ output) :
    minimumEntropy output S ≤ S y := csInf_le hbounded ⟨y, hy, rfl⟩

/-- Rephrasing the orbit identity with the actual infimum definition. -/
theorem quantity_eq_sub_minimumEntropy {output : Set E} {S : E → ℝ} {q : ℝ}
    (hbounded : BddBelow (S '' output))
    (hmax : ∀ e : Ensemble output, S e.average ≤ q)
    (orbit : Ensemble output) (havg : S orbit.average = q)
    (hent : ∀ i, S (orbit.state i) = minimumEntropy output S) :
    quantity output S = q - minimumEntropy output S :=
  quantity_eq_of_orbit (fun _ hy => minimumEntropy_le hbounded hy) hmax orbit havg hent

/-- Minimum entropy is unchanged by closing a set of outputs under mixtures,
provided S satisfies its concavity inequality on every ensemble. -/
theorem mixture_minimumEntropy {output : Set E} {S : E → ℝ}
    (hbounded : BddBelow (S '' output))
    (hconcave : ∀ e : Ensemble output,
      (∑ i, e.weight i * S (e.state i)) ≤ S e.average)
    {e : Ensemble output} : minimumEntropy output S ≤ S e.average := by
  have hsum : minimumEntropy output S ≤ ∑ i, e.weight i * S (e.state i) := by
    calc
      minimumEntropy output S = ∑ i, e.weight i * minimumEntropy output S := by
        rw [← Finset.sum_mul, e.weight_sum, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (minimumEntropy_le hbounded (e.state_mem i)) (e.weight_nonneg i))
  exact hsum.trans (hconcave e)

end Nonadditivity.Holevo
