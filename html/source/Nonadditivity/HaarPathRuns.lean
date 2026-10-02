/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathProfiles
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # First/last markers and the corrected BC coefficient exponent

The number of middle blocks need not be at most the number of distinct
edges. The valid bound is at most the number of marked positions minus one.
Only marked factors incur a moment-order factor, so this weaker block bound
still gives the required coefficient exponent.
-/
noncomputable section
namespace Nonadditivity.HaarPathRuns
open scoped BigOperators

/-- Number of maximal false runs that end before the end of the list.
When the last flag is true, these are exactly all middle blocks. -/
def middleRuns : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a::b::l => (if a=false ∧ b=true then 1 else 0) + middleRuns (b::l)

/-- Each middle block can be charged to its following marker; the initial
marker is never charged. This is the sharp general combinatorial bound. -/
theorem middleRuns_add_head_le (l : List Bool) :
    middleRuns l + (if l.head?=some true then 1 else 0) ≤ l.count true := by
  induction l with
  | nil => simp [middleRuns]
  | cons a l ih =>
      cases l with
      | nil => cases a <;> simp [middleRuns]
      | cons b l => cases a <;> cases b <;> simp [middleRuns] at * <;> omega

theorem middleRuns_add_one_le {l : List Bool} (hhead : l.head?=some true) :
    middleRuns l + 1 ≤ l.count true := by
  simpa only [hhead,if_pos rfl] using middleRuns_add_head_le l

/-- Marked first/last visits are singleton blocks; the unmarked intervals are
middle blocks. -/
def blockCount (l : List Bool) : ℕ := l.count true + middleRuns l

/-- The combined exponent from compositions and marked coefficient factors.
This replaces the unnecessarily strong and false bound `r ≤ 3*e`. -/
theorem corrected_exponent_le {l : List Bool} {e : ℕ}
    (hhead : l.head?=some true) (hmarks : l.count true ≤ 2*e) :
    blockCount l - 1 + l.count true ≤ 6*e-2 := by
  have hr := middleRuns_add_one_le hhead
  dsimp [blockCount]
  omega

variable {E : Type*} [DecidableEq E] {n : ℕ}

/-- The first occurrence of each label. -/
def firstPositions (f : Fin n → E) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j : Fin n, j < i → f j ≠ f i

/-- The last occurrence of each label. -/
def lastPositions (f : Fin n → E) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j : Fin n, i < j → f j ≠ f i

def endpointPositions (f : Fin n → E) : Finset (Fin n) :=
  firstPositions f ∪ lastPositions f

theorem card_firstPositions_le (f : Fin n → E) :
    (firstPositions f).card ≤ (Finset.univ.image f).card := by
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro i hi j hj he
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (Finset.mem_filter.mp hj).2 i hlt he
    · exact (Finset.mem_filter.mp hi).2 j hgt he.symm

theorem card_lastPositions_le (f : Fin n → E) :
    (lastPositions f).card ≤ (Finset.univ.image f).card := by
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro i hi j hj he
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (Finset.mem_filter.mp hi).2 j hlt he.symm
    · exact (Finset.mem_filter.mp hj).2 i hgt he

/-- At most two distinguished visits per distinct edge, with singleton
occurrences counted only once. -/
theorem card_endpointPositions_le (f : Fin n → E) :
    (endpointPositions f).card ≤ 2*(Finset.univ.image f).card := by
  have h := Finset.card_union_le (firstPositions f) (lastPositions f)
  have hf := card_firstPositions_le f
  have hl := card_lastPositions_le f
  dsimp [endpointPositions]
  omega

theorem first_endpoint (f : Fin (n+1) → E) : (0 : Fin (n+1)) ∈ endpointPositions f := by
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro j hj
  exact (Fin.not_lt_zero _ hj).elim

theorem last_endpoint (f : Fin (n+1) → E) : Fin.last n ∈ endpointPositions f := by
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro j hj
  exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- The literal marker flags of a finite edge-occurrence sequence. -/
def endpointFlags (f : Fin n → E) : List Bool :=
  List.ofFn fun i => decide (i ∈ endpointPositions f)

lemma count_true_eq_sum (l : List Bool) :
    l.count true = (l.map (fun b => if b then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp [ih,Nat.add_comm]

/-- The Boolean marker count is exactly the cardinality of first/last positions. -/
theorem count_endpointFlags (f : Fin n → E) :
    (endpointFlags f).count true = (endpointPositions f).card := by
  rw [count_true_eq_sum]
  simp [endpointFlags,List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem head_endpointFlags (f : Fin (n+1) → E) :
    (endpointFlags f).head?=some true := by
  simp [endpointFlags,List.ofFn_succ,first_endpoint]

/-- The repaired BC exponent for the actual first/last markers of any
nonempty occurrence sequence. -/
theorem occurrence_exponent_le (f : Fin (n+1) → E) :
    blockCount (endpointFlags f) - 1 + (endpointFlags f).count true ≤
      6*(Finset.univ.image f).card-2 := by
  apply corrected_exponent_le (head_endpointFlags f)
  rw [count_endpointFlags]
  exact card_endpointPositions_le f

/-- The eight-position balanced-word example has four markers and three
middle blocks. Thus the generic bound `r ≤ 3*e` fails already for two edges. -/
theorem two_edge_run_counterexample :
    blockCount [true,false,false,true,false,true,false,true]=7 ∧
    3*2 < blockCount [true,false,false,true,false,true,false,true] := by
  decide

end Nonadditivity.HaarPathRuns
