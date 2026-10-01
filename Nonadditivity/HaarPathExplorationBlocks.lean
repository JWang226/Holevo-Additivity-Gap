/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTree

/-! # The actual old-tree / fresh-run decomposition of exploration blocks

The endpoints and the switch time are minima of finite sets extracted from
the path itself. No block decomposition is supplied as a hypothesis.
-/

noncomputable section
namespace Nonadditivity.HaarPathGraph.Path

variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- Important traversals at or after `a`, together with the final sentinel. -/
def importantStops (a : ℕ) : Finset ℕ :=
  insert m ((P.importantTimes.filter fun i => a ≤ i.val).image Fin.val)

def nextImportant (a : ℕ) : ℕ :=
  (P.importantStops a).min' ⟨m,Finset.mem_insert_self _ _⟩

theorem nextImportant_mem (a : ℕ) : P.nextImportant a∈P.importantStops a :=
  Finset.min'_mem _ _

theorem nextImportant_bounds (a : ℕ) (ha : a ≤ m) :
    a ≤ P.nextImportant a ∧ P.nextImportant a ≤ m := by
  constructor
  · have h := P.nextImportant_mem a
    rcases Finset.mem_insert.mp h with h | h
    · simpa [h] using ha
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
      exact he ▸ (Finset.mem_filter.mp hi).2
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem not_important_before_next (a : ℕ) (i : Fin m)
    (hai : a ≤ i.val) (hi : i.val<P.nextImportant a) : i∉P.importantTimes := by
  intro himp
  have hm : i.val∈P.importantStops a := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨himp,hai⟩,rfl⟩)
  have hmin : P.nextImportant a ≤ i.val := Finset.min'_le _ _ hm
  omega

theorem nextImportant_is_important (a : ℕ) (hb : P.nextImportant a<m) :
    (⟨P.nextImportant a,hb⟩ : Fin m)∈P.importantTimes := by
  have h := P.nextImportant_mem a
  rcases Finset.mem_insert.mp h with h | h
  · omega
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hei : i=⟨P.nextImportant a,hb⟩ := Fin.ext he
    simpa only [←hei] using (Finset.mem_filter.mp hi).1

/-- Candidate fresh-run starts in `[a,b)`, with `b` for an empty fresh run. -/
def freshStops (a b : ℕ) : Finset ℕ :=
  insert b ((P.firstTimes.filter fun i => a ≤ i.val ∧ i.val<b).image Fin.val)

def firstFresh (a b : ℕ) : ℕ :=
  (P.freshStops a b).min' ⟨b,Finset.mem_insert_self _ _⟩

theorem firstFresh_mem (a b : ℕ) : P.firstFresh a b∈P.freshStops a b :=
  Finset.min'_mem _ _

theorem firstFresh_bounds (a b : ℕ) (hab : a ≤ b) :
    a ≤ P.firstFresh a b ∧ P.firstFresh a b ≤ b := by
  constructor
  · have h := P.firstFresh_mem a b
    rcases Finset.mem_insert.mp h with h | h
    · simpa [h] using hab
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
      exact he ▸ (Finset.mem_filter.mp hi).2.1
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem firstFresh_is_firstVisit (a b : ℕ) (hb : b ≤ m)
    (hs : P.firstFresh a b<b) :
    P.FirstVisit ⟨P.firstFresh a b,hs.trans_le hb⟩ := by
  have h := P.firstFresh_mem a b
  rcases Finset.mem_insert.mp h with h | h
  · omega
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hei : i=⟨P.firstFresh a b,hs.trans_le hb⟩ := Fin.ext he
    simpa only [←hei] using (P.mem_firstTimes i).mp (Finset.mem_filter.mp hi).1

theorem not_firstVisit_before_firstFresh (a b : ℕ) (hab : a ≤ b) (i : Fin m)
    (hai : a ≤ i.val) (hi : i.val<P.firstFresh a b) : ¬P.FirstVisit i := by
  intro hfirst
  have hib : i.val<b := hi.trans_le (P.firstFresh_bounds a b hab).2
  have hm : i.val∈P.freshStops a b := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
      ⟨(P.mem_firstTimes i).mpr hfirst,hai,hib⟩,rfl⟩)
  have hmin : P.firstFresh a b ≤ i.val := Finset.min'_le _ _ hm
  omega

/-- Once a first visit occurs, every following step before the next important
traversal is a first visit. -/
theorem firstVisit_propagates (a b : ℕ)
    (hno : ∀ i : Fin m, a ≤ i.val → i.val<b → i∉P.importantTimes)
    (i j : Fin m) (hai : a ≤ i.val) (hi : P.FirstVisit i)
    (hij : i.val ≤ j.val) (hjb : j.val<b) : P.FirstVisit j := by
  have hmain : ∀ k, i.val ≤ k → ∀ hk : k<m, k<b → P.FirstVisit ⟨k,hk⟩ := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base =>
        intro hk hb
        simpa using hi
    | succ k hik ih =>
        intro hk hb
        let u : Fin m := ⟨k,by omega⟩
        let v : Fin m := ⟨k+1,hk⟩
        have hu : P.FirstVisit u := ih u.isLt (by omega)
        rcases P.firstVisit_next hu (show u.val+1=v.val from rfl) with hv | hv
        · exact hv
        · exact (hno v (by dsimp [v]; omega) hb hv).elim
  exact hmain j.val hij j.isLt hjb

/-- The exact old-tree/fresh-run split inside an interval with no important
traversal. The switch is the computed minimum `firstFresh`. -/
theorem exploration_interval_split (a b : ℕ) (hab : a ≤ b) (hb : b ≤ m)
    (hno : ∀ i : Fin m, a ≤ i.val → i.val<b → i∉P.importantTimes) :
    (a ≤ P.firstFresh a b ∧ P.firstFresh a b ≤ b) ∧
    (∀ i : Fin m, a ≤ i.val → i.val<P.firstFresh a b →
      ¬P.FirstVisit i ∧ P.edgeAt i∈P.treeEdges) ∧
    (∀ i : Fin m, P.firstFresh a b ≤ i.val → i.val<b → P.FirstVisit i) := by
  have hbounds := P.firstFresh_bounds a b hab
  refine ⟨hbounds,?_,?_⟩
  · intro i hai hi
    refine ⟨P.not_firstVisit_before_firstFresh a b hab i hai hi,?_⟩
    have himp := hno i hai (hi.trans_le hbounds.2)
    simpa only [importantTimes, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] using himp
  · intro i hsi hib
    have hsb : P.firstFresh a b<b := hsi.trans_lt hib
    let j : Fin m := ⟨P.firstFresh a b,hsb.trans_le hb⟩
    exact P.firstVisit_propagates a b hno j i hbounds.1
      (P.firstFresh_is_firstVisit a b hb hsb) hsi hib

/-- Actual decomposition after any starting time, in particular immediately
after an important traversal. Both the next endpoint and the switch are
computed from the path. -/
theorem exploration_block_split (a : ℕ) (ha : a ≤ m) :
    let b := P.nextImportant a
    let s := P.firstFresh a b
    (a ≤ s ∧ s ≤ b) ∧
    (∀ i : Fin m, a ≤ i.val → i.val<s → ¬P.FirstVisit i ∧ P.edgeAt i∈P.treeEdges) ∧
    (∀ i : Fin m, s ≤ i.val → i.val<b → P.FirstVisit i) := by
  exact P.exploration_interval_split a (P.nextImportant a)
    (P.nextImportant_bounds a ha).1 (P.nextImportant_bounds a ha).2
    (P.not_important_before_next a)

/-- A tree edge at the initial step must itself be a discovery edge. -/
theorem firstVisit_zero_of_not_important (hm : 0<m)
    (hzero : (⟨0,hm⟩ : Fin m)∉P.importantTimes) : P.FirstVisit ⟨0,hm⟩ := by
  have ht : P.edgeAt ⟨0,hm⟩∈P.treeEdges := by
    simpa only [importantTimes, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] using hzero
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp ht
  have hfirst := (P.mem_firstTimes i).mp hi
  by_cases hi0 : i.val=0
  · have hei : i=⟨0,hm⟩ := Fin.ext hi0
    simpa only [←hei] using hfirst
  · exact (P.firstVisit_edge_not_earlier hfirst (by simp; omega) he.symm).elim

/-- Every step before the first important traversal discovers a new vertex. -/
theorem initial_prefix_firstVisit (i : Fin m) (hi : i.val<P.nextImportant 0) :
    P.FirstVisit i := by
  have hm : 0<m := Nat.zero_lt_of_lt i.isLt
  have hz : (⟨0,hm⟩ : Fin m)∉P.importantTimes :=
    P.not_important_before_next 0 ⟨0,hm⟩ (by simp) (by simp; omega)
  exact P.firstVisit_propagates 0 (P.nextImportant 0)
    (P.not_important_before_next 0) ⟨0,hm⟩ i (by simp)
    (P.firstVisit_zero_of_not_important hm hz) (by simp) hi

end Nonadditivity.HaarPathGraph.Path
