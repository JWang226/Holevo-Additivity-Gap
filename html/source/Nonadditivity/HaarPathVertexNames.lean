/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClassData
import Nonadditivity.HaarPathColorNormalization

/-! # Canonical vertex names by first appearance

Names are positions in the original length-m path, so they lie in `Fin m`.
A newly discovered vertex is named by its first arrival time. This gives a
fixed alphabet for sparse exploration marks without final-graph indexing.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathGraph HaarPathProfiles HaarPathClasses
variable {V : Type*} [DecidableEq V] {d m : ℕ}

variable (P : Path V d m) (hm : 0 < m)
include hm

/-- All visited vertices, including the terminal vertex, occur before time m. -/
lemma earlier_occurrence (j : Fin (m+1)) :
    ∃ i : Fin m, P.vertex i.castSucc=P.vertex j := by
  by_cases hj : j.val < m
  · exact ⟨⟨j.val,hj⟩,congrArg P.vertex (Fin.ext rfl)⟩
  · have he : j=Fin.last m := Fin.ext (by simp; omega)
    refine ⟨⟨0,hm⟩,?_⟩
    simpa only [he,Fin.castSucc_mk,Fin.mk_zero,P.closed]

def occurrenceSet (j : Fin (m+1)) : Finset (Fin m) :=
  Finset.univ.filter fun i => P.vertex i.castSucc=P.vertex j

lemma occurrenceSet_nonempty (j : Fin (m+1)) : (P.occurrenceSet j).Nonempty := by
  obtain ⟨i,hi⟩ := P.earlier_occurrence hm j
  exact ⟨i,by simp [occurrenceSet,hi]⟩

/-- The least actual occurrence is the vertex's canonical name. -/
def vertexName (j : Fin (m+1)) : Fin m :=
  (P.occurrenceSet j).min' (P.occurrenceSet_nonempty hm j)

lemma vertexName_spec (j : Fin (m+1)) :
    P.vertex (P.vertexName hm j).castSucc=P.vertex j := by
  exact (Finset.mem_filter.mp ((P.occurrenceSet j).min'_mem
    (P.occurrenceSet_nonempty hm j))).2

lemma vertexName_le (j : Fin (m+1)) (i : Fin m)
    (hi : P.vertex i.castSucc=P.vertex j) : P.vertexName hm j ≤ i := by
  exact (P.occurrenceSet j).min'_le i (by simp [occurrenceSet,hi])

/-- Names retain exactly the equality pattern of the vertices. -/
theorem vertexName_eq_iff (i j : Fin (m+1)) :
    P.vertexName hm i=P.vertexName hm j ↔ P.vertex i=P.vertex j := by
  constructor
  · intro h
    exact (P.vertexName_spec hm i).symm.trans
      ((congrArg (fun x : Fin m => P.vertex x.castSucc) h).trans (P.vertexName_spec hm j))
  · intro h
    apply le_antisymm
    · exact P.vertexName_le hm i _ ((P.vertexName_spec hm j).trans h.symm)
    · exact P.vertexName_le hm j _ ((P.vertexName_spec hm i).trans h)

@[simp] theorem vertexName_root : P.vertexName hm 0=⟨0,hm⟩ := by
  have h := P.vertexName_le hm 0 ⟨0,hm⟩ rfl
  apply Fin.ext
  change (P.vertexName hm 0).val=0
  have hv : (P.vertexName hm 0).val ≤ 0 := h
  omega

theorem vertexName_le_time (i : Fin m) : (P.vertexName hm i.castSucc).val ≤ i.val :=
  P.vertexName_le hm i.castSucc i rfl

/-- The new name is the current arrival time, with no choice or relabelling
of previously decoded vertices. -/
theorem vertexName_of_firstVisit {i : Fin m} (hi : P.FirstVisit i) :
    (P.vertexName hm i.succ).val=i.val+1 := by
  let j : Fin m := ⟨i.val+1,P.firstVisit_not_last hi⟩
  have hj : j.castSucc=i.succ := Fin.ext rfl
  have hle := P.vertexName_le hm i.succ j (congrArg P.vertex hj)
  have hvle : (P.vertexName hm i.succ).val ≤ i.val+1 := hle
  have hgt : i.val < (P.vertexName hm i.succ).val := by
    by_contra h
    exact hi (P.vertexName hm i.succ).castSucc (by simp; omega)
      (P.vertexName_spec hm i.succ)
  omega

/-- Renaming the vertices produces another genuine literal path. Its color
word is unchanged; independent endpoint color labels are tracked separately. -/
def namedPath : Path (Fin m) d m where
  vertex := P.vertexName hm
  colors := P.colors
  closed := (P.vertexName_eq_iff hm _ _).mpr P.closed
  reduced := P.reduced

theorem namedPath_firstVisit_iff (i : Fin m) :
    (P.namedPath hm).FirstVisit i ↔ P.FirstVisit i := by
  simp only [Path.FirstVisit,namedPath]
  constructor
  · intro h j hj he
    exact h j hj ((P.vertexName_eq_iff hm j i.succ).mpr he)
  · intro h j hj he
    exact h j hj ((P.vertexName_eq_iff hm j i.succ).mp he)

theorem namedPath_firstTimes : (P.namedPath hm).firstTimes=P.firstTimes := by
  ext i
  simp only [Path.mem_firstTimes,P.namedPath_firstVisit_iff hm]

theorem namedPath_edgeAt_eq_iff (i j : Fin m) :
    (P.namedPath hm).edgeAt i=(P.namedPath hm).edgeAt j ↔ P.edgeAt i=P.edgeAt j := by
  simp only [Path.edgeAt,namedPath,edge_eq_iff,P.vertexName_eq_iff hm]

theorem namedPath_importantTimes : (P.namedPath hm).importantTimes=P.importantTimes := by
  ext i
  simp only [Path.importantTimes,Finset.mem_filter,Finset.mem_univ,true_and,
    Path.treeEdges,Finset.mem_image,P.namedPath_firstTimes hm,P.namedPath_edgeAt_eq_iff hm]

end Nonadditivity.HaarPathGraph.Path

namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {d m : ℕ}

/-- Matching vertex names and independently normalized incidence colors
reconstructs the complete actual path equivalence class. The normal form
need not itself obey a global inverse-color convention. -/
theorem samePattern_of_named_data {P Q : Path V d m} (hm : 0 < m)
    (β γ : V → Equiv.Perm (Color d))
    (hv : ∀ j, P.vertexName hm j=Q.vertexName hm j)
    (hc : ∀ a, β (incidenceVertex P a) (incidenceColor P a)=
      γ (incidenceVertex Q a) (incidenceColor Q a)) : SamePattern P Q := by
  have hv' (i j : Fin (m+1)) : P.vertex i=P.vertex j ↔ Q.vertex i=Q.vertex j := by
    rw [←P.vertexName_eq_iff hm i j,←Q.vertexName_eq_iff hm i j,hv i,hv j]
  refine ⟨hv',fun a b hab => ?_⟩
  have hab' : incidenceVertex Q a=incidenceVertex Q b := by
    simpa only [incidenceVertex_eq] using
      (hv' (incidenceIndex a) (incidenceIndex b)).mp
        (by simpa only [incidenceVertex_eq] using hab)
  rw [←(β (incidenceVertex P b)).injective.eq_iff,←hab,
    hc a,hab,hc b,hab']
  exact (γ (incidenceVertex Q b)).injective.eq_iff

end Nonadditivity.HaarPathClasses
