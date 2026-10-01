/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathVertexNames
import Nonadditivity.HaarPathExplorationBlocks
import Nonadditivity.HaarPathCodes

/-! # Actual sparse exploration marks

The fixed-alphabet marks below are extracted from literal paths using their
first-occurrence vertex names and independent local color normalizers. No
edge of the unknown final graph is used as an encoding symbol.

This file constructs the code and its size budget. Injectivity of the sparse
code is a separate reconstruction theorem, not assumed here.
-/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- Two fixed, distinct local incidence labels. -/
def initialColor : Color 2 := (0,false)
def nextColor : Color 2 := (0,true)

def colorNormalizer (P : Path V 2 m) (hm : 0 < m) : V → Equiv.Perm (Color 2) :=
  Classical.choose (exists_local_color_normalization P hm initialColor nextColor (by decide))

def normalColor (P : Path V 2 m) (hm : 0 < m) (a : Incidence m) : Color 2 :=
  normalizedIncidenceColor P (colorNormalizer P hm) a

theorem normalColor_root (P : Path V 2 m) (hm : 0 < m) :
    normalColor P hm (⟨0,hm⟩,true)=initialColor := by
  exact (Classical.choose_spec
    (exists_local_color_normalization P hm initialColor nextColor (by decide))).1

theorem normalColor_incoming (P : Path V 2 m) (hm : 0 < m)
    (i : Fin m) (hi : P.FirstVisit i) : normalColor P hm (i,false)=initialColor := by
  exact (Classical.choose_spec
    (exists_local_color_normalization P hm initialColor nextColor (by decide))).2.1 i hi

theorem normalColor_after_firstVisit (P : Path V 2 m) (hm : 0 < m)
    (i j : Fin m) (hi : P.FirstVisit i) (hij : i.val+1=j.val) :
    normalColor P hm (j,true)=nextColor := by
  have hv : j.castSucc=i.succ := Fin.ext (by simpa using hij.symm)
  change colorNormalizer P hm (P.vertex j.castSucc) (P.colors j)=nextColor
  rw [hv]
  exact (Classical.choose_spec
    (exists_local_color_normalization P hm initialColor nextColor (by decide))).2.2 i j hi hij

/-- End of the actual old-tree run following position i. -/
def treeStop (P : Path V 2 m) (i : Fin m) : ℕ :=
  P.firstFresh (i.val+1) (P.nextImportant (i.val+1))

theorem treeStop_bounds (P : Path V 2 m) (i : Fin m) :
    i.val+1 ≤ treeStop P i ∧ treeStop P i ≤ m := by
  have hb := P.nextImportant_bounds (i.val+1) (by omega)
  have hs := P.firstFresh_bounds (i.val+1) (P.nextImportant (i.val+1)) hb.1
  exact ⟨hs.1,hs.2.trans hb.2⟩

def treeStopIndex (P : Path V 2 m) (i : Fin m) : Fin (m+1) :=
  ⟨treeStop P i,Nat.lt_succ_of_le (treeStop_bounds P i).2⟩

/-- Target, old-tree endpoint, and independent source/target/next colors. -/
def explorationMark (P : Path V 2 m) (hm : 0 < m) (i : Fin m) : ExplorationMark m :=
  (P.vertexName hm i.succ,
   P.vertexName hm (treeStopIndex P i),
   normalColor P hm (i,true),
   normalColor P hm (i,false),
   if hs : treeStop P i < m then normalColor P hm (⟨treeStop P i,hs⟩,true)
     else initialColor)

/-- Sorted actual important times with the full fixed-alphabet marks. -/
def explorationEventList (P : Path V 2 m) (hm : 0 < m) : List (ExplorationEvent m) :=
  (P.importantTimes.sort (· ≤ ·)).map fun i => (i,explorationMark P hm i)

@[simp] theorem explorationEventList_length (P : Path V 2 m) (hm : 0 < m) :
    (explorationEventList P hm).length=P.importantTimes.card := by
  simp [explorationEventList]

theorem explorationEventList_length_le (P : Path V 2 m) (hm : 0 < m) :
    (explorationEventList P hm).length ≤ P.defectTwice+2 := by
  rw [explorationEventList_length]
  exact P.card_importantTimes_le hm

def boundedExplorationCode (P : Path V 2 m) (hm : 0 < m) :
    BoundedList (ExplorationEvent m) (P.defectTwice+2) :=
  ⟨explorationEventList P hm,explorationEventList_length_le P hm⟩

@[simp] theorem explorationEventList_times (P : Path V 2 m) (hm : 0 < m) :
    (explorationEventList P hm).map Prod.fst=P.importantTimes.sort (· ≤ ·) := by
  simp [explorationEventList,List.map_map,Function.comp_def]

theorem importantTimes_eq_of_eventList_eq {P Q : Path V 2 m} (hm : 0 < m)
    (h : explorationEventList P hm=explorationEventList Q hm) :
    P.importantTimes=Q.importantTimes := by
  have he := congrArg (fun l : List (ExplorationEvent m) => (l.map Prod.fst).toFinset) h
  simpa using he

theorem explorationMark_eq_of_eventList_eq {P Q : Path V 2 m} (hm : 0 < m)
    (h : explorationEventList P hm=explorationEventList Q hm)
    (i : Fin m) (hi : i∈P.importantTimes) : explorationMark P hm i=explorationMark Q hm i := by
  have hmem : (i,explorationMark P hm i)∈explorationEventList P hm := by
    apply List.mem_map.mpr
    exact ⟨i,by simpa using hi,rfl⟩
  rw [h] at hmem
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hmem
  have hji : j=i := congrArg Prod.fst he
  subst j
  exact (congrArg Prod.snd he).symm

/-- The actual BC quotient restricted to a fixed integer defect. -/
abbrev DefectClass (V : Type*) [DecidableEq V] [Fintype V] (m δ : ℕ) (hm : 0 < m) :=
  {C : PathClass V 2 m // classDefectTwice hm C=δ}

def classRepresentative [Fintype V] {δ : ℕ} (hm : 0 < m)
    (C : DefectClass V m δ hm) : Path V 2 m := Quotient.out C.val

theorem classRepresentative_defect [Fintype V] {δ : ℕ} (hm : 0 < m)
    (C : DefectClass V m δ hm) : (classRepresentative hm C).defectTwice=δ := by
  have h := congrArg (classDefectTwice hm) (Quotient.out_eq C.val)
  exact h.trans C.property

/-- A concrete bounded sparse code for every actual defect class. Its
injectivity is established by the blockwise reconstruction in HaarPathCounting. -/
def classExplorationCode [Fintype V] {δ : ℕ} (hm : 0 < m)
    (C : DefectClass V m δ hm) : BoundedList (ExplorationEvent m) (δ+2) :=
  ⟨explorationEventList (classRepresentative hm C) hm,by
    have h := explorationEventList_length_le (classRepresentative hm C) hm
    have hd := classRepresentative_defect hm C
    omega⟩

end Nonadditivity.HaarPathClasses
