/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTransport

/-! # Reconstructing an actual path from compatible dart colors

The local signed-color equality pattern and reversal compatibility suffice to
recolor the literal path. Reducedness follows from the original reduced walk;
the result belongs to its actual coarse path class.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarPathRecoloring
open HaarPathGraph HaarPathProfiles HaarPathClasses
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
variable (P : Path V d m) (κ : {q // q∈P.darts} → Color d)
variable (hrev : ∀ q : {q // q∈P.darts},
  κ ⟨reverse q.val,P.reverse_mem q.property⟩=flipColor (κ q))
variable (hkernel : ∀ q r : {q // q∈P.darts}, source q.val=source r.val →
  (κ q=κ r ↔ color q.val=color r.val))
include hrev hkernel

def recolorPath : Path V d m where
  vertex := P.vertex
  colors i := κ ⟨P.traversal i,P.traversal_mem i⟩
  closed := P.closed
  reduced i j hij := by
    intro he
    have hs : source (P.traversal j)=source (reverse (P.traversal i)) := by
      simp only [Path.traversal,source_dart,source_reverse_dart]
      exact congrArg P.vertex (Fin.ext hij.symm)
    have hk : κ ⟨P.traversal j,P.traversal_mem j⟩=
        κ ⟨reverse (P.traversal i),P.reverse_mem (P.traversal_mem i)⟩ := by
      rw [hrev ⟨P.traversal i,P.traversal_mem i⟩]
      exact he
    have hc := (hkernel ⟨P.traversal j,P.traversal_mem j⟩
      ⟨reverse (P.traversal i),P.reverse_mem (P.traversal_mem i)⟩ hs).mp hk
    exact P.reduced i j hij (by simpa only [Path.traversal,color_dart,color_reverse_dart] using hc)

@[simp] theorem recolorPath_vertex : (recolorPath P κ hrev hkernel).vertex=P.vertex := rfl

@[simp] theorem recolorPath_colors (i : Fin m) :
    (recolorPath P κ hrev hkernel).colors i=κ ⟨P.traversal i,P.traversal_mem i⟩ := rfl

theorem recolorPath_incidenceVertex (a : Incidence m) :
    incidenceVertex (recolorPath P κ hrev hkernel) a=incidenceVertex P a := rfl

theorem recolorPath_incidenceColor (a : Incidence m) :
    incidenceColor (recolorPath P κ hrev hkernel) a=
      κ ⟨incidenceDart P a,incidenceDart_mem P a⟩ := by
  obtain ⟨i,b⟩ := a
  cases b
  · simpa only [incidenceColor,incidenceDart,Bool.false_eq_true,ite_false,recolorPath]
      using (hrev ⟨P.traversal i,P.traversal_mem i⟩).symm
  · rfl

/-- This is membership in the literal path equivalence relation, including
the local signed-color equality kernels at both ends of every traversal. -/
theorem recolorPath_samePattern : SamePattern P (recolorPath P κ hrev hkernel) := by
  constructor
  · intro i j
    rfl
  · intro a b hv
    rw [recolorPath_incidenceColor,recolorPath_incidenceColor]
    simpa only [color_incidenceDart] using (hkernel ⟨incidenceDart P a,incidenceDart_mem P a⟩
      ⟨incidenceDart P b,incidenceDart_mem P b⟩
      (by simpa only [source_incidenceDart] using hv)).symm

/-- The induced dart map changes the signed color and retains both literal
vertex endpoints. -/
theorem recolorPath_dartPerm (q : {q // q∈P.darts}) :
    (recolorPath_samePattern P κ hrev hkernel).dartPerm q.val=
      dart (source q.val) (κ q) (source (reverse q.val)) := by
  let h := recolorPath_samePattern P κ hrev hkernel
  obtain ⟨a,ha⟩ := exists_incidenceDart P q.property
  have hq : (⟨incidenceDart P a,incidenceDart_mem P a⟩ : {q // q∈P.darts})=q :=
    Subtype.ext ha
  rw [←ha,h.dartPerm_apply]
  apply (dart_eq_iff_source_color_target _ _).mpr
  refine ⟨?_,?_,?_⟩
  · simp only [source_incidenceDart,source_dart,recolorPath_incidenceVertex]
  · simp only [color_incidenceDart,color_dart,recolorPath_incidenceColor,hq]
  · rw [←incidenceDart_flip,source_incidenceDart,source_reverse_dart,
      ←incidenceDart_flip,source_incidenceDart,recolorPath_incidenceVertex]

end Nonadditivity.HaarPathRecoloring
