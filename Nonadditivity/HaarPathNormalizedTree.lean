/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTreeSegment
import Nonadditivity.HaarPathVertexNames

/-! # Endpoint reconstruction of actual old-tree intervals -/
noncomputable section
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathGraph HaarPathProfiles HaarPathClasses
variable {V : Type*} [DecidableEq V] {d m : ℕ}

theorem discoveryGraph_eq_of_vertex_prefix (P Q : Path V d m) (a : ℕ)
    (hv : ∀ j : Fin (m+1), j.val ≤ a → P.vertex j=Q.vertex j) :
    P.discoveryGraph a=Q.discoveryGraph a := by
  have hf (i : Fin m) (hi : i.val<a) : P.FirstVisit i ↔ Q.FirstVisit i := by
    constructor
    · intro hp j hj
      rw [← hv j (by omega), ← hv i.succ (by simp; omega)]
      exact hp j hj
    · intro hq j hj
      rw [hv j (by omega), hv i.succ (by simp; omega)]
      exact hq j hj
  ext x y
  constructor
  · rintro ⟨i,hi,hia,hxy⟩
    refine ⟨i,(hf i hia).mp hi,hia,?_⟩
    simpa only [hv i.castSucc (by simp; omega),hv i.succ (by simp; omega)] using hxy
  · rintro ⟨i,hi,hia,hxy⟩
    refine ⟨i,(hf i hia).mpr hi,hia,?_⟩
    simpa only [hv i.castSucc (by simp; omega),hv i.succ (by simp; omega)] using hxy

/-- An old-tree interval is determined by the decoded tree and its endpoint,
including the interval length. -/
theorem old_tree_segment_reconstruction (P Q : Path V d m) (a lP lQ : ℕ)
    (hP : a+lP ≤ m) (hQ : a+lQ ≤ m)
    (htP : ∀ i : Fin m, a ≤ i.val → i.val<a+lP → P.edgeAt i∈P.treeEdges)
    (hoP : ∀ i : Fin m, a ≤ i.val → i.val<a+lP → ¬P.FirstVisit i)
    (htQ : ∀ i : Fin m, a ≤ i.val → i.val<a+lQ → Q.edgeAt i∈Q.treeEdges)
    (hoQ : ∀ i : Fin m, a ≤ i.val → i.val<a+lQ → ¬Q.FirstVisit i)
    (hv : ∀ j : Fin (m+1), j.val ≤ a → P.vertex j=Q.vertex j)
    (he : P.vertexAt (a+lP)=Q.vertexAt (a+lQ)) :
    lP=lQ ∧ ∀ t, t ≤ lP → P.vertexAt (a+t)=Q.vertexAt (a+t) := by
  have hg := discoveryGraph_eq_of_vertex_prefix P Q a hv
  have hs : P.vertexAt a=Q.vertexAt a := by
    rw [P.vertexAt_eq a (by omega),Q.vertexAt_eq a (by omega)]
    exact hv ⟨a,by omega⟩ le_rfl
  let wP := P.oldTreeSegment a lP hP htP hoP
  let wQ := Q.oldTreeSegment a lQ hQ htQ hoQ
  let w := (wP.mapLe hg.le).copy hs he
  have hr : w.edges.IsChain (· ≠ ·) := by
    simpa only [w,SimpleGraph.Walk.edges_copy,SimpleGraph.Walk.edges_mapLe_eq_edges] using
      P.oldTreeSegment_reduced a lP hP htP hoP
  have hw : w=wQ := Q.discovery_tree_route_unique a w wQ hr
    (Q.oldTreeSegment_reduced a lQ hQ htQ hoQ)
  have hlist : List.ofFn (fun t : Fin (lP+1) => P.vertexAt (a+t.val)) =
      List.ofFn (fun t : Fin (lQ+1) => Q.vertexAt (a+t.val)) := by
    have hh := congrArg SimpleGraph.Walk.support hw
    simpa only [w,wP,wQ,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_mapLe_eq_support,
      oldTreeSegment_support] using hh
  have hlen : lP=lQ := by
    have hh := congrArg List.length hlist
    simp only [List.length_ofFn] at hh
    omega
  refine ⟨hlen,?_⟩
  subst lQ
  intro t ht
  exact congrFun (List.ofFn_inj.mp hlist) ⟨t,by omega⟩

theorem namedPath_tree_edge_mem_iff (P : Path V d m) (hm : 0<m) (i : Fin m) :
    (P.namedPath hm).edgeAt i ∈ (P.namedPath hm).treeEdges ↔ P.edgeAt i ∈ P.treeEdges := by
  simp only [treeEdges,Finset.mem_image,P.namedPath_firstTimes hm,P.namedPath_edgeAt_eq_iff hm]

/-- Matching names at the old endpoint identify the whole old-tree route. -/
theorem named_old_tree_reconstruction (P Q : Path V d m) (hm : 0<m)
    (a bP bQ : ℕ) (haP : a ≤ bP) (haQ : a ≤ bQ) (hPm : bP ≤ m) (hQm : bQ ≤ m)
    (htP : ∀ i : Fin m, a ≤ i.val → i.val<bP → P.edgeAt i∈P.treeEdges)
    (hoP : ∀ i : Fin m, a ≤ i.val → i.val<bP → ¬P.FirstVisit i)
    (htQ : ∀ i : Fin m, a ≤ i.val → i.val<bQ → Q.edgeAt i∈Q.treeEdges)
    (hoQ : ∀ i : Fin m, a ≤ i.val → i.val<bQ → ¬Q.FirstVisit i)
    (hv : ∀ j : Fin (m+1), j.val ≤ a → P.vertexName hm j=Q.vertexName hm j)
    (he : P.vertexName hm ⟨bP,by omega⟩=Q.vertexName hm ⟨bQ,by omega⟩) :
    bP=bQ ∧ ∀ j : Fin (m+1), a ≤ j.val → j.val ≤ bP →
      P.vertexName hm j=Q.vertexName hm j := by
  have hbP : a+(bP-a)=bP := by omega
  have hbQ : a+(bQ-a)=bQ := by omega
  obtain ⟨hl,hv'⟩ := old_tree_segment_reconstruction (P.namedPath hm) (Q.namedPath hm)
    a (bP-a) (bQ-a) (by omega) (by omega)
    (fun i hi hj => (P.namedPath_tree_edge_mem_iff hm i).mpr (htP i hi (by omega)))
    (fun i hi hj h => hoP i hi (by omega) ((P.namedPath_firstVisit_iff hm i).mp h))
    (fun i hi hj => (Q.namedPath_tree_edge_mem_iff hm i).mpr (htQ i hi (by omega)))
    (fun i hi hj h => hoQ i hi (by omega) ((Q.namedPath_firstVisit_iff hm i).mp h))
    hv (by rw [hbP,hbQ,(P.namedPath hm).vertexAt_eq bP hPm,
      (Q.namedPath hm).vertexAt_eq bQ hQm]; exact he)
  refine ⟨by omega,?_⟩
  intro j haj hjP
  have h := hv' (j.val-a) (by omega)
  have hj : a+(j.val-a)=j.val := by omega
  rw [hj,vertexAt_fin,vertexAt_fin] at h
  exact h

end Nonadditivity.HaarPathGraph.Path
