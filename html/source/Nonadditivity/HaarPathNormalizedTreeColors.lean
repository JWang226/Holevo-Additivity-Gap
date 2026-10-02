/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathNormalizedTree

/-! # Old-tree routes reconstruct both normalized incidence labels -/
noncomputable section
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {d m : ℕ}

theorem normalized_repeated_edge (P Q : Path V d m)
    (β γ : V → Equiv.Perm (Color d)) (i k : Fin m)
    (hP : P.edgeAt i=P.edgeAt k) (hQ : Q.edgeAt i=Q.edgeAt k)
    (hnP : P.vertex k.castSucc ≠ P.vertex k.succ)
    (hnQ : Q.vertex k.castSucc ≠ Q.vertex k.succ)
    (hv : P.vertex i.castSucc=P.vertex k.castSucc ↔ Q.vertex i.castSucc=Q.vertex k.castSucc)
    (hc : ∀ b : Bool, normalizedIncidenceColor P β (k,b)=normalizedIncidenceColor Q γ (k,b)) :
    ∀ b : Bool, normalizedIncidenceColor P β (i,b)=normalizedIncidenceColor Q γ (i,b) := by
  rcases edge_eq_iff.mp hP with ⟨hPx,hPc,hPy⟩ | ⟨hPx,hPc,hPy⟩
  · rcases edge_eq_iff.mp hQ with ⟨hQx,hQc,hQy⟩ | ⟨hQx,hQc,hQy⟩
    · intro b
      cases b
      · simpa [normalizedIncidenceColor,incidenceVertex,incidenceColor,
          hPx,hPc,hPy,hQx,hQc,hQy] using hc false
      · simpa [normalizedIncidenceColor,incidenceVertex,incidenceColor,
          hPx,hPc,hPy,hQx,hQc,hQy] using hc true
    · exact (hnQ ((hv.mp hPx).symm.trans hQx)).elim
  · rcases edge_eq_iff.mp hQ with ⟨hQx,hQc,hQy⟩ | ⟨hQx,hQc,hQy⟩
    · exact (hnP ((hv.mpr hQx).symm.trans hPx)).elim
    · intro b
      cases b
      · simpa [normalizedIncidenceColor,incidenceVertex,incidenceColor,
          hPx,hPc,hPy,hQx,hQc,hQy,flipColor] using hc true
      · simpa [normalizedIncidenceColor,incidenceVertex,incidenceColor,
          hPx,hPc,hPy,hQx,hQc,hQy,flipColor] using hc false

theorem normalized_old_tree_colors (P Q : Path V d m) (hm : 0<m)
    (β γ : V → Equiv.Perm (Color d)) (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m)
    (htP : ∀ i : Fin m, a ≤ i.val → i.val<b → P.edgeAt i∈P.treeEdges)
    (hoP : ∀ i : Fin m, a ≤ i.val → i.val<b → ¬P.FirstVisit i)
    (htQ : ∀ i : Fin m, a ≤ i.val → i.val<b → Q.edgeAt i∈Q.treeEdges)
    (hv : ∀ j : Fin (m+1), j.val ≤ b → P.vertexName hm j=Q.vertexName hm j)
    (hc : ∀ z : Incidence m, z.1.val<a →
      normalizedIncidenceColor P β z=normalizedIncidenceColor Q γ z) :
    ∀ i : Fin m, a ≤ i.val → i.val<b → ∀ c : Bool,
      normalizedIncidenceColor P β (i,c)=normalizedIncidenceColor Q γ (i,c) := by
  intro i hai hib
  obtain ⟨k,hk,hki⟩ := Finset.mem_image.mp (htP i hai hib)
  have hkf := (P.mem_firstTimes k).mp hk
  have hki' : k.val ≤ i.val := by
    by_contra h
    exact P.firstVisit_edge_not_earlier hkf (by omega) hki.symm
  have hka : k.val<a := by
    by_contra h
    exact hoP k (by omega) (by omega) hkf
  have hkQ : Q.FirstVisit k := by
    intro j hj he
    apply hkf j hj
    apply (P.vertexName_eq_iff hm j k.succ).mp
    rw [hv j (by omega),hv k.succ (by simp; omega)]
    exact (Q.vertexName_eq_iff hm j k.succ).mpr he
  have hkQt : Q.edgeAt k∈Q.treeEdges := Finset.mem_image.mpr
    ⟨k,(Q.mem_firstTimes k).mpr hkQ,rfl⟩
  have hkPt : P.edgeAt k∈P.treeEdges := Finset.mem_image.mpr ⟨k,hk,rfl⟩
  have heN : (P.namedPath hm).edgeAt k=(P.namedPath hm).edgeAt i :=
    (P.namedPath_edgeAt_eq_iff hm k i).mpr hki
  have heS := (P.namedPath hm).edgeAt_eq_unoriented heN
  have heQ : s((Q.namedPath hm).vertex k.castSucc,(Q.namedPath hm).vertex k.succ) =
      s((Q.namedPath hm).vertex i.castSucc,(Q.namedPath hm).vertex i.succ) := by
    simpa only [Path.namedPath,hv k.castSucc (by simp; omega),hv k.succ (by simp; omega),
      hv i.castSucc (by simp; omega),hv i.succ (by simp; omega)] using heS
  have hkiQ : Q.edgeAt k=Q.edgeAt i :=
    (Q.namedPath_edgeAt_eq_iff hm k i).mp ((Q.namedPath hm).tree_edge_eq_of_unoriented
      ((Q.namedPath_tree_edge_mem_iff hm k).mpr hkQt)
      ((Q.namedPath_tree_edge_mem_iff hm i).mpr (htQ i hai hib)) heQ)
  have hvertex : P.vertex i.castSucc=P.vertex k.castSucc ↔
      Q.vertex i.castSucc=Q.vertex k.castSucc := by
    rw [← P.vertexName_eq_iff hm i.castSucc k.castSucc,
      ← Q.vertexName_eq_iff hm i.castSucc k.castSucc,
      hv i.castSucc (by simp; omega),hv k.castSucc (by simp; omega)]
  exact normalized_repeated_edge P Q β γ i k hki.symm hkiQ.symm
    (P.tree_edge_nonloop hkPt) (Q.tree_edge_nonloop hkQt) hvertex
    (fun c => hc (k,c) hka)

/-- Complete normalized reconstruction of an old-tree interval from the
decoded prefix and the endpoint's first-occurrence name. -/
theorem normalized_old_tree_reconstruction (P Q : Path V d m) (hm : 0<m)
    (β γ : V → Equiv.Perm (Color d))
    (a bP bQ : ℕ) (haP : a ≤ bP) (haQ : a ≤ bQ) (hPm : bP ≤ m) (hQm : bQ ≤ m)
    (htP : ∀ i : Fin m, a ≤ i.val → i.val<bP → P.edgeAt i∈P.treeEdges)
    (hoP : ∀ i : Fin m, a ≤ i.val → i.val<bP → ¬P.FirstVisit i)
    (htQ : ∀ i : Fin m, a ≤ i.val → i.val<bQ → Q.edgeAt i∈Q.treeEdges)
    (hoQ : ∀ i : Fin m, a ≤ i.val → i.val<bQ → ¬Q.FirstVisit i)
    (hv : ∀ j : Fin (m+1), j.val ≤ a → P.vertexName hm j=Q.vertexName hm j)
    (hc : ∀ z : Incidence m, z.1.val<a →
      normalizedIncidenceColor P β z=normalizedIncidenceColor Q γ z)
    (he : P.vertexName hm ⟨bP,by omega⟩=Q.vertexName hm ⟨bQ,by omega⟩) :
    bP=bQ ∧
    (∀ j : Fin (m+1), a ≤ j.val → j.val ≤ bP → P.vertexName hm j=Q.vertexName hm j) ∧
    (∀ i : Fin m, a ≤ i.val → i.val<bP → ∀ c : Bool,
      normalizedIncidenceColor P β (i,c)=normalizedIncidenceColor Q γ (i,c)) := by
  obtain ⟨hb,hv'⟩ := P.named_old_tree_reconstruction Q hm a bP bQ haP haQ hPm hQm
    htP hoP htQ hoQ hv he
  subst bQ
  refine ⟨rfl,hv',?_⟩
  apply normalized_old_tree_colors P Q hm β γ a bP haP hPm htP hoP htQ _ hc
  intro j hj
  by_cases hja : j.val ≤ a
  · exact hv j hja
  · exact hv' j (by omega) hj

end Nonadditivity.HaarPathClasses
