/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathVertexNames
import Nonadditivity.HaarPathExplorationBlocks

/-! # Literal reconstruction of normalized fresh exploration runs

Fresh vertex names are their first-arrival times. Incoming incidence labels
are fixed, as are outgoing labels after the first fresh step. Consequently
the start name and first outgoing label determine the whole interval's
normalized data.
-/

noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles

variable {V : Type*} [DecidableEq V] {d m : ℕ}

/-- The two local normalization requirements at first arrivals. -/
def FreshNormalization (P : Path V d m) (β : V → Equiv.Perm (Color d))
    (c₀ c₁ : Color d) : Prop :=
  (∀ i : Fin m, P.FirstVisit i → β (P.vertex i.succ) (flipColor (P.colors i))=c₀) ∧
  (∀ i j : Fin m, P.FirstVisit i → i.val+1=j.val → β (P.vertex i.succ) (P.colors j)=c₁)

/-- Reconstruct all names and both incidence labels on an actual fresh run.
No intermediate color choices or vertex correspondences are supplied. -/
theorem normalized_fresh_run (P Q : Path V d m) (hm : 0<m)
    (β γ : V → Equiv.Perm (Color d)) (c₀ c₁ : Color d)
    (hβ : FreshNormalization P β c₀ c₁) (hγ : FreshNormalization Q γ c₀ c₁)
    (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m)
    (hfresh : ∀ i : Fin m, a ≤ i.val → i.val<b → P.FirstVisit i ∧ Q.FirstVisit i)
    (hstart : P.vertexName hm ⟨a,by omega⟩=Q.vertexName hm ⟨a,by omega⟩)
    (hfirst : ∀ i : Fin m, i.val=a →
      normalizedIncidenceColor P β (i,true)=normalizedIncidenceColor Q γ (i,true)) :
    (∀ j : Fin (m+1), a ≤ j.val → j.val ≤ b → P.vertexName hm j=Q.vertexName hm j) ∧
    (∀ i : Fin m, a ≤ i.val → i.val<b →
      normalizedIncidenceColor P β (i,true)=normalizedIncidenceColor Q γ (i,true) ∧
      normalizedIncidenceColor P β (i,false)=normalizedIncidenceColor Q γ (i,false)) := by
  constructor
  · intro j haj hjb
    by_cases hja : j.val=a
    · have he : j=⟨a,by omega⟩ := Fin.ext hja
      simpa only [he] using hstart
    · let i : Fin m := ⟨j.val-1,by omega⟩
      have hij : i.succ=j := Fin.ext (by dsimp [i]; omega)
      have hi := hfresh i (by dsimp [i]; omega) (by dsimp [i]; omega)
      apply Fin.ext
      rw [←hij,P.vertexName_of_firstVisit hm hi.1,Q.vertexName_of_firstVisit hm hi.2]
  · intro i hai hib
    have hi := hfresh i hai hib
    constructor
    · by_cases hia : i.val=a
      · exact hfirst i hia
      · let j : Fin m := ⟨i.val-1,by omega⟩
        have hji : j.val+1=i.val := by dsimp [j]; omega
        have hidx : i.castSucc=j.succ := Fin.ext hji.symm
        have hj := hfresh j (by dsimp [j]; omega) (by dsimp [j]; omega)
        change β (P.vertex i.castSucc) (P.colors i)=γ (Q.vertex i.castSucc) (Q.colors i)
        rw [hidx,hβ.2 j i hj.1 hji,hγ.2 j i hj.2 hji]
    · change β (P.vertex i.succ) (flipColor (P.colors i))=
        γ (Q.vertex i.succ) (flipColor (Q.colors i))
      rw [hβ.1 i hi.1,hγ.1 i hi.2]

/-- The initial fresh prefix requires no color mark: the root's outgoing
color is fixed by its own normalization. -/
theorem normalized_initial_fresh_run (P Q : Path V d m) (hm : 0<m)
    (β γ : V → Equiv.Perm (Color d)) (c₀ c₁ : Color d)
    (hβ : FreshNormalization P β c₀ c₁) (hγ : FreshNormalization Q γ c₀ c₁)
    (hβroot : β (P.vertex 0) (P.colors ⟨0,hm⟩)=c₀)
    (hγroot : γ (Q.vertex 0) (Q.colors ⟨0,hm⟩)=c₀)
    (b : ℕ) (hbm : b ≤ m)
    (hfresh : ∀ i : Fin m, i.val<b → P.FirstVisit i ∧ Q.FirstVisit i) :
    (∀ j : Fin (m+1), j.val ≤ b → P.vertexName hm j=Q.vertexName hm j) ∧
    (∀ i : Fin m, i.val<b →
      normalizedIncidenceColor P β (i,true)=normalizedIncidenceColor Q γ (i,true) ∧
      normalizedIncidenceColor P β (i,false)=normalizedIncidenceColor Q γ (i,false)) := by
  have hs : P.vertexName hm ⟨0,by omega⟩=Q.vertexName hm ⟨0,by omega⟩ := by simp
  have ho (i : Fin m) (hi : i.val=0) :
      normalizedIncidenceColor P β (i,true)=normalizedIncidenceColor Q γ (i,true) := by
    have he : i=⟨0,hm⟩ := Fin.ext hi
    subst i
    change β (P.vertex 0) (P.colors ⟨0,hm⟩)=γ (Q.vertex 0) (Q.colors ⟨0,hm⟩)
    rw [hβroot,hγroot]
  have h := normalized_fresh_run P Q hm β γ c₀ c₁ hβ hγ 0 b (by omega) hbm
    (fun i _ hi => hfresh i hi) hs ho
  exact ⟨fun j hj => h.1 j (by omega) hj,fun i hi => h.2 i (by omega) hi⟩

/-- Before a shared first important time, the normalized data agree without
any stored labels. The fresh-run hypothesis follows from the actual paths. -/
theorem normalized_before_first_important (P Q : Path V d m) (hm : 0<m)
    (β γ : V → Equiv.Perm (Color d)) (c₀ c₁ : Color d)
    (hβ : FreshNormalization P β c₀ c₁) (hγ : FreshNormalization Q γ c₀ c₁)
    (hβroot : β (P.vertex 0) (P.colors ⟨0,hm⟩)=c₀)
    (hγroot : γ (Q.vertex 0) (Q.colors ⟨0,hm⟩)=c₀)
    (hb : P.nextImportant 0=Q.nextImportant 0) :
    (∀ j : Fin (m+1), j.val ≤ P.nextImportant 0 →
      P.vertexName hm j=Q.vertexName hm j) ∧
    (∀ i : Fin m, i.val<P.nextImportant 0 →
      normalizedIncidenceColor P β (i,true)=normalizedIncidenceColor Q γ (i,true) ∧
      normalizedIncidenceColor P β (i,false)=normalizedIncidenceColor Q γ (i,false)) := by
  apply normalized_initial_fresh_run P Q hm β γ c₀ c₁ hβ hγ hβroot hγroot
    (P.nextImportant 0) (P.nextImportant_bounds 0 (by omega)).2
  intro i hi
  exact ⟨P.initial_prefix_firstVisit i hi,Q.initial_prefix_firstVisit i (by simpa only [←hb] using hi)⟩

end Nonadditivity.HaarPathClasses
