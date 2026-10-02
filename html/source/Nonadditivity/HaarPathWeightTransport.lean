/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathColorRelabel
import Nonadditivity.HaarPathRelabel

/-! # Exact transport of Haar path weights

Color-preserving dart matching, including literal traversal multiplicities,
gives equality of actual Haar integrals. The intermediate permutations act
independently on the row and column labels of each matrix family.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarPathWeightTransport
open HaarPathGraph HaarPathProfiles HaarPathClasses HaarPathWeights
open HaarPathColorRelabel MeasureTheory HaarModel
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

def dartRelabel (σ τ : Fin d → Equiv.Perm V) : Equiv.Perm (Dart V d) where
  toFun q := ((σ q.1.2.1 q.1.1,q.1.2.1,τ q.1.2.1 q.1.2.2),q.2)
  invFun q := (((σ q.1.2.1).symm q.1.1,q.1.2.1,(τ q.1.2.1).symm q.1.2.2),q.2)
  left_inv q := by simp
  right_inv q := by simp

@[simp] theorem dartRelabel_color (σ τ : Fin d → Equiv.Perm V) (q : Dart V d) :
    color (dartRelabel σ τ q)=color q := rfl

@[simp] theorem dartRelabel_reverse (σ τ : Fin d → Equiv.Perm V) (q : Dart V d) :
    dartRelabel σ τ (reverse q)=reverse (dartRelabel σ τ q) := rfl

theorem dartRelabel_eq_of_entry_perms {P Q : Path V d m}
    (F : {q // q∈P.darts} ≃ {q // q∈Q.darts})
    (hcolor : ∀ q, color (F q).val=color q.val)
    (hrev : ∀ q : {q // q∈P.darts},
      F ⟨reverse q.val,P.reverse_mem q.property⟩ =
        ⟨reverse (F q).val,Q.reverse_mem (F q).property⟩)
    (σ τ : Fin d → Equiv.Perm V)
    (hp : ∀ q : {q // q∈P.darts}, ∀ a : Fin d,
      color q.val=(a,true) →
        σ a (source q.val)=source (F q).val ∧
        τ a (source (reverse q.val))=source (reverse (F q).val))
    (q : {q // q∈P.darts}) : dartRelabel σ τ q.val=(F q).val := by
  have hpos (r : {q // q∈P.darts}) (hb : r.val.2=true) :
      dartRelabel σ τ r.val=(F r).val := by
    have hr : color r.val=(r.val.1.2.1,true) := by simp only [color,hb]
    obtain ⟨hrow,hcol⟩ := hp r r.val.1.2.1 hr
    have hc := hcolor r
    have hb' : (F r).val.2=true := (congrArg Prod.snd hc).trans hb
    apply (dart_eq_iff_source_color_target _ _).mpr
    refine ⟨?_,hc.symm,?_⟩
    · simpa only [dartRelabel,Equiv.coe_fn_mk,source,hb,ite_true,hb'] using hrow
    · simpa only [dartRelabel,Equiv.coe_fn_mk,source,reverse,hb,hb',
        Bool.not_true,Bool.false_eq_true,ite_false] using hcol
  cases hb : q.val.2
  · let r : {q // q∈P.darts} := ⟨reverse q.val,P.reverse_mem q.property⟩
    have hr : r.val.2=true := by simp only [r,reverse,hb,Bool.not_false]
    have he := hpos r hr
    have he' := congrArg reverse he
    simpa only [r,dartRelabel_reverse,hrev,reverse_reverse] using he'
  · exact hpos q hb

theorem traversalList_perm_of_dart_counts {P Q : Path V d m}
    (F : {q // q∈P.darts} ≃ {q // q∈Q.darts})
    (E : Equiv.Perm (Dart V d)) (hE : ∀ q, E q.val=(F q).val)
    (hcount : ∀ q : {q // q∈P.darts},
      P.traversalList.count q.val=Q.traversalList.count (F q).val) :
    Q.traversalList.Perm (P.traversalList.map E) := by
  classical
  apply List.perm_iff_count.mpr
  intro r
  obtain ⟨q,rfl⟩ := E.surjective r
  rw [List.count_map_of_injective _ _ E.injective]
  by_cases hq : q∈P.darts
  · rw [hE ⟨q,hq⟩]
    exact (hcount ⟨q,hq⟩).symm
  · have hn : E q∉Q.darts := by
      intro he
      obtain ⟨r,hr⟩ := F.surjective ⟨E q,he⟩
      have hEq : E r.val=E q := (hE r).trans (congrArg Subtype.val hr)
      exact hq (E.injective hEq ▸ r.property)
    have hP : q∉P.traversalList := by
      intro h
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
      exact hq (hi ▸ P.traversal_mem i)
    have hQ : E q∉Q.traversalList := by
      intro h
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
      exact hn (hi ▸ Q.traversal_mem i)
    rw [List.count_eq_zero.mpr hP,List.count_eq_zero.mpr hQ]

def dartEntry {N : ℕ} (q : Dart (Fin (N+1)) 2) : SignedEntry N :=
  (color q,(q.1.1,q.1.2.2))

theorem pathEntries_eq_map_traversal {N m : ℕ} (P : Path (Fin (N+1)) 2 m) :
    pathEntries P=P.traversalList.map dartEntry := by
  simp only [pathEntries,Path.traversalList,List.map_ofFn]
  congr 1
  funext i
  cases hb : (P.colors i).2 <;>
    simp [dartEntry,Path.traversal,dart,edge,color,hb]
  all_goals exact Prod.ext rfl hb

def signedRelabel {N : ℕ} (σ τ : Fin 2 → Equiv.Perm (Fin (N+1)))
    (e : SignedEntry N) : SignedEntry N := (e.1,(σ e.1.1 e.2.1,τ e.1.1 e.2.2))

theorem selected_map_signedRelabel {N : ℕ}
    (σ τ : Fin 2 → Equiv.Perm (Fin (N+1))) (c : Color 2) (L : List (SignedEntry N)) :
    selected c (L.map (signedRelabel σ τ))=
      relabelEntries (σ c.1) (τ c.1) (selected c L) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    by_cases he : e.1=c
    · simp [selected,signedRelabel,relabelEntries,he] at ih ⊢
      exact ih
    · simp [selected,signedRelabel,relabelEntries,he] at ih ⊢
      exact ih

/-- Literal multiplicity-preserving colored dart matching preserves the exact
path expectation, with no restrictions on the degree or matrix dimension. -/
theorem integral_pathProduct_eq_of_dart_transport {N m : ℕ}
    {P Q : Path (Fin (N+1)) 2 m} (h : SamePattern P Q)
    (F : {q // q∈P.darts} ≃ {q // q∈Q.darts})
    (hcolor : ∀ q, color (F q).val=color q.val)
    (hcore : ∀ q, source q.val∈P.coreVertices →
      source (F q).val=h.vertexPerm (source q.val))
    (hcoreiff : ∀ q, source (F q).val∈Q.coreVertices ↔ source q.val∈P.coreVertices)
    (hrev : ∀ q : {q // q∈P.darts},
      F ⟨reverse q.val,P.reverse_mem q.property⟩ =
        ⟨reverse (F q).val,Q.reverse_mem (F q).property⟩)
    (hcount : ∀ q : {q // q∈P.darts},
      P.traversalList.count q.val=Q.traversalList.count (F q).val) :
    (∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N)) =
      ∫ U : LocalUnitary N × LocalUnitary N, pathProduct Q U ∂(haar N).prod (haar N) := by
  obtain ⟨σ,τ,hp⟩ := exists_family_entry_perms h F hcolor hcore hcoreiff hrev
  have hE := dartRelabel_eq_of_entry_perms F hcolor hrev σ τ hp
  have ht := traversalList_perm_of_dart_counts F (dartRelabel σ τ) hE hcount
  have he : (pathEntries Q).Perm ((pathEntries P).map (signedRelabel σ τ)) := by
    rw [pathEntries_eq_map_traversal,pathEntries_eq_map_traversal]
    convert ht.map dartEntry using 1 <;> simp only [List.map_map] <;> rfl
  have hs (a : Fin 2) (b : Bool) :
      (selected (a,b) (pathEntries Q)).Perm
        (relabelEntries (σ a) (τ a) (selected (a,b) (pathEntries P))) := by
    rw [←selected_map_signedRelabel σ τ (a,b) (pathEntries P)]
    exact (he.filter _).map Prod.snd
  simp_rw [pathProduct_eq]
  exact (integral_signedProduct_eq_of_family_relabel (pathEntries P) (pathEntries Q) σ τ hs).symm

end Nonadditivity.HaarPathWeightTransport
