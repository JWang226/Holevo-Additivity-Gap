/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathFreshRuns
import Nonadditivity.HaarPathClassData

/-! # Relabelling and tree-route reconstruction for known prefixes

Prefix incidence patterns give actual vertex and local-color permutations.
Those permutations identify the complete discovery trees, so a reduced old
route is determined by its marked endpoint in the already decoded tree.
-/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} {d m : ℕ} [DecidableEq V]
variable {P Q : Path V d m} {k : ℕ}

/-- Literal relabelling of the portion already decoded. -/
def PrefixRelabeled (P Q : Path V d m) (k : ℕ) : Prop :=
  ∃ τ : Equiv.Perm V, ∃ β : V → Equiv.Perm (Color d),
    (∀ j : Fin (m+1), j.val ≤ k → τ (P.vertex j)=Q.vertex j) ∧
    ∀ a : Incidence m, a.1.val < k →
      β (incidenceVertex P a) (incidenceColor P a)=incidenceColor Q a

/-- A prefix pattern supplies actual permutations, including arbitrary
extensions on every vertex or color that has not yet been encountered. -/
theorem prefixSamePattern_relabeled [Fintype V]
    (h : PrefixSamePattern P Q k) : PrefixRelabeled P Q k := by
  classical
  obtain ⟨τ,hτ⟩ := exists_perm_of_kernel_eq
    (fun j : {j : Fin (m+1) // j.val ≤ k} => P.vertex j.val)
    (fun j : {j : Fin (m+1) // j.val ≤ k} => Q.vertex j.val)
    (fun a b => h.1 a.val b.val a.property b.property)
  have hlocal (v : V) : ∃ β : Equiv.Perm (Color d),
      ∀ a : {a : Incidence m // a.1.val < k ∧ incidenceVertex P a=v},
        β (incidenceColor P a.val)=incidenceColor Q a.val := by
    apply exists_perm_of_kernel_eq
    intro a b
    exact h.2 a.val b.val a.property.1 b.property.1
      (a.property.2.trans b.property.2.symm)
  choose β hβ using hlocal
  refine ⟨τ,β,fun j hj => hτ ⟨j,hj⟩,fun a ha => ?_⟩
  exact hβ (incidenceVertex P a) ⟨a,ha,rfl⟩

theorem prefixSamePattern_firstVisit_iff
    (h : PrefixSamePattern P Q k) (i : Fin m) (hi : i.val < k) :
    P.FirstVisit i ↔ Q.FirstVisit i := by
  constructor
  · intro hp j hj he
    exact hp j hj ((h.1 j i.succ (by omega) (by simp; omega)).mpr he)
  · intro hq j hj he
    exact hq j hj ((h.1 j i.succ (by omega) (by simp; omega)).mp he)

/-- The vertex permutation of a known prefix identifies its actual discovery
tree with that of the other path. No final-graph data is used. -/
def prefixTreeIso (h : PrefixSamePattern P Q k) (τ : Equiv.Perm V)
    (hτ : ∀ j : Fin (m+1), j.val ≤ k → τ (P.vertex j)=Q.vertex j) :
    P.discoveryGraph k ≃g Q.discoveryGraph k where
  toEquiv := τ
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨i,hi,hik,hxy⟩
      have hP := (prefixSamePattern_firstVisit_iff h i hik).mpr hi
      have hs := hτ i.castSucc (by simp; omega)
      have ht := hτ i.succ (by simp; omega)
      refine ⟨i,hP,hik,?_⟩
      rcases hxy with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inl ⟨τ.injective (hx.trans hs.symm),τ.injective (hy.trans ht.symm)⟩
      · exact Or.inr ⟨τ.injective (hx.trans ht.symm),τ.injective (hy.trans hs.symm)⟩
    · rintro ⟨i,hi,hik,hxy⟩
      have hQ := (prefixSamePattern_firstVisit_iff h i hik).mp hi
      have hs := hτ i.castSucc (by simp; omega)
      have ht := hτ i.succ (by simp; omega)
      refine ⟨i,hQ,hik,?_⟩
      rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨hs,ht⟩
      · exact Or.inr ⟨ht,hs⟩

/-- Reduced tree routes between corresponding marked endpoints agree after
transport through the decoded prefix. This is the non-circular tree-run
reconstruction step. -/
theorem prefix_tree_route_reconstruction
    (h : PrefixSamePattern P Q k) (τ : Equiv.Perm V)
    (hτ : ∀ j : Fin (m+1), j.val ≤ k → τ (P.vertex j)=Q.vertex j)
    {x y : V} (a : (P.discoveryGraph k).Walk x y)
    (b : (Q.discoveryGraph k).Walk (τ x) (τ y))
    (ha : a.edges.IsChain (· ≠ ·)) (hb : b.edges.IsChain (· ≠ ·)) :
    a.map (prefixTreeIso h τ hτ).toHom=b := by
  let e := prefixTreeIso h τ hτ
  have hap := ((P.discoveryGraph_isAcyclic k).isPath_iff_isChain a).mpr ha
  have hbp := ((Q.discoveryGraph_isAcyclic k).isPath_iff_isChain b).mpr hb
  have ham : (a.map e.toHom).IsPath := SimpleGraph.Walk.map_isPath_of_injective e.injective hap
  exact congrArg Subtype.val ((Q.discoveryGraph_isAcyclic k).path_unique
    ⟨a.map e.toHom,ham⟩ ⟨b,hbp⟩)

end Nonadditivity.HaarPathClasses
