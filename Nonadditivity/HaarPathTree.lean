/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathExploration
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # The actual discovery tree is acyclic

The proof constructs every prefix graph by adding the edge to a newly visited
vertex. The result supplies the unique-tree-route step in path encoding.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph
open scoped BigOperators
variable {V : Type*} {d m : ℕ}

lemma edge_reverse_color {x y z : V} {c c' : HaarPathProfiles.Color d}
    (hxy : x≠y) (h : edge x c y=edge y c' z) : c'=flipColor c := by
  obtain ⟨g,b⟩ := c
  obtain ⟨g',b'⟩ := c'
  cases b  <;>  cases b'  <;>  simp only [edge, Bool.false_eq_true,
    ite_false, ite_true, Prod.mk.injEq] at h
  all_goals simp only [flipColor, Bool.not_false, Bool.not_true, Prod.mk.injEq]
  all_goals tauto

namespace Path
variable [DecidableEq V] (P : Path V d m)

/-- A first visit cannot be immediately followed by an old tree-edge visit.
The next step either discovers another vertex or is important. -/
theorem firstVisit_next {i j : Fin m} (hi : P.FirstVisit i) (hij : i.val+1=j.val) :
    P.FirstVisit j ∨ j∈P.importantTimes := by
  by_cases hj : P.FirstVisit j
  · exact Or.inl hj
  right
  simp only [importantTimes,Finset.mem_filter,Finset.mem_univ,true_and]
  intro htree
  obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp htree
  have hkf := (P.mem_firstTimes k).mp hk
  have hkj : k.val < j.val := by
    by_contra h
    by_cases he : k=j
    · subst k; exact hj hkf
    · have hlt : j.val < k.val := by
        have hne : j.val≠k.val := by intro hv; exact he (Fin.ext hv.symm)
        omega
      exact P.firstVisit_edge_not_earlier hkf hlt hke.symm
  have hji : j.castSucc=i.succ := Fin.ext (by simpa using hij.symm)
  by_cases hki : k=i
  · subst k
    have hn : P.vertex i.castSucc ≠ P.vertex i.succ := hi i.castSucc (by simp)
    have he : edge (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ) =
        edge (P.vertex i.succ) (P.colors j) (P.vertex j.succ) := by
      simpa only [edgeAt,hji] using hke
    exact P.reduced i j hij (edge_reverse_color hn he)
  · have hlt : k.val < i.val := by
      have hn : k.val≠i.val := by intro hv; exact hki (Fin.ext hv)
      omega
    rcases edge_endpoints hke with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact hi k.castSucc (by simp; omega) (hx.trans (congrArg P.vertex hji))
    · exact hi k.succ (by simp; omega) (hy.trans (congrArg P.vertex hji))

/-- The simple graph obtained from discovery edges before time `k`. Tree
edges cannot be loops or parallel edges, so forgetting their colors is safe. -/
def discoveryGraph (k : ℕ) : SimpleGraph V where
  Adj x y := ∃ i : Fin m, P.FirstVisit i ∧ i.val < k ∧
    ((x=P.vertex i.castSucc ∧ y=P.vertex i.succ) ∨
     (x=P.vertex i.succ ∧ y=P.vertex i.castSucc))
  symm := by
    intro x y
    rintro ⟨i,hi,hik,hxy⟩
    exact ⟨i,hi,hik,by tauto⟩
  loopless := by
    constructor
    intro x
    rintro ⟨i,hi,hik,hxx⟩
    have hn := hi i.castSucc (show i.castSucc.val ≤ i.val from le_rfl)
    rcases hxx with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact hn (h₁.symm.trans h₂)
    · exact hn (h₂.symm.trans h₁)

@[simp] theorem discoveryGraph_zero : P.discoveryGraph 0=⊥ := by
  ext x y
  simp [discoveryGraph]

/-- A vertex discovered at the next step is isolated in the prefix graph. -/
theorem discoveryGraph_new_isolated {i : Fin m} (hi : P.FirstVisit i) (x : V) :
    ¬ (P.discoveryGraph i.val).Adj (P.vertex i.succ) x := by
  rintro ⟨j,hj,hji,hxy⟩
  rcases hxy with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact hi j.castSucc (by simp; omega) hs.symm
  · exact hi j.succ (by simp; omega) hs.symm

theorem discoveryGraph_new_not_reachable {i : Fin m} (hi : P.FirstVisit i) :
    ¬ (P.discoveryGraph i.val).Reachable (P.vertex i.castSucc) (P.vertex i.succ) := by
  intro hr
  obtain ⟨w⟩ := hr.symm
  have hn := hi i.castSucc (show i.castSucc.val ≤ i.val from le_rfl)
  obtain ⟨x,hx,q,he⟩ := SimpleGraph.Walk.not_nil_iff.mp
    (SimpleGraph.Walk.not_nil_of_ne (p := w) hn.symm)
  exact P.discoveryGraph_new_isolated hi x hx

/-- One exploration step adds one edge precisely when it discovers a vertex. -/
theorem discoveryGraph_succ_of_first {i : Fin m} (hi : P.FirstVisit i) :
    P.discoveryGraph (i.val+1) = P.discoveryGraph i.val ⊔
      SimpleGraph.fromEdgeSet {s(P.vertex i.castSucc,P.vertex i.succ)} := by
  ext x y
  simp only [SimpleGraph.sup_adj,SimpleGraph.fromEdgeSet_adj,Set.mem_singleton_iff,
    Sym2.eq_iff]
  constructor
  · rintro ⟨j,hj,hji,hxy⟩
    by_cases hlt : j.val < i.val
    · exact Or.inl ⟨j,hj,hlt,hxy⟩
    · have he : j=i := Fin.ext (by omega)
      subst j
      right
      refine ⟨hxy,?_⟩
      have hn := hi i.castSucc (show i.castSucc.val ≤ i.val from le_rfl)
      rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hn
      · exact hn.symm
  · rintro (⟨j,hj,hji,hxy⟩ | ⟨hxy,hne⟩)
    · exact ⟨j,hj,by omega,hxy⟩
    · exact ⟨i,hi,by omega,hxy⟩

theorem discoveryGraph_succ_of_not_first {k : ℕ}
    (hk : ∀ i : Fin m, i.val=k → ¬P.FirstVisit i) :
    P.discoveryGraph (k+1)=P.discoveryGraph k := by
  ext x y
  constructor
  · rintro ⟨i,hi,hik,hxy⟩
    exact ⟨i,hi,by have hn : i.val≠k := fun he =>  hk i he hi; omega,hxy⟩
  · rintro ⟨i,hi,hik,hxy⟩
    exact ⟨i,hi,by omega,hxy⟩

/-- Acyclicity of every actual discovery prefix. -/
theorem discoveryGraph_isAcyclic (k : ℕ) : (P.discoveryGraph k).IsAcyclic := by
  induction k with
  | zero =>  rw [P.discoveryGraph_zero]; exact SimpleGraph.isAcyclic_bot
  | succ k ih => 
      by_cases h : ∃ i : Fin m, i.val=k ∧ P.FirstVisit i
      · obtain ⟨i,hi,hfirst⟩ := h
        subst k
        rw [P.discoveryGraph_succ_of_first hfirst]
        exact SimpleGraph.IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable
          (P.discoveryGraph_new_not_reachable hfirst) ih
      · rw [P.discoveryGraph_succ_of_not_first (by simpa only [not_exists,not_and] using h)]
        exact ih

/-- Every non-backtracking walk in the actual discovery tree is the unique
such route between its endpoints. The non-backtracking condition is the
literal inequality of consecutive unoriented tree edges. -/
theorem discovery_tree_route_unique (k : ℕ) {x y : V}
    (a b : (P.discoveryGraph k).Walk x y)
    (ha : a.edges.IsChain (· ≠ ·)) (hb : b.edges.IsChain (· ≠ ·)) : a=b := by
  have ht := P.discoveryGraph_isAcyclic k
  have hap := (ht.isPath_iff_isChain a).mpr ha
  have hbp := (ht.isPath_iff_isChain b).mpr hb
  exact congrArg Subtype.val (ht.path_unique ⟨a,hap⟩ ⟨b,hbp⟩)

end Path
end Nonadditivity.HaarPathGraph
