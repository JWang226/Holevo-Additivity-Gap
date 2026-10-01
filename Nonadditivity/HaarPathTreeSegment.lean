/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTree
import Mathlib.Data.List.ChainOfFn

/-! # Actual old-tree segments are reduced routes in the decoded prefix

Colored tree edges are uniquely determined by their unordered endpoints.
Therefore reduced colors exclude immediate reversal even after colors are
forgotten. An interval containing only old tree traversals is a literal walk
in the discovery graph at the beginning of that interval.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathGraph

section Walk
variable {V : Type*} {T : SimpleGraph V}

def walkOfSteps (v : ℕ → V) : (n : ℕ) →
    (∀ i, i < n → T.Adj (v i) (v (i+1))) → T.Walk (v 0) (v n)
  | 0, _ => .nil
  | n+1, h => .cons (h 0 (by omega))
      (walkOfSteps (fun i => v (i+1)) n (fun i hi => h (i+1) (by omega)))

theorem walkOfSteps_support (v : ℕ → V) (n : ℕ)
    (h : ∀ i, i < n → T.Adj (v i) (v (i+1))) :
    (walkOfSteps v n h).support = List.ofFn (fun i : Fin (n+1) => v i.val) := by
  induction n generalizing v with
  | zero => simp [walkOfSteps]
  | succ n ih =>
    rw [walkOfSteps, SimpleGraph.Walk.support_cons, ih]
    conv_rhs => rw [List.ofFn_succ]
    rfl

theorem walkOfSteps_edges (v : ℕ → V) (n : ℕ)
    (h : ∀ i, i < n → T.Adj (v i) (v (i+1))) :
    (walkOfSteps v n h).edges = List.ofFn (fun i : Fin n => s(v i.val, v (i.val+1))) := by
  induction n generalizing v with
  | zero => simp [walkOfSteps]
  | succ n ih =>
    rw [walkOfSteps, SimpleGraph.Walk.edges_cons, ih, List.ofFn_succ]
    rfl

theorem walkOfSteps_reduced (v : ℕ → V) (n : ℕ)
    (h : ∀ i, i < n → T.Adj (v i) (v (i+1)))
    (hr : ∀ i, i+1 < n → s(v i, v (i+1)) ≠ s(v (i+1), v (i+2))) :
    (walkOfSteps v n h).edges.IsChain (· ≠ ·) := by
  rw [walkOfSteps_edges, List.isChain_ofFn]
  intro i hi
  exact hr i hi
end Walk

namespace Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

lemma firstVisit_unoriented_injective {i j : Fin m}
    (hi : P.FirstVisit i) (hj : P.FirstVisit j)
    (h : s(P.vertex i.castSucc,P.vertex i.succ) = s(P.vertex j.castSucc,P.vertex j.succ)) :
    i=j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · rcases Sym2.eq_iff.mp h with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact hj i.succ (by simp; omega) hy
    · exact hj i.castSucc (by simp; omega) hx
  · rcases Sym2.eq_iff.mp h with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact hi j.succ (by simp; omega) hy.symm
    · exact hi j.castSucc (by simp; omega) hy.symm

lemma edgeAt_eq_unoriented {i j : Fin m} (h : P.edgeAt i=P.edgeAt j) :
    s(P.vertex i.castSucc,P.vertex i.succ) = s(P.vertex j.castSucc,P.vertex j.succ) :=
  Sym2.eq_iff.mpr (edge_endpoints h)

lemma tree_edge_eq_of_unoriented {i j : Fin m}
    (hi : P.edgeAt i ∈ P.treeEdges) (hj : P.edgeAt j ∈ P.treeEdges)
    (h : s(P.vertex i.castSucc,P.vertex i.succ) = s(P.vertex j.castSucc,P.vertex j.succ)) :
    P.edgeAt i=P.edgeAt j := by
  obtain ⟨k,hk,hki⟩ := Finset.mem_image.mp hi
  obtain ⟨l,hl,hlj⟩ := Finset.mem_image.mp hj
  have hkl : k=l := P.firstVisit_unoriented_injective
    ((P.mem_firstTimes k).mp hk) ((P.mem_firstTimes l).mp hl)
    ((P.edgeAt_eq_unoriented hki).trans (h.trans (P.edgeAt_eq_unoriented hlj).symm))
  exact hki.symm.trans (hkl ▸ hlj)

lemma tree_edge_nonloop {i : Fin m} (hi : P.edgeAt i ∈ P.treeEdges) :
    P.vertex i.castSucc ≠ P.vertex i.succ := by
  obtain ⟨k,hk,hki⟩ := Finset.mem_image.mp hi
  have hn := ((P.mem_firstTimes k).mp hk) k.castSucc (show k.castSucc.val ≤ k.val from le_rfl)
  rcases edge_endpoints hki with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · intro he; exact hn (hx.trans (he.trans hy.symm))
  · intro he; exact hn (hx.trans (he.symm.trans hy.symm))

/-- Forgetting colors preserves non-backtracking on discovery-tree edges. -/
theorem tree_edges_reduced {i j : Fin m} (hij : i.val+1=j.val)
    (hi : P.edgeAt i ∈ P.treeEdges) (hj : P.edgeAt j ∈ P.treeEdges) :
    s(P.vertex i.castSucc,P.vertex i.succ) ≠ s(P.vertex j.castSucc,P.vertex j.succ) := by
  intro he
  have hc := P.tree_edge_eq_of_unoriented hi hj he
  have hs : j.castSucc=i.succ := Fin.ext (by simpa using hij.symm)
  have he' : edge (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ) =
      edge (P.vertex i.succ) (P.colors j) (P.vertex j.succ) := by
    simpa only [edgeAt, hs] using hc
  exact P.reduced i j hij (edge_reverse_color (P.tree_edge_nonloop hi) he')

/-- Every edge of an old-only interval was discovered before the interval. -/
theorem old_tree_edge_in_prefix {a b : ℕ} {i : Fin m}
    (hai : a ≤ i.val) (hib : i.val < b) (hi : P.edgeAt i ∈ P.treeEdges)
    (hold : ∀ j : Fin m, a ≤ j.val → j.val < b → ¬P.FirstVisit j) :
    (P.discoveryGraph a).Adj (P.vertex i.castSucc) (P.vertex i.succ) := by
  obtain ⟨k,hk,hki⟩ := Finset.mem_image.mp hi
  have hkf := (P.mem_firstTimes k).mp hk
  have hki' : k.val ≤ i.val := by
    by_contra h
    exact P.firstVisit_edge_not_earlier hkf (by omega) hki.symm
  have hka : k.val < a := by
    by_contra h
    exact hold k (by omega) (by omega) hkf
  refine ⟨k,hkf,hka,?_⟩
  rcases edge_endpoints hki with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact Or.inl ⟨hx.symm,hy.symm⟩
  · exact Or.inr ⟨hy.symm,hx.symm⟩

/-- A total notation for the actual vertex sequence, clipped only outside
the path's valid index range. All segment uses remain inside that range. -/
def vertexAt (i : ℕ) : V := P.vertex ⟨min i m,by omega⟩

@[simp] theorem vertexAt_fin (i : Fin (m+1)) : P.vertexAt i.val=P.vertex i := by
  unfold vertexAt
  congr 1
  apply Fin.ext
  exact min_eq_left (by omega)

lemma vertexAt_eq (i : ℕ) (hi : i ≤ m) :
    P.vertexAt i=P.vertex ⟨i,by omega⟩ := by
  unfold vertexAt
  congr 1
  apply Fin.ext
  exact min_eq_left hi

theorem old_segment_adj (a l : ℕ) (hbound : a+l ≤ m)
    (htree : ∀ i : Fin m, a ≤ i.val → i.val < a+l → P.edgeAt i ∈ P.treeEdges)
    (hold : ∀ i : Fin m, a ≤ i.val → i.val < a+l → ¬P.FirstVisit i)
    (t : ℕ) (ht : t < l) :
    (P.discoveryGraph a).Adj (P.vertexAt (a+t)) (P.vertexAt (a+(t+1))) := by
  let i : Fin m := ⟨a+t,by omega⟩
  have ha : a ≤ i.val := by dsimp [i]; omega
  have hb : i.val < a+l := by dsimp [i]; omega
  have he₁ : P.vertexAt (a+t)=P.vertex i.castSucc := by
    rw [P.vertexAt_eq (a+t) (by omega)]; rfl
  have he₂ : P.vertexAt (a+(t+1))=P.vertex i.succ := by
    rw [P.vertexAt_eq (a+(t+1)) (by omega)]
    rfl
  rw [he₁,he₂]
  exact P.old_tree_edge_in_prefix ha hb (htree i ha hb) hold

def oldTreeSegment (a l : ℕ) (hbound : a+l ≤ m)
    (htree : ∀ i : Fin m, a ≤ i.val → i.val < a+l → P.edgeAt i ∈ P.treeEdges)
    (hold : ∀ i : Fin m, a ≤ i.val → i.val < a+l → ¬P.FirstVisit i) :
    (P.discoveryGraph a).Walk (P.vertexAt a) (P.vertexAt (a+l)) :=
  walkOfSteps (fun t => P.vertexAt (a+t)) l (P.old_segment_adj a l hbound htree hold)

theorem oldTreeSegment_support (a l : ℕ) (hbound : a+l ≤ m)
    (htree : ∀ i : Fin m, a ≤ i.val → i.val < a+l → P.edgeAt i ∈ P.treeEdges)
    (hold : ∀ i : Fin m, a ≤ i.val → i.val < a+l → ¬P.FirstVisit i) :
    (P.oldTreeSegment a l hbound htree hold).support =
      List.ofFn (fun t : Fin (l+1) => P.vertexAt (a+t.val)) :=
  walkOfSteps_support _ _ _

theorem oldTreeSegment_reduced (a l : ℕ) (hbound : a+l ≤ m)
    (htree : ∀ i : Fin m, a ≤ i.val → i.val < a+l → P.edgeAt i ∈ P.treeEdges)
    (hold : ∀ i : Fin m, a ≤ i.val → i.val < a+l → ¬P.FirstVisit i) :
    (P.oldTreeSegment a l hbound htree hold).edges.IsChain (· ≠ ·) := by
  apply walkOfSteps_reduced
  intro t ht
  let i : Fin m := ⟨a+t,by omega⟩
  let j : Fin m := ⟨a+(t+1),by omega⟩
  have hi : a ≤ i.val ∧ i.val < a+l := by dsimp [i]; omega
  have hj : a ≤ j.val ∧ j.val < a+l := by dsimp [j]; omega
  have he := P.tree_edges_reduced (i := i) (j := j) (by dsimp [i,j]; omega)
    (htree i hi.1 hi.2) (htree j hj.1 hj.2)
  have hv₀ : P.vertexAt (a+t)=P.vertex i.castSucc := by
    rw [P.vertexAt_eq (a+t) (by omega)]; rfl
  have hv₁ : P.vertexAt (a+(t+1))=P.vertex i.succ := by
    rw [P.vertexAt_eq (a+(t+1)) (by omega)]
    rfl
  have hv₁' : P.vertexAt (a+(t+1))=P.vertex j.castSucc := by
    rw [P.vertexAt_eq (a+(t+1)) (by omega)]; rfl
  have hv₂ : P.vertexAt (a+(t+2))=P.vertex j.succ := by
    rw [P.vertexAt_eq (a+(t+2)) (by omega)]
    rfl
  change s(P.vertexAt (a+t),P.vertexAt (a+(t+1))) ≠
    s(P.vertexAt (a+(t+1)),P.vertexAt (a+(t+2)))
  simpa only [hv₀,hv₁,hv₂,← hv₁'] using he

end Path
end Nonadditivity.HaarPathGraph
