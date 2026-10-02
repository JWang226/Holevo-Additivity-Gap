/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathGraph
import Mathlib.Data.Fintype.Fin

/-! # First-visit exploration of literal closed reduced paths

The discovery tree is formed by edges whose terminal vertex has not appeared
before. This file proves its cardinality and the corrected important-time
bound, including the case where the last traversal is a tree edge.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph
open scoped BigOperators
variable {V : Type*} {d m : ℕ}

lemma edge_endpoints {x y x' y' : V} {c c' : HaarPathProfiles.Color d}
    (h : edge x c y = edge x' c' y') :
    (x=x' ∧ y=y') ∨ (x=y' ∧ y=x') := by
  obtain ⟨g,b⟩ := c
  obtain ⟨g',b'⟩ := c'
  cases b <;> cases b' <;> simp only [edge, Bool.false_eq_true,
    ite_false, ite_true, Prod.mk.injEq] at h
  all_goals tauto

namespace Path
variable [DecidableEq V] (P : Path V d m)
local instance : BEq (Edge V d) := instBEqOfDecidableEq

/-- A position that discovers a vertex for the first time. -/
def FirstVisit (i : Fin m) : Prop :=
  ∀ j : Fin (m+1), j.val ≤ i.val → P.vertex j ≠ P.vertex i.succ

instance (i : Fin m) : Decidable (P.FirstVisit i) := inferInstanceAs
  (Decidable (∀ j : Fin (m+1), j.val ≤ i.val → P.vertex j ≠ P.vertex i.succ))

def firstTimes : Finset (Fin m) := Finset.univ.filter P.FirstVisit

def edgeAt (i : Fin m) : Edge V d :=
  edge (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ)

/-- The literal discovery-tree edges, without a supplied spanning-tree oracle. -/
def treeEdges : Finset (Edge V d) := P.firstTimes.image P.edgeAt

/-- Important positions are the traversals of a non-tree edge. We include
all positions here; excluding the final position cannot increase the count. -/
def importantTimes : Finset (Fin m) :=
  Finset.univ.filter fun i => P.edgeAt i ∉ P.treeEdges

@[simp] theorem mem_firstTimes (i : Fin m) : i ∈ P.firstTimes ↔ P.FirstVisit i := by
  simp [firstTimes]

lemma firstVisit_terminal_ne_root {i : Fin m} (hi : P.FirstVisit i) :
    P.vertex i.succ ≠ P.vertex 0 := Ne.symm (hi 0 (by simp))

lemma firstVisit_not_last {i : Fin m} (hi : P.FirstVisit i) : i.val+1<m := by
  by_contra hn
  have he : i.succ=Fin.last m := Fin.ext (by simp; omega)
  exact P.firstVisit_terminal_ne_root hi (by rw [he,P.closed])

lemma firstVisit_terminal_injective :
    Set.InjOn (fun i : Fin m => P.vertex i.succ) P.firstTimes := by
  intro i hi j hj he
  have hfi := (P.mem_firstTimes i).mp hi
  have hfj := (P.mem_firstTimes j).mp hj
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact hfj i.succ (by simpa using hij) he
  · exact hfi j.succ (by simpa using hji) he.symm

/-- Every non-root visited vertex has a unique discovery time. -/
theorem firstTimes_terminal_image :
    P.firstTimes.image (fun i => P.vertex i.succ) = P.vertices.erase (P.vertex 0) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_erase.mpr ⟨P.firstVisit_terminal_ne_root
      ((P.mem_firstTimes i).mp hi),P.end_mem i⟩
  · intro hv
    obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
    let S : Finset (Fin (m+1)) := Finset.univ.filter fun j => P.vertex j=v
    obtain ⟨k,hk,hkv⟩ := Finset.mem_image.mp hv
    have hS : S.Nonempty := ⟨k.castSucc,by simp [S,hkv]⟩
    let j := S.min' hS
    have hjv : P.vertex j=v := (Finset.mem_filter.mp (S.min'_mem hS)).2
    have hjpos : 0<j.val := by
      by_contra h
      have hj0 : j=0 := Fin.ext (by change j.val=0; omega)
      exact hne (by rw [←hjv,hj0])
    let i : Fin m := ⟨j.val-1,by have := j.isLt; omega⟩
    have hji : i.succ=j := Fin.ext (by change j.val-1+1=j.val; omega)
    refine Finset.mem_image.mpr ⟨i,?_,by rw [hji,hjv]⟩
    apply (P.mem_firstTimes i).mpr
    intro q hq he
    have hqS : q∈S := by simp [S,he,hji,hjv]
    have hmin : j≤q := S.min'_le _ hqS
    have hmin' : j.val≤q.val := hmin
    dsimp [i] at hq
    omega

lemma root_mem_vertices (hm : 0<m) : P.vertex 0∈P.vertices := by
  simpa using P.start_mem ⟨0,hm⟩

/-- Exactly one new vertex is added at each discovery time. -/
theorem card_firstTimes (hm : 0<m) : P.firstTimes.card+1=P.vertices.card := by
  have hc := Finset.card_image_of_injOn P.firstVisit_terminal_injective
  rw [P.firstTimes_terminal_image] at hc
  have he := Finset.card_erase_add_one (P.root_mem_vertices hm)
  omega

/-- An edge that first discovers a vertex was not traversed earlier. This
also handles negative colors and loops in the original colored multigraph. -/
theorem firstVisit_edge_not_earlier {j : Fin m} (hj : P.FirstVisit j)
    {i : Fin m} (hij : i.val<j.val) : P.edgeAt i ≠ P.edgeAt j := by
  intro he
  rcases edge_endpoints he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact hj i.succ (by simpa using hij) hy
  · exact hj i.castSucc (by simp; omega) hx

theorem firstVisit_edge_injective : Set.InjOn P.edgeAt P.firstTimes := by
  intro i hi j hj he
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact P.firstVisit_edge_not_earlier ((P.mem_firstTimes j).mp hj) hij he
  · exact P.firstVisit_edge_not_earlier ((P.mem_firstTimes i).mp hi) hji he.symm

theorem card_treeEdges (hm : 0<m) : P.treeEdges.card+1=P.vertices.card := by
  rw [treeEdges,Finset.card_image_of_injOn P.firstVisit_edge_injective]
  exact P.card_firstTimes hm

lemma edgeAt_mem_edges (i : Fin m) : P.edgeAt i∈P.edges := by
  apply List.mem_toFinset.mpr
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

lemma treeEdges_subset_edges : P.treeEdges⊆P.edges := by
  intro e he
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  exact P.edgeAt_mem_edges i

/-- The complement of important positions consists of the actual visits of
the discovery tree; no assumption about the final traversal is made. -/
theorem important_add_tree_visits :
    P.importantTimes.card + ∑ e∈P.treeEdges, P.edgeList.count e = m := by
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter fun i : Fin m => P.edgeAt i∈P.treeEdges)
    (t := P.treeEdges) (g := P.edgeAt) (f := fun _ => (1 : ℕ))
    (by intro i hi; exact (Finset.mem_filter.mp hi).2)
  have hcount (e : Edge V d) (he : e∈P.treeEdges) :
      ((Finset.univ.filter fun i : Fin m => P.edgeAt i∈P.treeEdges).filter
        fun i => P.edgeAt i=e).card = P.edgeList.count e := by
    simp only [Finset.filter_filter]
    have hf : (Finset.univ.filter fun i : Fin m =>
        P.edgeAt i∈P.treeEdges ∧ P.edgeAt i=e) =
        Finset.univ.filter fun i : Fin m => P.edgeAt i=e := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact And.right
      · intro h; exact ⟨h ▸ he,h⟩
    rw [hf]
    simpa [edgeList,edgeAt] using
      (Fin.card_filter_univ_eq_vector_get_eq_count e (List.Vector.ofFn P.edgeAt))
  have htree : (Finset.univ.filter fun i : Fin m => P.edgeAt i∈P.treeEdges).card =
      ∑ e∈P.treeEdges, P.edgeList.count e := by
    calc
      _ = ∑ e∈P.treeEdges, ((Finset.univ.filter fun i : Fin m =>
          P.edgeAt i∈P.treeEdges).filter fun i => P.edgeAt i=e).card := by
        simpa using hsum.symm
      _ = _ := Finset.sum_congr rfl hcount
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i : Fin m => P.edgeAt i∈P.treeEdges)
  rw [htree] at hpart
  simpa [importantTimes,add_comm] using hpart

/-- At least two visits per tree edge, except for genuine singleton edges. -/
theorem twice_treeEdges_le_visits_add_singletons :
    2*P.treeEdges.card ≤ (∑ e∈P.treeEdges, P.edgeList.count e) +
      (HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  have hpoint (e : Edge V d) (he : e∈P.treeEdges) :
      2 ≤ P.edgeList.count e + (if P.edgeList.count e=1 then 1 else 0) := by
    have hp : 0<P.edgeList.count e := List.count_pos_iff.mpr
      (List.mem_toFinset.mp (P.treeEdges_subset_edges he))
    split_ifs <;> omega
  have hs := Finset.sum_le_sum hpoint
  have hsub : (P.treeEdges.filter fun e => P.edgeList.count e=1) ⊆
      HaarPathMultiplicity.singletonEdges P.edgeList := by
    intro e he
    obtain ⟨he,hc⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨P.treeEdges_subset_edges he,hc⟩
  have hc := Finset.card_le_card hsub
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib,
    Finset.sum_ite,Nat.mul_one] at hs
  omega

/-- Corrected BC important-time estimate. The `+2` is essential: the last
traversal may be a tree edge, so it cannot always be deducted from this count. -/
theorem card_importantTimes_le (hm : 0<m) :
    P.importantTimes.card ≤ P.defectTwice+2 := by
  have ht := P.card_treeEdges hm
  have hv := P.important_add_tree_visits
  have hs := P.twice_treeEdges_le_visits_add_singletons
  have hd := P.twice_vertices_le_length_add_singletons
  dsimp [defectTwice]
  omega

end Path
end Nonadditivity.HaarPathGraph
