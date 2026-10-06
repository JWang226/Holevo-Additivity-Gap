/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainLabels
import Nonadditivity.HaarPathChainProfiles

/-! # Edge multiplicities in the actual maximal-chain decomposition

An original colored edge occurs exactly as often as its orientation-free
core-chain label. In particular the singleton edge budget is exactly the sum
of the lengths of singleton core chains.
-/
noncomputable section
open scoped BigOperators
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

def chainEdges (c : P.CoreChain) : List (Edge V d) := c.val.map Prod.fst

@[simp] theorem chainEdges_reverse (c : P.CoreChain) :
    P.chainEdges (P.coreChainReverse c) = (P.chainEdges c).reverse := by
  change ((c.val.reverse.map reverse).map Prod.fst) = (c.val.map Prod.fst).reverse
  simp [List.map_map, reverse, List.map_reverse]

theorem chainLabel_eq_of_common_edge (c c' : P.CoreChain) {e : Edge V d}
    (he : e ∈ P.chainEdges c) (he' : e ∈ P.chainEdges c') :
    P.chainLabel c = P.chainLabel c' := by
  obtain ⟨q,hq,hqe⟩ := List.mem_map.mp he
  obtain ⟨q',hq',hq'e⟩ := List.mem_map.mp he'
  have hfst : q.1 = q'.1 := hqe.trans hq'e.symm
  have hor : q = q' ∨ q = reverse q' := by
    obtain ⟨a,b⟩ := q
    obtain ⟨a',b'⟩ := q'
    change a=a' at hfst
    subst a'
    cases b <;> cases b' <;> simp [reverse]
  rcases hor with rfl | hrev
  · rw [P.coreChain_eq_of_common_dart c c' hq hq']
  · have hmem : q ∈ (P.coreChainReverse c').val := by
      change q ∈ c'.val.reverse.map reverse
      exact List.mem_map.mpr ⟨q',List.mem_reverse.mpr hq',hrev.symm⟩
    rw [P.coreChain_eq_of_common_dart c (P.coreChainReverse c') hq hmem,
      P.chainLabel_reverse]

theorem chainEdges_mem_of_label_eq (c c' : P.CoreChain)
    (h : P.chainLabel c = P.chainLabel c') {e : Edge V d}
    (he : e ∈ P.chainEdges c) : e ∈ P.chainEdges c' := by
  have hmem : c ∈ ({c',P.coreChainReverse c'} : Finset P.CoreChain) := by
    have hv := congrArg Subtype.val h
    change {c,P.coreChainReverse c} = {c',P.coreChainReverse c'} at hv
    rw [←hv]
    simp
  rcases Finset.mem_insert.mp hmem with rfl | hc
  · exact he
  · have hc := Finset.mem_singleton.mp hc
    simpa [hc] using he

theorem chainEdges_count (c c' : P.CoreChain) {e : Edge V d}
    (he : e ∈ P.chainEdges c') :
    (P.chainEdges c).count e = if P.chainLabel c = P.chainLabel c' then 1 else 0 := by
  split_ifs with h
  · exact List.count_eq_one_of_mem (P.coreChain_edges_nodup c)
      (P.chainEdges_mem_of_label_eq c' c h.symm he)
  · apply List.count_eq_zero.mpr
    intro hc
    exact h (P.chainLabel_eq_of_common_edge c c' hc he)

theorem edgeList_eq_flatMap_chainEdges (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) :
    P.edgeList = cs.flatMap P.chainEdges := by
  have hh := congrArg (List.map Prod.fst) hcs
  have he : P.traversalList.map Prod.fst = P.edgeList := by
    simp only [traversalList,edgeList,List.map_ofFn]
    rfl
  rw [he,List.map_flatten,List.map_map] at hh
  exact hh.symm

theorem count_flatMap_chainEdges (cs : List P.CoreChain) (c : P.CoreChain)
    {e : Edge V d} (he : e ∈ P.chainEdges c) :
    (cs.flatMap P.chainEdges).count e = (cs.map P.chainLabel).count (P.chainLabel c) := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
      simp only [List.flatMap_cons,List.count_append,List.map_cons,List.count_cons]
      rw [P.chainEdges_count a c he,ih]
      by_cases h : P.chainLabel a = P.chainLabel c
      · simp [h]
        omega
      · simp [h]

theorem edge_count_eq_chain_count (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList)
    (c : P.CoreChain) {e : Edge V d} (he : e ∈ P.chainEdges c) :
    P.edgeList.count e = (cs.map P.chainLabel).count (P.chainLabel c) := by
  rw [P.edgeList_eq_flatMap_chainEdges cs hcs]
  exact P.count_flatMap_chainEdges cs c he

def labelEdges (e : P.unorientedChains) : Finset (Edge V d) :=
  (P.chainEdges (P.representative e)).toFinset

theorem labelEdges_card (e : P.unorientedChains) :
    (P.labelEdges e).card = (P.representative e).val.length := by
  rw [labelEdges,chainEdges,List.toFinset_card_of_nodup (P.coreChain_edges_nodup _)]
  exact List.length_map _

theorem labelEdges_disjoint {e e' : P.unorientedChains} (h : e ≠ e') :
    Disjoint (P.labelEdges e) (P.labelEdges e') := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  apply h
  have he := P.chainLabel_eq_of_common_edge (P.representative e) (P.representative e')
    (List.mem_toFinset.mp hq) (List.mem_toFinset.mp hq')
  simpa [P.label_representative] using he

theorem edge_mem_labelEdges (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList)
    (q : Edge V d) (hq : q ∈ P.edges) :
    ∃ e : P.unorientedChains, q ∈ P.labelEdges e := by
  have hm : q ∈ cs.flatMap P.chainEdges := by
    rw [←P.edgeList_eq_flatMap_chainEdges cs hcs]
    exact List.mem_toFinset.mp hq
  obtain ⟨c,hc,hqc⟩ := List.mem_flatMap.mp hm
  refine ⟨P.chainLabel c,List.mem_toFinset.mpr ?_⟩
  exact P.chainEdges_mem_of_label_eq c (P.representative (P.chainLabel c))
    (P.label_representative _).symm hqc

theorem labelEdges_subset (e : P.unorientedChains) : P.labelEdges e ⊆ P.edges := by
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  exact (Finset.mem_product.mp (P.toCore_mem (P.representative e).property.1 ha)).1

theorem singletonEdges_eq_biUnion (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) :
    HaarPathMultiplicity.singletonEdges P.edgeList =
      (Finset.univ.filter (fun e => (cs.map P.chainLabel).count e = 1)).biUnion
        P.labelEdges := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqe,hcount⟩ := Finset.mem_filter.mp hq
    obtain ⟨e,he⟩ := P.edge_mem_labelEdges cs hcs q hqe
    refine Finset.mem_biUnion.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,he⟩
    have hh := P.edge_count_eq_chain_count cs hcs (P.representative e)
      (List.mem_toFinset.mp he)
    have hcount' : P.edgeList.count q=1 := by
      simpa only [List.count_eq_countP,Bool.beq_eq_decide_eq] using hcount
    simpa [P.label_representative] using hh.symm.trans hcount'
  · intro hq
    obtain ⟨e,he,hqe⟩ := Finset.mem_biUnion.mp hq
    refine Finset.mem_filter.mpr ⟨P.labelEdges_subset e hqe,?_⟩
    have hh := P.edge_count_eq_chain_count cs hcs (P.representative e)
      (List.mem_toFinset.mp hqe)
    simpa only [List.count_eq_countP,Bool.beq_eq_decide_eq] using hh.trans
      (by simpa [P.label_representative] using (Finset.mem_filter.mp he).2)

/-- Exact transfer of the original singleton budget to compressed labels. -/
theorem singletonEdges_card_eq_chain_lengths (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) :
    (HaarPathMultiplicity.singletonEdges P.edgeList).card =
      ∑ e ∈ Finset.univ.filter (fun e => (cs.map P.chainLabel).count e = 1),
        (P.representative e).val.length := by
  rw [P.singletonEdges_eq_biUnion cs hcs]
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun e he => P.labelEdges_card e)
  · intro e he e' he' hne
    exact P.labelEdges_disjoint hne

end Nonadditivity.HaarPathGraph.Path
