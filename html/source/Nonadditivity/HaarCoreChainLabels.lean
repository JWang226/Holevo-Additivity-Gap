/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChainPartition
import Nonadditivity.HaarPathCoefficientWords

/-! # Literal unoriented labels of the actual core-chain occurrence sequence

Every compressed edge occurs in the path, and the two orientations have the
same label. Thus the number of variables in the endpoint sum is exactly the
number of unoriented core edges, rather than the number of traversals.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarPathGraph.Path

variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- The literal orientation-free label of a core-chain occurrence. -/
def chainLabel (c : P.CoreChain) : P.unorientedChains :=
  ⟨{c, P.coreChainReverse c}, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem chainLabel_reverse (c : P.CoreChain) :
    P.chainLabel (P.coreChainReverse c) = P.chainLabel c := by
  apply Subtype.ext
  change {P.coreChainReverse c, P.coreChainReverse (P.coreChainReverse c)} =
    {c, P.coreChainReverse c}
  rw [P.coreChainReverse_involutive]
  exact Finset.pair_comm _ _

/-- Every orientation of every graph edge is either an original traversal
or the reverse of an original traversal. -/
theorem dart_eq_traversal_or_reverse (q : Dart V d) (hq : q ∈ P.darts) :
    ∃ i : Fin m, q = P.traversal i ∨ q = reverse (P.traversal i) := by
  have he : q.1 ∈ P.edges := (Finset.mem_product.mp hq).1
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp he)
  have hedge : (P.traversal i).1 = q.1 := hi
  refine ⟨i, ?_⟩
  by_cases hb : q.2 = (P.traversal i).2
  · exact Or.inl (Prod.ext hedge.symm hb)
  · right
    refine Prod.ext (show q.1 = (reverse (P.traversal i)).1 from hedge.symm) ?_
    change q.2 = !(P.traversal i).2
    cases hq2 : q.2 <;> cases ht2 : (P.traversal i).2 <;> simp_all

/-- Every core chain occurs in one of its two orientations in the actual
maximal-chain decomposition. -/
theorem chain_or_reverse_mem_decomposition (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) (c : P.CoreChain) :
    c ∈ cs ∨ P.coreChainReverse c ∈ cs := by
  let q := c.val.head (P.toCore_nonempty c.property.1)
  have hqc : q ∈ c.val := List.head_mem _
  have hq : q ∈ P.darts := P.toCore_mem c.property.1 hqc
  obtain ⟨i,hi | hi⟩ := P.dart_eq_traversal_or_reverse q hq
  · have hmem : q ∈ (cs.map Subtype.val).flatten := by
      rw [hcs, hi]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    obtain ⟨l,hl,hql⟩ := List.mem_flatten.mp hmem
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hl
    have he := P.coreChain_eq_of_common_dart c c' hqc hql
    exact Or.inl (he.symm ▸ hc')
  · have hmem : reverse q ∈ (cs.map Subtype.val).flatten := by
      rw [hcs, hi, reverse_reverse]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    obtain ⟨l,hl,hql⟩ := List.mem_flatten.mp hmem
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hl
    have hrev : reverse q ∈ (P.coreChainReverse c).val := by
      exact List.mem_map.mpr ⟨q,List.mem_reverse.mpr hqc,rfl⟩
    have he := P.coreChain_eq_of_common_dart (P.coreChainReverse c) c' hrev hql
    exact Or.inr (he.symm ▸ hc')

/-- The occurrence sequence covers every actual orientation-free core label. -/
theorem chainLabels_cover (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) :
    ∀ e : P.unorientedChains, ∃ c ∈ cs, P.chainLabel c = e := by
  intro e
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp e.property
  have hel : P.chainLabel c = e := Subtype.ext he
  rcases P.chain_or_reverse_mem_decomposition cs hcs c with hc | hc
  · exact ⟨c,hc,hel⟩
  · exact ⟨P.coreChainReverse c,hc,(P.chainLabel_reverse c).trans hel⟩

/-- There are exactly as many distinct occurrence labels as actual core edges. -/
theorem card_chainLabels (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) :
    (cs.map P.chainLabel).toFinset.card = P.unorientedChains.card := by
  have he : (cs.map P.chainLabel).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    obtain ⟨c,hc,rfl⟩ := P.chainLabels_cover cs hcs e
    exact List.mem_toFinset.mpr (List.mem_map_of_mem hc)
  rw [he, Finset.card_univ, Fintype.card_coe]

/-- Pick one of the two literal orientations of each compressed edge. -/
def representative (e : P.unorientedChains) : P.CoreChain :=
  (show e.val.Nonempty from by
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp e.property
    rw [←he]
    exact ⟨c,by simp⟩).choose

theorem representative_mem (e : P.unorientedChains) : P.representative e ∈ e.val :=
by
  unfold representative
  exact Classical.choose_spec _

theorem label_representative (e : P.unorientedChains) : P.chainLabel (P.representative e) = e := by
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp e.property
  apply Subtype.ext
  exact (HaarPathInvolution.pair_eq_of_mem P.coreChainReverse_involutive
    (he ▸ P.representative_mem e)).trans he

/-- Each actual oriented occurrence is its representative or its reverse. -/
theorem eq_representative_or_reverse (c : P.CoreChain) :
    c = P.representative (P.chainLabel c) ∨
      c = P.coreChainReverse (P.representative (P.chainLabel c)) := by
  have h := P.representative_mem (P.chainLabel c)
  change P.representative (P.chainLabel c) ∈ {c,P.coreChainReverse c} at h
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl h.symm
  · have he := Finset.mem_singleton.mp h
    exact Or.inr (by rw [he,P.coreChainReverse_involutive])

end Nonadditivity.HaarPathGraph.Path
