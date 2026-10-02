/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarRepresentativePositions
import Nonadditivity.HaarCoreChainMultiplicity
import Nonadditivity.HaarCoreChainEndpoints

/-! # Reversal-coherent reindexing inside unoriented core edges -/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

def representativeReindex (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length)) : Equiv.Perm P.RepresentativePosition where
  toFun p := ⟨p.1,σ p.1 p.2.1,p.2.2⟩
  invFun p := ⟨p.1,(σ p.1).symm p.2.1,p.2.2⟩
  left_inv := by rintro ⟨e,i,b⟩; simp
  right_inv := by rintro ⟨e,i,b⟩; simp

/-- Reindex the positions of each unoriented edge, simultaneously and coherently
in its two orientations. -/
def chainReindex (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length)) : Equiv.Perm P.darts :=
  P.representativePositionEquiv.symm.trans
    ((P.representativeReindex σ).trans P.representativePositionEquiv)

@[simp] theorem chainReindex_apply_position (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length))
    (e : P.unorientedChains) (i : Fin (P.representative e).val.length) (b : Bool) :
    P.chainReindex σ (P.representativePositionEquiv ⟨e,i,b⟩)=
      P.representativePositionEquiv ⟨e,σ e i,b⟩ := by
  simp only [chainReindex,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem chainReindex_reverse (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length)) (q : P.darts) :
    P.chainReindex σ ⟨reverse q.val,P.reverse_mem q.property⟩ =
      ⟨reverse (P.chainReindex σ q).val,P.reverse_mem (P.chainReindex σ q).property⟩ := by
  obtain ⟨⟨e,i,b⟩,rfl⟩ := P.representativePositionEquiv.surjective q
  rw [←P.representativePositionEquiv_reverse,P.chainReindex_apply_position,
    P.chainReindex_apply_position,P.representativePositionEquiv_reverse]

/-- Directed traversal multiplicity is constant along a chain, so arbitrary
reindexing within that chain preserves the literal number of occurrences. -/
theorem chainReindex_count (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length)) (q : P.darts) :
    P.traversalList.count q.val=P.traversalList.count (P.chainReindex σ q).val := by
  obtain ⟨j,hj⟩ := P.dart_eq_traversal_or_reverse q.val q.property
  have hm : 0<m := Nat.zero_lt_of_lt j.isLt
  obtain ⟨⟨e,i,b⟩,rfl⟩ := P.representativePositionEquiv.surjective q
  rw [P.chainReindex_apply_position]
  simp only [P.representativePositionEquiv_val]
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    apply P.traversal_count_constant_on_chain hm (P.coreChainReverse (P.representative e))
    · exact List.mem_map.mpr ⟨_,List.mem_reverse.mpr (List.get_mem _ _),rfl⟩
    · exact List.mem_map.mpr ⟨_,List.mem_reverse.mpr (List.get_mem _ _),rfl⟩
  · simp only [ite_true]
    exact P.traversal_count_constant_on_chain hm (P.representative e)
      (List.get_mem _ _) (List.get_mem _ _)

/-- Fixing the chain endpoints fixes every dart whose source is a core vertex. -/
theorem chainReindex_fixed_core (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length))
    (hfix : ∀ e i, (i.val=0 ∨ i.val+1=(P.representative e).val.length) → σ e i=i)
    (q : P.darts) (hq : source q.val∈P.coreVertices) : P.chainReindex σ q=q := by
  obtain ⟨⟨e,i,b⟩,rfl⟩ := P.representativePositionEquiv.surjective q
  rw [P.chainReindex_apply_position]
  have hi : i.val=0 ∨ i.val+1=(P.representative e).val.length := by
    rw [P.representativePositionEquiv_val] at hq
    cases b
    · exact Or.inr ((P.coreChain_reverse_source_mem_core_iff _ _).mp hq)
    · exact Or.inl ((P.coreChain_source_mem_core_iff _ _).mp hq)
  rw [hfix e i hi]

theorem chainReindex_mem_core_iff (σ : ∀ e : P.unorientedChains,
    Equiv.Perm (Fin (P.representative e).val.length))
    (hfix : ∀ e i, (i.val=0 ∨ i.val+1=(P.representative e).val.length) → σ e i=i)
    (q : P.darts) : source (P.chainReindex σ q).val∈P.coreVertices ↔ source q.val∈P.coreVertices := by
  constructor
  · intro hc
    have hfixed := P.chainReindex_fixed_core σ hfix (P.chainReindex σ q) hc
    have he := (P.chainReindex σ).injective hfixed
    simpa only [he] using hc
  · intro hc
    rw [P.chainReindex_fixed_core σ hfix q hc]
    exact hc

end Nonadditivity.HaarPathGraph.Path
