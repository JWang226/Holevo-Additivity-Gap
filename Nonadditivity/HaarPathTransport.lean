/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClassData
import Nonadditivity.HaarPathChainProfiles
import Nonadditivity.HaarPathDecomposition

/-! # Transport of the actual suppressed graph under path equivalence -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

def incidenceDart (P : Path V d m) (a : Incidence m) : Dart V d :=
  if a.2 then P.traversal a.1 else reverse (P.traversal a.1)

def flipIncidence (a : Incidence m) : Incidence m := (a.1,!a.2)

@[simp] theorem source_incidenceDart (P : Path V d m) (a : Incidence m) :
    source (incidenceDart P a)=incidenceVertex P a := by
  obtain ⟨i,b⟩ := a
  cases b <;> simp [incidenceDart,incidenceVertex,Path.traversal]

@[simp] theorem color_incidenceDart (P : Path V d m) (a : Incidence m) :
    color (incidenceDart P a)=incidenceColor P a := by
  obtain ⟨i,b⟩ := a
  cases b <;> simp [incidenceDart,incidenceColor,Path.traversal]

@[simp] theorem incidenceDart_flip (P : Path V d m) (a : Incidence m) :
    incidenceDart P (flipIncidence a)=reverse (incidenceDart P a) := by
  obtain ⟨i,b⟩ := a
  cases b <;> simp [incidenceDart,flipIncidence]

lemma dart_eq_iff_source_color_target (q r : Dart V d) : q=r ↔
    source q=source r ∧ color q=color r ∧ source (reverse q)=source (reverse r) := by
  obtain ⟨⟨x,a,y⟩,b⟩ := q
  obtain ⟨⟨x',a',y'⟩,b'⟩ := r
  cases b <;> cases b' <;> simp [source,color,reverse,Prod.mk.injEq] <;> tauto

lemma incidenceDart_mem (P : Path V d m) (a : Incidence m) : incidenceDart P a ∈ P.darts := by
  obtain ⟨i,b⟩ := a
  cases b
  · exact P.reverse_traversal_mem i
  · exact P.traversal_mem i

lemma exists_incidenceDart (P : Path V d m) {q : Dart V d} (hq : q ∈ P.darts) :
    ∃ a : Incidence m, incidenceDart P a=q := by
  obtain ⟨he,_⟩ := Finset.mem_product.mp hq
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp he)
  obtain ⟨e,b⟩ := q
  change edge (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ)=e at hi
  subst e
  cases hc : P.colors i with
  | mk a c =>
    cases b <;> cases c
    · exact ⟨(i,true),by simp [incidenceDart,Path.traversal,dart,hc]⟩
    · exact ⟨(i,false),by simp [incidenceDart,Path.traversal,dart,reverse,hc]⟩
    · exact ⟨(i,false),by simp [incidenceDart,Path.traversal,dart,reverse,hc]⟩
    · exact ⟨(i,true),by simp [incidenceDart,Path.traversal,dart,hc]⟩

namespace SamePattern
variable {P Q : Path V d m} (h : SamePattern P Q)
include h

theorem incidenceDart_eq_iff (a b : Incidence m) :
    incidenceDart P a=incidenceDart P b ↔ incidenceDart Q a=incidenceDart Q b := by
  simp only [dart_eq_iff_source_color_target, source_incidenceDart,color_incidenceDart,
    ←incidenceDart_flip]
  constructor
  · rintro ⟨hv,hc,ht⟩
    exact ⟨(h.incidenceVertex_iff a b).mp hv,(h.2 a b hv).mp hc,
      (h.incidenceVertex_iff _ _).mp ht⟩
  · rintro ⟨hv,hc,ht⟩
    have hv' := (h.incidenceVertex_iff a b).mpr hv
    exact ⟨hv',(h.2 a b hv').mpr hc,(h.incidenceVertex_iff _ _).mpr ht⟩

/-- Concrete permutations extending the finite observable vertex/dart maps. -/
def vertexPerm : Equiv.Perm V := Classical.choose (exists_perm_of_kernel_eq P.vertex Q.vertex h.1)
def dartPerm : Equiv.Perm (Dart V d) := Classical.choose
  (exists_perm_of_kernel_eq (incidenceDart P) (incidenceDart Q) h.incidenceDart_eq_iff)

@[simp] theorem vertexPerm_apply (i : Fin (m+1)) : h.vertexPerm (P.vertex i)=Q.vertex i :=
  Classical.choose_spec (exists_perm_of_kernel_eq P.vertex Q.vertex h.1) i

@[simp] theorem dartPerm_apply (a : Incidence m) : h.dartPerm (incidenceDart P a)=incidenceDart Q a :=
  Classical.choose_spec
    (exists_perm_of_kernel_eq (incidenceDart P) (incidenceDart Q) h.incidenceDart_eq_iff) a

theorem dartPerm_mem_iff (q : Dart V d) : h.dartPerm q ∈ Q.darts ↔ q ∈ P.darts := by
  constructor
  · intro hq
    obtain ⟨a,ha⟩ := exists_incidenceDart Q hq
    have he : incidenceDart P a=q := h.dartPerm.injective ((h.dartPerm_apply a).trans ha)
    exact he ▸ incidenceDart_mem P a
  · intro hq
    obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
    rw [h.dartPerm_apply]
    exact incidenceDart_mem Q a

theorem source_dartPerm {q : Dart V d} (hq : q ∈ P.darts) :
    source (h.dartPerm q)=h.vertexPerm (source q) := by
  obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
  simp only [dartPerm_apply,source_incidenceDart,incidenceVertex_eq,vertexPerm_apply]

theorem dartPerm_reverse {q : Dart V d} (hq : q ∈ P.darts) :
    h.dartPerm (reverse q)=reverse (h.dartPerm q) := by
  obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
  rw [←incidenceDart_flip,h.dartPerm_apply,h.dartPerm_apply,incidenceDart_flip]

theorem vertexPerm_mem_vertices_iff (v : V) : h.vertexPerm v ∈ Q.vertices ↔ v ∈ P.vertices := by
  simp only [Path.vertices,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,h.vertexPerm.injective ((h.vertexPerm_apply i.castSucc).trans hi)⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i,(h.vertexPerm_apply i.castSucc).symm⟩

/-- The transport preserves incidence degree, including loops twice. -/
theorem degree_vertexPerm (v : V) : Q.degree (h.vertexPerm v)=P.degree v := by
  have he : Q.darts.filter (fun q => source q=h.vertexPerm v) =
      (P.darts.filter (fun q => source q=v)).image h.dartPerm := by
    ext q
    constructor
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      let r := h.dartPerm.symm q
      have hr : r ∈ P.darts := (h.dartPerm_mem_iff r).mp (by simpa [r] using hq'.1)
      refine Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,?_⟩,by simp [r]⟩
      apply h.vertexPerm.injective
      rw [←h.source_dartPerm hr]
      simpa [r] using hq'.2
    · rintro hq
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hr,hs⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨(h.dartPerm_mem_iff r).mpr hr,by rw [h.source_dartPerm hr,hs]⟩
  unfold Path.degree
  rw [he,Finset.card_image_of_injective _ h.dartPerm.injective]

theorem vertexPerm_mem_core_iff (v : V) :
    h.vertexPerm v ∈ Q.coreVertices ↔ v ∈ P.coreVertices := by
  simp only [Path.coreVertices,Finset.mem_filter,h.vertexPerm_mem_vertices_iff,
    h.degree_vertexPerm,←h.vertexPerm_apply 0,h.vertexPerm.injective.eq_iff]

theorem source_reverse_dartPerm {q : Dart V d} (hq : q ∈ P.darts) :
    source (reverse (h.dartPerm q))=h.vertexPerm (source (reverse q)) := by
  rw [←h.dartPerm_reverse hq]
  exact h.source_dartPerm (P.reverse_mem hq)

/-- Degree-two stopping chains are preserved as literal lists of transported darts. -/
theorem toCore_map {l : List (Dart V d)} (hl : P.ToCore l) :
    Q.ToCore (l.map h.dartPerm) := by
  induction hl with
  | last a ha hc =>
    apply Path.ToCore.last
    · exact (h.dartPerm_mem_iff a).mpr ha
    · rw [h.source_reverse_dartPerm ha]
      exact (h.vertexPerm_mem_core_iff _).mpr hc
  | cons a b l ha hc hj hr ht ih =>
    apply Path.ToCore.cons
    · exact (h.dartPerm_mem_iff a).mpr ha
    · rw [h.source_reverse_dartPerm ha,h.vertexPerm_mem_core_iff]
      exact hc
    · rw [h.source_reverse_dartPerm ha,h.source_dartPerm (P.toCore_head_mem ht),hj]
    · rw [←h.dartPerm_reverse ha]
      exact fun he => hr (h.dartPerm.injective he)
    · exact ih

/-- Transport of a complete oriented chain, including both core endpoints. -/
def coreChainMap (c : P.CoreChain) : Q.CoreChain := by
  refine ⟨c.val.map h.dartPerm,h.toCore_map c.property.1,?_⟩
  obtain ⟨a,l,he,hc⟩ := c.property.2
  have ha : a ∈ P.darts := P.toCore_head_mem (he ▸ c.property.1)
  refine ⟨h.dartPerm a,l.map h.dartPerm,by simp [he],?_⟩
  rw [h.source_dartPerm ha,h.vertexPerm_mem_core_iff]
  exact hc

@[simp] theorem coreChainMap_val (c : P.CoreChain) :
    (h.coreChainMap c).val=c.val.map h.dartPerm := rfl

@[simp] theorem coreChainMap_length (c : P.CoreChain) :
    (h.coreChainMap c).val.length=c.val.length := by simp

theorem symm : SamePattern Q P := samePattern_equivalence.symm h

theorem dartPerm_symm_apply {q : Dart V d} (hq : q ∈ P.darts) :
    h.symm.dartPerm (h.dartPerm q)=q := by
  obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
  rw [h.dartPerm_apply,h.symm.dartPerm_apply]

theorem coreChainMap_symm_apply (c : P.CoreChain) : h.symm.coreChainMap (h.coreChainMap c)=c := by
  apply Subtype.ext
  simp only [coreChainMap_val,List.map_map]
  calc
    _ = c.val.map id := List.map_congr_left (fun q hq =>
      h.dartPerm_symm_apply (P.toCore_mem c.property.1 hq))
    _ = _ := List.map_id _

/-- The actual bijection of oriented suppressed chains. -/
def coreChainEquiv : P.CoreChain ≃ Q.CoreChain where
  toFun := h.coreChainMap
  invFun := h.symm.coreChainMap
  left_inv := h.coreChainMap_symm_apply
  right_inv c := by
    have he := h.symm.coreChainMap_symm_apply c
    convert he using 1

@[simp] theorem coreChainEquiv_apply (c : P.CoreChain) : h.coreChainEquiv c=h.coreChainMap c := rfl

/-- Orientation reversal commutes with the transported chain bijection. -/
theorem coreChainMap_reverse (c : P.CoreChain) :
    h.coreChainMap (P.coreChainReverse c)=Q.coreChainReverse (h.coreChainMap c) := by
  apply Subtype.ext
  change (c.val.reverse.map reverse).map h.dartPerm=(c.val.map h.dartPerm).reverse.map reverse
  simp only [List.map_map,List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro q hq
  exact h.dartPerm_reverse (P.toCore_mem c.property.1 hq)

/-- Transport is pointwise in the original traversal time. -/
@[simp] theorem dartPerm_traversal (i : Fin m) : h.dartPerm (P.traversal i)=Q.traversal i :=
  h.dartPerm_apply (i,true)

theorem traversalList_map : P.traversalList.map h.dartPerm=Q.traversalList := by
  simp only [Path.traversalList,List.map_ofFn]
  congr 1
  funext i
  exact h.dartPerm_traversal i

/-- Every chain occurrence and every cut position is transported unchanged.
The chain colors may change; its length and traversal interval do not. -/
theorem chain_decomposition_map (cs : List P.CoreChain)
    (hc : (cs.map Subtype.val).flatten=P.traversalList) :
    ((cs.map h.coreChainMap).map Subtype.val).flatten=Q.traversalList := by
  rw [←h.traversalList_map,←hc,List.map_flatten]
  simp only [List.map_map,coreChainMap_val,Function.comp_def]
  rfl

end SamePattern
end Nonadditivity.HaarPathClasses
