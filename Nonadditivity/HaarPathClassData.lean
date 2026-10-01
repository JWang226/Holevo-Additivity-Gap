/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClasses

/-! # Exploration statistics descend to the actual path quotient

Repeated colored edges, discovery times, important times and the defect are
invariant under the literal vertex-and-local-color equivalence.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph
variable {V : Type*} {d : ℕ}

theorem edge_eq_iff {x y x' y' : V} {c c' : HaarPathProfiles.Color d} :
    edge x c y=edge x' c' y' ↔
      (x=x' ∧ c=c' ∧ y=y') ∨ (x=y' ∧ c=flipColor c' ∧ y=x') := by
  obtain ⟨g,b⟩ := c
  obtain ⟨g',b'⟩ := c'
  cases b <;> cases b' <;> simp [edge,flipColor,Prod.mk.injEq]
  all_goals tauto
end Nonadditivity.HaarPathGraph

namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} {d m : ℕ} [DecidableEq V]
variable {P Q : Path V d m}

namespace SamePattern

theorem incidenceVertex_iff (h : SamePattern P Q) (a b : Incidence m) :
    incidenceVertex P a=incidenceVertex P b ↔
      incidenceVertex Q a=incidenceVertex Q b := by
  simpa only [incidenceVertex_eq] using h.1 (incidenceIndex a) (incidenceIndex b)

theorem firstVisit_iff (h : SamePattern P Q) (i : Fin m) :
    P.FirstVisit i ↔ Q.FirstVisit i := by
  simp only [Path.FirstVisit]
  constructor
  · intro hi j hj he
    exact hi j hj ((h.1 j i.succ).mpr he)
  · intro hi j hj he
    exact hi j hj ((h.1 j i.succ).mp he)

theorem firstTimes_eq (h : SamePattern P Q) : P.firstTimes=Q.firstTimes := by
  ext i
  simpa only [Path.mem_firstTimes] using h.firstVisit_iff i

theorem edgeAt_eq_iff (h : SamePattern P Q) (i j : Fin m) :
    P.edgeAt i=P.edgeAt j ↔ Q.edgeAt i=Q.edgeAt j := by
  simp only [Path.edgeAt,edge_eq_iff]
  have hf : P.vertex i.castSucc=P.vertex j.castSucc →
      (P.colors i=P.colors j ↔ Q.colors i=Q.colors j) := by
    intro hv
    exact h.2 (i,true) (j,true) hv
  have hr : P.vertex i.castSucc=P.vertex j.succ →
      (P.colors i=flipColor (P.colors j) ↔ Q.colors i=flipColor (Q.colors j)) := by
    intro hv
    exact h.2 (i,true) (j,false) hv
  constructor
  · rintro (⟨hs,hc,ht⟩ | ⟨hs,hc,ht⟩)
    · exact Or.inl ⟨(h.1 _ _).mp hs,(hf hs).mp hc,(h.1 _ _).mp ht⟩
    · exact Or.inr ⟨(h.1 _ _).mp hs,(hr hs).mp hc,(h.1 _ _).mp ht⟩
  · rintro (⟨hs,hc,ht⟩ | ⟨hs,hc,ht⟩)
    · have hs' := (h.1 _ _).mpr hs
      exact Or.inl ⟨hs',(hf hs').mpr hc,(h.1 _ _).mpr ht⟩
    · have hs' := (h.1 _ _).mpr hs
      exact Or.inr ⟨hs',(hr hs').mpr hc,(h.1 _ _).mpr ht⟩

theorem edgeAt_mem_treeEdges_iff (h : SamePattern P Q) (i : Fin m) :
    P.edgeAt i∈P.treeEdges ↔ Q.edgeAt i∈Q.treeEdges := by
  simp only [Path.treeEdges,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,h.firstTimes_eq ▸ hj,(h.edgeAt_eq_iff j i).mp he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,h.firstTimes_eq.symm ▸ hj,(h.edgeAt_eq_iff j i).mpr he⟩

theorem importantTimes_eq (h : SamePattern P Q) : P.importantTimes=Q.importantTimes := by
  ext i
  simp only [Path.importantTimes,Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr (h.edgeAt_mem_treeEdges_iff i)

theorem vertices_card_eq (h : SamePattern P Q) (hm : 0 < m) :
    P.vertices.card=Q.vertices.card := by
  have hp := P.card_firstTimes hm
  have hq := Q.card_firstTimes hm
  rw [h.firstTimes_eq] at hp
  omega

end SamePattern

/-- Relabeling an arbitrary edge list by a bijection preserves its exact
singleton count; the statement is about literal multiplicities. -/
theorem singletonEdges_map_card {E : Type*} [DecidableEq E]
    (l : List E) (σ : Equiv.Perm E) :
    (HaarPathMultiplicity.singletonEdges (l.map σ)).card =
      (HaarPathMultiplicity.singletonEdges l).card := by
  classical
  have he : HaarPathMultiplicity.singletonEdges (l.map σ) =
      (HaarPathMultiplicity.singletonEdges l).image σ := by
    ext e
    simp only [HaarPathMultiplicity.singletonEdges,Finset.mem_filter,List.mem_toFinset,
      List.mem_map,Finset.mem_image]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hc⟩
      refine ⟨x,⟨hx,?_⟩,rfl⟩
      simpa only [List.count_map_of_injective l σ σ.injective] using hc
    · rintro ⟨x,⟨hx,hc⟩,rfl⟩
      refine ⟨⟨x,hx,rfl⟩,?_⟩
      simpa only [List.count_map_of_injective l σ σ.injective] using hc
  rw [he,Finset.card_image_of_injective _ σ.injective]

namespace SamePattern

theorem singleton_card_eq [Fintype V] (h : SamePattern P Q) :
    (HaarPathMultiplicity.singletonEdges P.edgeList).card =
      (HaarPathMultiplicity.singletonEdges Q.edgeList).card := by
  obtain ⟨σ,hσ⟩ := exists_perm_of_kernel_eq P.edgeAt Q.edgeAt h.edgeAt_eq_iff
  have he : P.edgeList.map σ=Q.edgeList := by
    simp only [Path.edgeList,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact hσ i
  rw [←he,singletonEdges_map_card]

theorem defectTwice_eq [Fintype V] (h : SamePattern P Q) (hm : 0 < m) :
    P.defectTwice=Q.defectTwice := by
  simp only [Path.defectTwice,h.vertices_card_eq hm,h.singleton_card_eq]

end SamePattern

/-- The important-position finset is an honest function on BC path classes. -/
def classImportantTimes (C : PathClass V d m) : Finset (Fin m) :=
  Quotient.lift Path.importantTimes
    (fun _ _ (h : SamePattern _ _) => h.importantTimes_eq) C

/-- The defect is an honest function on nonempty path classes. -/
def classDefectTwice [Fintype V] (hm : 0 < m) (C : PathClass V d m) : ℕ :=
  Quotient.lift Path.defectTwice
    (fun _ _ (h : SamePattern _ _) => h.defectTwice_eq hm) C

/-- The corrected exploration budget holds directly on genuine equivalence
classes, with no representative or graph invariant supplied by the caller. -/
theorem classImportantTimes_card_le [Fintype V] (hm : 0 < m) (C : PathClass V d m) :
    (classImportantTimes C).card ≤ classDefectTwice hm C+2 := by
  induction C using Quotient.inductionOn with
  | h P => exact P.card_importantTimes_le hm

end Nonadditivity.HaarPathClasses
