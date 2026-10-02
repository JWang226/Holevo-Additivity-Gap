/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTransport

/-! # The genuine refined equivalence of Haar paths

The original local-color equivalence is refined by equality of the actual
signed-color profiles on corresponding suppressed chains.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

namespace SamePattern
variable {P Q R : Path V d m}

theorem refl (P : Path V d m) : SamePattern P P := samePattern_equivalence.refl P

theorem trans (h : SamePattern P Q) (k : SamePattern Q R) : SamePattern P R :=
  samePattern_equivalence.trans h k

theorem dartPerm_refl {P : Path V d m} {q : Dart V d} (hq : q ∈ P.darts) :
    (refl P).dartPerm q=q := by
  obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
  exact (refl P).dartPerm_apply a

theorem dartPerm_trans (h : SamePattern P Q) (k : SamePattern Q R)
    {q : Dart V d} (hq : q ∈ P.darts) :
    (h.trans k).dartPerm q=k.dartPerm (h.dartPerm q) := by
  obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
  rw [h.dartPerm_apply,k.dartPerm_apply,(h.trans k).dartPerm_apply]

@[simp] theorem coreChainMap_refl (P : Path V d m) (c : P.CoreChain) :
    (refl P).coreChainMap c=c := by
  apply Subtype.ext
  change c.val.map (refl P).dartPerm=c.val
  calc
    _ = c.val.map id := List.map_congr_left (fun q hq => dartPerm_refl (P.toCore_mem c.property.1 hq))
    _ = _ := List.map_id _

theorem coreChainMap_trans (h : SamePattern P Q) (k : SamePattern Q R) (c : P.CoreChain) :
    (h.trans k).coreChainMap c=k.coreChainMap (h.coreChainMap c) := by
  apply Subtype.ext
  simp only [coreChainMap_val,List.map_map]
  exact List.map_congr_left (fun q hq => h.dartPerm_trans k (P.toCore_mem c.property.1 hq))

theorem color_dartPerm_of_colors_eq (h : SamePattern P Q) (hc : P.colors=Q.colors)
    {q : Dart V d} (hq : q ∈ P.darts) : color (h.dartPerm q)=color q := by
  obtain ⟨a,rfl⟩ := exists_incidenceDart P hq
  simp only [h.dartPerm_apply,color_incidenceDart,incidenceColor,hc]

end SamePattern

/-- BC's refined relation, using actual corresponding core chains. The
existential witness is a proof of the already established coarse relation. -/
def RefinedPattern (P Q : Path V d m) : Prop :=
  ∃ h : SamePattern P Q, ∀ c : P.CoreChain,
    P.coreChainProfile c=Q.coreChainProfile (h.coreChainEquiv c)


/-- Chain profiles depend only on the literal color word. -/
theorem coreChainProfile_eq_of_colorList_eq {P Q : Path V d m}
    (c : P.CoreChain) (c' : Q.CoreChain) (h : c.val.map color=c'.val.map color) :
    P.coreChainProfile c=Q.coreChainProfile c' := by
  obtain ⟨a,l,he,ha⟩ := c.property.2
  obtain ⟨b,r,he',hb⟩ := c'.property.2
  have hl : color a=color b ∧ l.map color=r.map color := by simpa [he,he'] using h
  apply Subtype.ext
  simp only [Path.coreChainProfile,he,he',List.head_cons,List.tail_cons]
  rw [hl.1,hl.2]

namespace RefinedPattern
variable {P Q R : Path V d m}

theorem samePattern (h : RefinedPattern P Q) : SamePattern P Q := h.choose

theorem profile_eq (h : RefinedPattern P Q) (c : P.CoreChain) :
    P.coreChainProfile c=Q.coreChainProfile (h.samePattern.coreChainEquiv c) := h.choose_spec c

/-- Keeping the literal colors fixed leaves all refined chain profiles fixed;
only the injective vertex labels change. -/
theorem of_colors_eq (h : SamePattern P Q) (hc : P.colors=Q.colors) : RefinedPattern P Q := by
  refine ⟨h,fun c => ?_⟩
  apply coreChainProfile_eq_of_colorList_eq
  simp only [SamePattern.coreChainEquiv_apply,SamePattern.coreChainMap_val,List.map_map]
  symm
  exact List.map_congr_left (fun q hq => h.color_dartPerm_of_colors_eq hc (P.toCore_mem c.property.1 hq))

theorem refl (P : Path V d m) : RefinedPattern P P := by
  refine ⟨SamePattern.refl P,fun c => ?_⟩
  simp

theorem symm (h : RefinedPattern P Q) : RefinedPattern Q P := by
  obtain ⟨h,hp⟩ := h
  refine ⟨h.symm,fun c => ?_⟩
  change Q.coreChainProfile c=P.coreChainProfile (h.symm.coreChainMap c)
  calc
    _ = Q.coreChainProfile (h.coreChainMap (h.symm.coreChainMap c)) :=
      congrArg Q.coreChainProfile (h.coreChainEquiv.right_inv c).symm
    _ = _ := (hp (h.symm.coreChainMap c)).symm

theorem trans (h : RefinedPattern P Q) (k : RefinedPattern Q R) : RefinedPattern P R := by
  obtain ⟨h,hp⟩ := h
  obtain ⟨k,kp⟩ := k
  refine ⟨h.trans k,fun c => ?_⟩
  calc
    _ = Q.coreChainProfile (h.coreChainEquiv c) := hp c
    _ = R.coreChainProfile (k.coreChainEquiv (h.coreChainEquiv c)) := kp _
    _ = _ := congrArg R.coreChainProfile (h.coreChainMap_trans k c).symm

end RefinedPattern

theorem refinedPattern_equivalence : Equivalence (@RefinedPattern V _ _ d m) :=
  ⟨RefinedPattern.refl,RefinedPattern.symm,RefinedPattern.trans⟩

def refinedPathSetoid : Setoid (Path V d m) := ⟨RefinedPattern,refinedPattern_equivalence⟩

/-- The actual refined quotient whose fibres appear in the operator estimate. -/
abbrev RefinedClass (V : Type*) [Fintype V] [DecidableEq V] (d m : ℕ) :=
  Quotient (@refinedPathSetoid V _ _ d m)

end Nonadditivity.HaarPathClasses
