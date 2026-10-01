/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTree
import Mathlib.Logic.Equiv.Fintype

/-! # Literal vertex-and-local-color path equivalence

BC's first path equivalence simultaneously preserves repeated vertices and
repeated colors at each vertex. Both directions of every traversal are part
of the incidence data. This file constructs the relabelling permutations
from equality patterns; they are not supplied as an assumption.
-/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {A E : Type*}

/-- Equality of two labeling kernels gives an actual bijection of their ranges. -/
def rangeEquivOfKernel (f g : A → E)
    (h : ∀ a b, f a=f b ↔ g a=g b) : Set.range f ≃ Set.range g where
  toFun x := ⟨g (Classical.choose x.property),⟨_,rfl⟩⟩
  invFun y := ⟨f (Classical.choose y.property),⟨_,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have he := Classical.choose_spec x.property
    have he' := Classical.choose_spec
      (show g (Classical.choose x.property) ∈ Set.range g from ⟨_,rfl⟩)
    exact ((h _ _).mpr he').trans he
  right_inv y := by
    apply Subtype.ext
    have he := Classical.choose_spec y.property
    have he' := Classical.choose_spec
      (show f (Classical.choose y.property) ∈ Set.range f from ⟨_,rfl⟩)
    exact ((h _ _).mp he').trans he

theorem rangeEquivOfKernel_apply (f g : A → E)
    (h : ∀ a b, f a=f b ↔ g a=g b) (a : A) :
    (rangeEquivOfKernel f g h ⟨f a,⟨a,rfl⟩⟩).val=g a := by
  exact (h _ _).mp (Classical.choose_spec (show f a∈Set.range f from ⟨a,rfl⟩))

/-- For a finite label alphabet, the range bijection extends to a genuine
permutation of the whole alphabet. -/
theorem exists_perm_of_kernel_eq [Fintype E] (f g : A → E)
    (h : ∀ a b, f a=f b ↔ g a=g b) :
    ∃ σ : Equiv.Perm E, ∀ a, σ (f a)=g a := by
  classical
  let e := rangeEquivOfKernel f g h
  refine ⟨e.extendSubtype,fun a => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (f a) ⟨a,rfl⟩]
  exact rangeEquivOfKernel_apply f g h a

variable {V : Type*} {d m : ℕ}

abbrev Incidence (m : ℕ) := Fin m × Bool

def incidenceVertex (P : Path V d m) (a : Incidence m) : V :=
  if a.2 then P.vertex a.1.castSucc else P.vertex a.1.succ

def incidenceColor (P : Path V d m) (a : Incidence m) : Color d :=
  if a.2 then P.colors a.1 else flipColor (P.colors a.1)

def incidenceIndex (a : Incidence m) : Fin (m+1) :=
  if a.2 then a.1.castSucc else a.1.succ

@[simp] theorem incidenceVertex_eq (P : Path V d m) (a : Incidence m) :
    incidenceVertex P a=P.vertex (incidenceIndex a) := by
  obtain ⟨i,b⟩ := a
  cases b <;> rfl

/-- The exact local-color relabelling relation on actual paths. Requiring
both incidences of each edge is BC's compatibility at its two endpoints. -/
def Relabeled (P Q : Path V d m) : Prop :=
  ∃ τ : Equiv.Perm V, ∃ β : V → Equiv.Perm (Color d),
    (∀ j, τ (P.vertex j)=Q.vertex j) ∧
    ∀ a, β (incidenceVertex P a) (incidenceColor P a)=incidenceColor Q a

/-- Finite observable equality patterns of vertices and local colors. -/
def SamePattern (P Q : Path V d m) : Prop :=
  (∀ i j, P.vertex i=P.vertex j ↔ Q.vertex i=Q.vertex j) ∧
  ∀ a b, incidenceVertex P a=incidenceVertex P b →
    (incidenceColor P a=incidenceColor P b ↔ incidenceColor Q a=incidenceColor Q b)

theorem relabeled_samePattern {P Q : Path V d m} (h : Relabeled P Q) :
    SamePattern P Q := by
  obtain ⟨τ,β,hv,hc⟩ := h
  constructor
  · intro i j
    rw [←hv i,←hv j]
    exact τ.injective.eq_iff.symm
  · intro a b hab
    rw [←hc a,←hc b,hab]
    exact (β (incidenceVertex P b)).injective.eq_iff.symm

/-- Actual construction of all global and local permutations from patterns. -/
theorem samePattern_relabeled [Fintype V] {P Q : Path V d m}
    (h : SamePattern P Q) : Relabeled P Q := by
  classical
  obtain ⟨τ,hτ⟩ := exists_perm_of_kernel_eq P.vertex Q.vertex h.1
  have hlocal (v : V) : ∃ β : Equiv.Perm (Color d),
      ∀ a : {a : Incidence m // incidenceVertex P a=v},
        β (incidenceColor P a.val)=incidenceColor Q a.val := by
    apply exists_perm_of_kernel_eq
    intro a b
    exact h.2 a.val b.val (a.property.trans b.property.symm)
  choose β hβ using hlocal
  refine ⟨τ,β,hτ,fun a => ?_⟩
  exact hβ (incidenceVertex P a) ⟨a,rfl⟩

theorem relabeled_iff_samePattern [Fintype V] (P Q : Path V d m) :
    Relabeled P Q ↔ SamePattern P Q :=
  ⟨relabeled_samePattern,samePattern_relabeled⟩

/-- Coarse path equivalence is an actual equivalence relation. -/
theorem samePattern_equivalence : Equivalence (@SamePattern V d m) := by
  constructor
  · intro P
    exact ⟨fun _ _ => Iff.rfl,fun _ _ _ => Iff.rfl⟩
  · intro P Q h
    refine ⟨fun i j => (h.1 i j).symm,fun a b hab => ?_⟩
    have hbase : incidenceVertex P a=incidenceVertex P b := by
      simp only [incidenceVertex_eq]
      apply (h.1 (incidenceIndex a) (incidenceIndex b)).mpr
      simpa only [incidenceVertex_eq] using hab
    exact (h.2 a b hbase).symm
  · intro P Q R hp hq
    refine ⟨fun i j => (hp.1 i j).trans (hq.1 i j),fun a b hab => ?_⟩
    have hbase : incidenceVertex Q a=incidenceVertex Q b := by
      simp only [incidenceVertex_eq]
      apply (hp.1 (incidenceIndex a) (incidenceIndex b)).mp
      simpa only [incidenceVertex_eq] using hab
    exact (hp.2 a b hab).trans (hq.2 a b hbase)

def pathSetoid : Setoid (Path V d m) := ⟨SamePattern,samePattern_equivalence⟩

/-- The quotient in the path counting problem, with the paper's genuine
relabeling relation characterized above. -/
abbrev PathClass (V : Type*) (d m : ℕ) := Quotient (@pathSetoid V d m)

/-- A finite Boolean code for the entire incidence pattern. This initial
normal form is exact; its later sparse encoding uses exploration marks. -/
def patternCode [DecidableEq V] (P : Path V d m) :
    ((Fin (m+1) × Fin (m+1)) → Bool) × ((Incidence m × Incidence m) → Bool) :=
  (fun p => decide (P.vertex p.1=P.vertex p.2),
   fun p => decide (incidenceVertex P p.1=incidenceVertex P p.2 ∧
     incidenceColor P p.1=incidenceColor P p.2))

theorem patternCode_eq_iff [DecidableEq V] (P Q : Path V d m) :
    patternCode P=patternCode Q ↔ SamePattern P Q := by
  constructor
  · intro h
    have hv : ∀ i j, P.vertex i=P.vertex j ↔ Q.vertex i=Q.vertex j := by
      intro i j
      have he := congrFun (congrArg Prod.fst h) (i,j)
      simpa only [patternCode,decide_eq_decide] using he
    refine ⟨hv,fun a b hab => ?_⟩
    have hab' : incidenceVertex Q a=incidenceVertex Q b := by
      simp only [incidenceVertex_eq]
      apply (hv (incidenceIndex a) (incidenceIndex b)).mp
      simpa only [incidenceVertex_eq] using hab
    have he := congrFun (congrArg Prod.snd h) (a,b)
    simpa only [patternCode,hab,hab',true_and,decide_eq_decide] using he
  · intro h
    apply Prod.ext
    · funext p
      exact decide_eq_decide.mpr (h.1 p.1 p.2)
    · funext p
      apply decide_eq_decide.mpr
      have hv : incidenceVertex P p.1=incidenceVertex P p.2 ↔
          incidenceVertex Q p.1=incidenceVertex Q p.2 := by
        simpa only [incidenceVertex_eq] using h.1 (incidenceIndex p.1) (incidenceIndex p.2)
      constructor
      · rintro ⟨hb,hc⟩
        exact ⟨hv.mp hb,(h.2 p.1 p.2 hb).mp hc⟩
      · rintro ⟨hb,hc⟩
        exact ⟨hv.mpr hb,(h.2 p.1 p.2 (hv.mpr hb)).mpr hc⟩

/-- An injective, actual finite representation of the path quotient. -/
def classPatternCode [DecidableEq V] (C : PathClass V d m) :=
  Quotient.lift patternCode
    (fun _ _ h => (patternCode_eq_iff _ _).mpr h) C

theorem classPatternCode_injective [DecidableEq V] :
    Function.Injective (@classPatternCode V d m _) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h P =>
    induction b using Quotient.inductionOn with
    | h Q =>
      intro he
      apply Quotient.sound
      exact (patternCode_eq_iff P Q).mp he

instance [DecidableEq V] : Fintype (PathClass V d m) :=
  Fintype.ofInjective classPatternCode classPatternCode_injective

end Nonadditivity.HaarPathClasses
