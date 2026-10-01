/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathMarks
import Nonadditivity.HaarPathNormalizedFresh

/-! # Reconstruction of the normalized data from sparse exploration marks

Pointwise prefix data are stronger than path equivalence. Each important
mark extends those data by one step; the tree and fresh-run bridges then
reconstruct the intervening unmarked steps.
-/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {m : ℕ}
variable {P Q : Path V 2 m}

/-- Literal equality of all normalized data in the decoded prefix. -/
def NormalizedPrefixEq (P Q : Path V 2 m) (hm : 0 < m) (k : ℕ) : Prop :=
  (∀ j : Fin (m+1), j.val ≤ k → P.vertexName hm j=Q.vertexName hm j) ∧
  ∀ a : Incidence m, a.1.val < k → normalColor P hm a=normalColor Q hm a

theorem normalizedPrefixEq_zero (P Q : Path V 2 m) (hm : 0 < m) :
    NormalizedPrefixEq P Q hm 0 := by
  constructor
  · intro j hj
    have he : j=0 := Fin.ext (by change j.val=0; omega)
    subst j
    rw [P.vertexName_root hm,Q.vertexName_root hm]
  · intro a ha
    omega

theorem normalizedPrefixEq_mono (hm : 0 < m) {j k : ℕ}
    (h : NormalizedPrefixEq P Q hm k) (hjk : j ≤ k) : NormalizedPrefixEq P Q hm j :=
  ⟨fun a ha => h.1 a (ha.trans hjk),fun a ha => h.2 a (ha.trans_le hjk)⟩

theorem normalizedPrefixEq_full (hm : 0 < m)
    (h : NormalizedPrefixEq P Q hm m) : SamePattern P Q := by
  apply samePattern_of_named_data hm (colorNormalizer P hm) (colorNormalizer Q hm)
  · intro j
    exact h.1 j (by omega)
  · intro a
    exact h.2 a a.1.isLt

/-- Extend by an actual step once its target and two incidence labels are
known. This covers important edges, including loops and repeated edges. -/
theorem normalizedPrefixEq_extend (hm : 0 < m) (i : Fin m)
    (hp : NormalizedPrefixEq P Q hm i.val)
    (ht : P.vertexName hm i.succ=Q.vertexName hm i.succ)
    (hc : ∀ b : Bool, normalColor P hm (i,b)=normalColor Q hm (i,b)) :
    NormalizedPrefixEq P Q hm (i.val+1) := by
  constructor
  · intro j hj
    by_cases hj' : j.val ≤ i.val
    · exact hp.1 j hj'
    · have he : j=i.succ := Fin.ext (by simp; omega)
      subst j
      exact ht
  · rintro ⟨j,b⟩ hj
    by_cases hj' : j.val < i.val
    · exact hp.2 (j,b) hj'
    · have he : j=i := Fin.ext (by change j.val < i.val+1 at hj; omega)
      subst j
      exact hc b

/-- Projection of the actual sparse mark supplies all data of an important
step, using no lookup in the unreconstructed final graph. -/
theorem normalizedPrefixEq_extend_mark (hm : 0 < m) (i : Fin m)
    (hp : NormalizedPrefixEq P Q hm i.val)
    (hmark : explorationMark P hm i=explorationMark Q hm i) :
    NormalizedPrefixEq P Q hm (i.val+1) := by
  apply normalizedPrefixEq_extend hm i hp
  · exact congrArg Prod.fst hmark
  · intro b
    cases b
    · exact congrArg (fun x : ExplorationMark m => x.2.2.2.1) hmark
    · exact congrArg (fun x : ExplorationMark m => x.2.2.1) hmark

theorem nextImportant_eq_of_eventList_eq (hm : 0 < m)
    (h : explorationEventList P hm=explorationEventList Q hm) (a : ℕ) :
    P.nextImportant a=Q.nextImportant a := by
  have hi := importantTimes_eq_of_eventList_eq hm h
  simp only [Path.nextImportant,Path.importantStops,hi]

theorem normalizer_freshNormalization (P : Path V 2 m) (hm : 0 < m) :
    FreshNormalization P (colorNormalizer P hm) initialColor nextColor := by
  constructor
  · intro i hi
    exact normalColor_incoming P hm i hi
  · intro i j hi hij
    have hv : j.castSucc=i.succ := Fin.ext (by simpa using hij.symm)
    simpa only [normalColor,normalizedIncidenceColor,incidenceVertex,incidenceColor,
      if_true,hv] using normalColor_after_firstVisit P hm i j hi hij

end Nonadditivity.HaarPathClasses
