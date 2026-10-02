/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathFreshRuns

/-! # Literal finite marks for outgoing color classes

An outgoing color is encoded by its least matching prior incidence, or by a
fresh-color sentinel. Equality of these concrete finite codes reconstructs
the full outgoing-color equality pattern. The honest alphabet has `2m+1`
members; no smaller cardinality is assumed.
-/

noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles

variable {V : Type*} [DecidableEq V] {d m : ℕ}

def incidenceRank (a : Incidence m) : ℕ := 2*a.1.val + if a.2 then 1 else 0

theorem incidenceRank_injective : Function.Injective (@incidenceRank m) := by
  rintro ⟨a,ab⟩ ⟨b,bb⟩ he
  cases ab <;> cases bb <;> simp [incidenceRank] at he
  · have h : a=b := Fin.ext (by omega)
    simp [h]
  · omega
  · omega
  · have h : a=b := Fin.ext (by omega)
    simp [h]

local instance incidenceOrder : LinearOrder (Incidence m) :=
  LinearOrder.lift' incidenceRank incidenceRank_injective

/-- Previous incidences at this vertex carrying the new outgoing color. -/
def matchingIncidences (P : Path V d m) (i : Fin m) : Finset (Incidence m) :=
  Finset.univ.filter fun a => a.1.val < i.val ∧
    incidenceVertex P a=P.vertex i.castSucc ∧ incidenceColor P a=P.colors i

@[simp] theorem mem_matchingIncidences (P : Path V d m) (i : Fin m) (a : Incidence m) :
    a ∈ matchingIncidences P i ↔ a.1.val < i.val ∧
      incidenceVertex P a=P.vertex i.castSucc ∧ incidenceColor P a=P.colors i := by
  simp [matchingIncidences]

/-- The least previous matching incidence, with `none` for a new color. -/
def outgoingCode (P : Path V d m) (i : Fin m) : Option (Incidence m) :=
  if h : (matchingIncidences P i).Nonempty then
    some ((matchingIncidences P i).min' h) else none

theorem outgoingCode_some_mem (P : Path V d m) (i : Fin m) (a : Incidence m)
    (h : outgoingCode P i=some a) : a ∈ matchingIncidences P i := by
  unfold outgoingCode at h
  split_ifs at h with hn
  · have he := Option.some.inj h
    rw [←he]
    exact Finset.min'_mem _ _

theorem outgoingCode_none_iff (P : Path V d m) (i : Fin m) :
    outgoingCode P i=none ↔ matchingIncidences P i=∅ := by
  unfold outgoingCode
  split_ifs with hn
  · simp [hn.ne_empty]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

theorem outgoingCode_some_le (P : Path V d m) (i : Fin m) (a b : Incidence m)
    (ha : outgoingCode P i=some a) (hb : b∈matchingIncidences P i) :
    incidenceRank a ≤ incidenceRank b := by
  have hn : (matchingIncidences P i).Nonempty := ⟨b,hb⟩
  have he : (matchingIncidences P i).min' hn=a := by
    simpa [outgoingCode, hn] using ha
  rw [←he]
  exact Finset.min'_le _ _ hb

/-- This is an explicit bound for the actual mark type. -/
theorem outgoingCode_alphabet_card : Fintype.card (Option (Incidence m))=2*m+1 := by
  simp [Nat.mul_comm]

/-- Equality of finite marks recovers every outgoing-color comparison. -/
theorem outgoingMark_of_code_eq (P Q : Path V d m) (i : Fin m)
    (hp : PrefixSamePattern P Q i.val) (hc : outgoingCode P i=outgoingCode Q i) :
    OutgoingMark P Q i := by
  intro a ha hv
  cases hcode : outgoingCode P i with
  | none =>
      have heP := (outgoingCode_none_iff P i).mp hcode
      have heQ := (outgoingCode_none_iff Q i).mp (hc.symm.trans hcode)
      have hvQ : incidenceVertex Q a=Q.vertex i.castSucc := by
        rw [incidenceVertex_eq]
        apply (hp.1 (incidenceIndex a) i.castSucc
          (incidenceIndex_le_of_before a ha) (by simp)).mp
        simpa only [incidenceVertex_eq] using hv
      apply iff_of_false
      · intro he
        have hmem := (mem_matchingIncidences P i a).mpr ⟨ha,hv,he⟩
        simp [heP] at hmem
      · intro he
        have hmem := (mem_matchingIncidences Q i a).mpr ⟨ha,hvQ,he⟩
        simp [heQ] at hmem
  | some b =>
      have hbP := (mem_matchingIncidences P i b).mp (outgoingCode_some_mem P i b hcode)
      have hbQ := (mem_matchingIncidences Q i b).mp
        (outgoingCode_some_mem Q i b (hc.symm.trans hcode))
      have he := hp.2 a b ha hbP.1 (hv.trans hbP.2.1.symm)
      simpa only [hbP.2.2,hbQ.2.2] using he

/-- A concrete finite color mark suffices to extend a fresh path prefix. -/
theorem prefixSamePattern_extend_code (P Q : Path V d m) (i : Fin m)
    (hp : PrefixSamePattern P Q i.val) (hP : P.FirstVisit i) (hQ : Q.FirstVisit i)
    (hc : outgoingCode P i=outgoingCode Q i) : PrefixSamePattern P Q (i.val+1) :=
  prefixSamePattern_extend_firstVisit P Q i hp hP hQ (outgoingMark_of_code_eq P Q i hp hc)

end Nonadditivity.HaarPathClasses
