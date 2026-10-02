/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClasses

/-! # Fresh exploration runs carry no internal color marks

When a path discovers a fresh vertex, only the outgoing color at the old
vertex needs a mark. At every later step of a consecutive discovery run,
the only previous incidence is the incoming edge; reduction forces the new
outgoing color to be distinct. Thus all subsequent equality patterns are
determined without additional marks.
-/

noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles

variable {V : Type*} [DecidableEq V] {d m : ℕ}

/-- The exact vertex and local-color equality patterns of a path prefix. -/
def PrefixSamePattern (P Q : Path V d m) (k : ℕ) : Prop :=
  (∀ i j : Fin (m+1), i.val ≤ k → j.val ≤ k →
    (P.vertex i=P.vertex j ↔ Q.vertex i=Q.vertex j)) ∧
  ∀ a b : Incidence m, a.1.val < k → b.1.val < k →
    incidenceVertex P a=incidenceVertex P b →
    (incidenceColor P a=incidenceColor P b ↔ incidenceColor Q a=incidenceColor Q b)

omit [DecidableEq V] in
theorem prefixSamePattern_mono {P Q : Path V d m} {j k : ℕ}
    (h : PrefixSamePattern P Q k) (hjk : j ≤ k) : PrefixSamePattern P Q j := by
  exact ⟨fun a b ha hb => h.1 a b (ha.trans hjk) (hb.trans hjk),
    fun a b ha hb => h.2 a b (ha.trans_le hjk) (hb.trans_le hjk)⟩

omit [DecidableEq V] in
theorem prefixSamePattern_full {P Q : Path V d m}
    (h : PrefixSamePattern P Q m) : SamePattern P Q := by
  exact ⟨fun i j => h.1 i j (by omega) (by omega),
    fun a b => h.2 a b a.1.isLt b.1.isLt⟩

theorem incidenceIndex_le_of_before (a : Incidence m) {k : ℕ}
    (ha : a.1.val < k) : (incidenceIndex a).val ≤ k := by
  obtain ⟨a,b⟩ := a
  change a.val < k at ha
  cases b <;> simp only [incidenceIndex, Bool.false_eq_true, if_false, if_true,
    Fin.val_succ, Fin.val_castSucc] <;> omega

/-- The sole new color information at a first visit is its outgoing color's
equality pattern with old incidences at the starting vertex. -/
def OutgoingMark (P Q : Path V d m) (i : Fin m) : Prop :=
  ∀ a : Incidence m, a.1.val < i.val →
    incidenceVertex P a=P.vertex i.castSucc →
    (incidenceColor P a=P.colors i ↔ incidenceColor Q a=Q.colors i)

/-- Extend the full observable pattern by one fresh-vertex step. The proof
uses the literal two incidences of the new edge. -/
theorem prefixSamePattern_extend_firstVisit (P Q : Path V d m) (i : Fin m)
    (hp : PrefixSamePattern P Q i.val) (hP : P.FirstVisit i) (hQ : Q.FirstVisit i)
    (hmark : OutgoingMark P Q i) : PrefixSamePattern P Q (i.val+1) := by
  constructor
  · intro a b ha hb
    by_cases hai : a.val ≤ i.val
    · by_cases hbi : b.val ≤ i.val
      · exact hp.1 a b hai hbi
      · have he : b=i.succ := Fin.ext (by simp; omega)
        subst b
        exact iff_of_false (hP a hai) (hQ a hai)
    · have he : a=i.succ := Fin.ext (by simp; omega)
      subst a
      by_cases hbi : b.val ≤ i.val
      · exact iff_of_false (Ne.symm (hP b hbi)) (Ne.symm (hQ b hbi))
      · have he : b=i.succ := Fin.ext (by simp; omega)
        subst b
        simp
  · have holdnew (a : Incidence m) (ha : a.1.val < i.val) (b : Bool)
        (hab : incidenceVertex P a=incidenceVertex P (i,b)) :
        (incidenceColor P a=incidenceColor P (i,b) ↔
          incidenceColor Q a=incidenceColor Q (i,b)) := by
      cases b with
      | false =>
          exact (hP (incidenceIndex a) (incidenceIndex_le_of_before a ha)
            (by simpa only [incidenceVertex_eq, incidenceIndex, if_false] using hab)).elim
      | true => exact hmark a ha hab
    have hnewnew (a b : Bool)
        (hab : incidenceVertex P (i,a)=incidenceVertex P (i,b)) :
        (incidenceColor P (i,a)=incidenceColor P (i,b) ↔
          incidenceColor Q (i,a)=incidenceColor Q (i,b)) := by
      have hn := hP i.castSucc (show i.castSucc.val ≤ i.val from le_rfl)
      cases a <;> cases b
      · simp
      · exact (hn hab.symm).elim
      · exact (hn hab).elim
      · simp
    rintro ⟨a,ab⟩ ⟨b,bb⟩ ha hb hab
    by_cases hai : a.val < i.val
    · by_cases hbi : b.val < i.val
      · exact hp.2 (a,ab) (b,bb) hai hbi hab
      · have he : b=i := Fin.ext (by change b.val < i.val+1 at hb; omega)
        subst b
        exact holdnew (a,ab) hai bb hab
    · have he : a=i := Fin.ext (by change a.val < i.val+1 at ha; omega)
      subst a
      by_cases hbi : b.val < i.val
      · simpa only [eq_comm] using holdnew (b,bb) hbi ab hab.symm
      · have he : b=i := Fin.ext (by change b.val < i.val+1 at hb; omega)
        subst b
        exact hnewnew ab bb hab

/-- Immediately after a first visit, the previous incoming incidence is the
only old incidence at the current vertex. -/
theorem incidence_at_fresh_vertex_unique (P : Path V d m) (i j : Fin m)
    (hij : i.val+1=j.val) (hi : P.FirstVisit i)
    (a : Incidence m) (ha : a.1.val < j.val)
    (hv : incidenceVertex P a=P.vertex j.castSucc) : a=(i,false) := by
  have hji : j.castSucc=i.succ := Fin.ext (by simp; omega)
  rw [hji] at hv
  obtain ⟨a,b⟩ := a
  change a.val < j.val at ha
  cases b with
  | true =>
      exact (hi a.castSucc (by change a.val ≤ i.val; omega) hv).elim
  | false =>
      have hai : a.val=i.val := by
        by_contra hn
        have hlt : a.val < i.val := by omega
        exact hi a.succ (by simp; omega) hv
      exact congrArg (fun k : Fin m => (k,false)) (Fin.ext hai)

/-- No color mark is needed after a fresh visit: reducedness fixes the only
possible comparison with the previous incoming incidence. -/
theorem outgoingMark_after_firstVisit (P Q : Path V d m) (i j : Fin m)
    (hij : i.val+1=j.val) (hi : P.FirstVisit i) : OutgoingMark P Q j := by
  intro a ha hv
  have he := incidence_at_fresh_vertex_unique P i j hij hi a ha hv
  subst a
  exact iff_of_false (Ne.symm (P.reduced i j hij)) (Ne.symm (Q.reduced i j hij))

theorem prefixSamePattern_extend_after_firstVisit (P Q : Path V d m) (i j : Fin m)
    (hij : i.val+1=j.val) (hp : PrefixSamePattern P Q j.val)
    (hi : P.FirstVisit i) (hP : P.FirstVisit j) (hQ : Q.FirstVisit j) :
    PrefixSamePattern P Q (j.val+1) :=
  prefixSamePattern_extend_firstVisit P Q j hp hP hQ
    (outgoingMark_after_firstVisit P Q i j hij hi)

/-- An entire consecutive fresh run is determined by its first-step pattern.
The induction adds no further outgoing-color marks. -/
theorem prefixSamePattern_fresh_run (P Q : Path V d m) (s t : ℕ)
    (hst : s < t) (htm : t ≤ m) (hp : PrefixSamePattern P Q (s+1))
    (hfresh : ∀ i : Fin m, s ≤ i.val → i.val < t → P.FirstVisit i ∧ Q.FirstVisit i) :
    PrefixSamePattern P Q t := by
  have hmain : ∀ k, s+1 ≤ k → k ≤ t → PrefixSamePattern P Q k := by
    intro k hsk
    induction k, hsk using Nat.le_induction with
    | base => exact fun _ => hp
    | succ k hsk ih =>
        intro hkt
        let i : Fin m := ⟨k-1,by omega⟩
        let j : Fin m := ⟨k,by omega⟩
        have hij : i.val+1=j.val := by dsimp [i,j]; omega
        have hi := (hfresh i (by dsimp [i]; omega) (by dsimp [i]; omega)).1
        have hj := hfresh j (by dsimp [j]; omega) (by dsimp [j]; omega)
        exact prefixSamePattern_extend_after_firstVisit P Q i j hij
          (ih (by omega)) hi hj.1 hj.2
  exact hmain t (by omega) le_rfl

end Nonadditivity.HaarPathClasses
