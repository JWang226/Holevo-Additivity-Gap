/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChainPartition

/-! # Internal vertices have unique outgoing signed colors

The degree-two hypothesis alone would not separate colors. Reducedness of the
original path supplies two distinct signed colors, exhausting its two darts.
Core-chain internal vertices also occur only once, by deterministic continuation
and the prohibition against traversing both orientations of one edge.
-/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

theorem internal_darts_color_separated {v : V} (hv : v∈P.vertices)
    (hcore : v∉P.coreVertices) :
    ∃ a b : Dart V d, a∈P.darts ∧ b∈P.darts ∧ source a=v ∧ source b=v ∧
      color a≠color b ∧ ∀ q∈P.darts, source q=v → q=a ∨ q=b := by
  have hroot : v≠P.vertex 0 := by
    intro he
    exact hcore (Finset.mem_filter.mpr ⟨hv,Or.inl he⟩)
  obtain ⟨i,hi,hiv⟩ := Finset.mem_image.mp hv
  have hi0 : 0 < (i : Fin m).val := by
    by_contra h
    have he : i.castSucc=0 := Fin.ext (by simp; omega)
    exact hroot (by rw [←hiv,he])
  let j : Fin m := ⟨i.val-1,by omega⟩
  have hji : j.val+1=i.val := by dsimp [j]; omega
  have hjs : j.succ=i.castSucc := Fin.ext hji
  let a := P.traversal i
  let b := reverse (P.traversal j)
  have ha : a∈P.darts := P.traversal_mem i
  have hb : b∈P.darts := P.reverse_traversal_mem j
  have hav : source a=v := by simpa only [a,traversal,source_dart] using hiv
  have hbv : source b=v := by simp only [b,traversal,source_reverse_dart,hjs,hiv]
  have hc : color a≠color b := by
    simpa only [a,b,traversal,color_dart,color_reverse_dart] using P.reduced j i hji
  refine ⟨a,b,ha,hb,hav,hbv,hc,?_⟩
  intro q hq hqv
  by_cases hqa : q=a
  · exact Or.inl hqa
  · right
    have hba : b≠a := fun he => hc (congrArg color he.symm)
    exact (P.next_dart_unique ha hb hq (hav ▸ hcore)
      (hav.trans hbv.symm) (hav.trans hqv.symm) hba hqa).symm

/-- At a non-core vertex, its signed color determines its outgoing dart. -/
theorem internal_color_injective {q r : Dart V d} (hq : q∈P.darts) (hr : r∈P.darts)
    (hcore : source q∉P.coreVertices) (hs : source q=source r) (hc : color q=color r) : q=r := by
  obtain ⟨a,b,ha,hb,hav,hbv,hab,hex⟩ := P.internal_darts_color_separated (P.source_mem hq) hcore
  rcases hex q hq rfl with hqa | hqb <;> rcases hex r hr hs.symm with hra | hrb
  · exact hqa.trans hra.symm
  · exact (hab (by simpa only [hqa,hrb] using hc)).elim
  · exact (hab (by simpa only [hqb,hra] using hc.symm)).elim
  · exact hqb.trans hrb.symm

theorem toCore_predecessor_or_first {l : List (Dart V d)} (h : P.ToCore l)
    {q : Dart V d} (hq : q∈l) :
    l.head?=some q ∨ ∃ p∈l, source (reverse p)=source q ∧ q≠reverse p := by
  induction h with
  | last a ha hc => left; simpa using (List.mem_singleton.mp hq).symm
  | cons a b l ha hc hj hr ht ih =>
    rcases List.mem_cons.mp hq with hqa | hq
    · left; simp [hqa]
    · rcases ih hq with hhead | ⟨p,hp,hpq,hred⟩
      · have he : b=q := by simpa using hhead
        subst q
        exact Or.inr ⟨a,by simp,hj,hr⟩
      · exact Or.inr ⟨p,List.mem_cons_of_mem _ hp,hpq,hred⟩

theorem coreChain_predecessor (c : P.CoreChain) {q : Dart V d}
    (hq : q∈c.val) (hcore : source q∉P.coreVertices) :
    ∃ p∈c.val, source (reverse p)=source q ∧ q≠reverse p := by
  rcases P.toCore_predecessor_or_first c.property.1 hq with hh | h
  · obtain ⟨a,t,he,hac⟩ := c.property.2
    have haq : a=q := by simpa only [he,List.head?_cons,Option.some.injEq] using hh
    exact (hcore (haq ▸ hac)).elim
  · exact h

/-- An internal vertex appears at most once in a maximal core chain. -/
theorem coreChain_source_injective (c : P.CoreChain) {q r : Dart V d}
    (hq : q∈c.val) (hr : r∈c.val) (hcore : source q∉P.coreVertices)
    (hs : source q=source r) : q=r := by
  by_contra hne
  obtain ⟨p,hp,hpq,hred⟩ := P.coreChain_predecessor c hq hcore
  have he : reverse p=r := P.next_dart_unique (P.toCore_mem c.property.1 hq)
    (P.reverse_mem (P.toCore_mem c.property.1 hp)) (P.toCore_mem c.property.1 hr)
    hcore hpq.symm hs (Ne.symm hred) (Ne.symm hne)
  exact P.coreChain_not_both_orientations c hp (he ▸ hr)

theorem toCore_tail_source_not_core {l : List (Dart V d)} (h : P.ToCore l)
    {q : Dart V d} (hq : q∈l.tail) : source q∉P.coreVertices := by
  induction h with
  | last a ha hc => simp at hq
  | cons a b l ha hc hj hr ht ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · simpa only [hj] using hc
    · exact ih hq

theorem toCore_step {l : List (Dart V d)} (h : P.ToCore l)
    (i : ℕ) (hi : i+1<l.length) :
    source (reverse l[i])=source l[i+1] ∧ l[i+1]≠reverse l[i] := by
  induction h generalizing i with
  | last a ha hc => simp at hi
  | cons a b l ha hc hj hr ht ih =>
    cases i with
    | zero => exact ⟨hj,hr⟩
    | succ i => exact ih i (by simpa using hi)

theorem coreChain_internal_sources_nodup (c : P.CoreChain) :
    (c.val.tail.map source).Nodup := by
  apply List.Nodup.map_on _ (P.toCore_nodup c.property.1).tail
  intro q hq r hr hs
  exact P.coreChain_source_injective c (List.mem_of_mem_tail hq) (List.mem_of_mem_tail hr)
    (P.toCore_tail_source_not_core c.property.1 hq) hs

end Nonadditivity.HaarPathGraph.Path
