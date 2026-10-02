/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathReconstruction

/-! # The fresh-run steps in sparse normalized path reconstruction -/

noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles

variable {V : Type*} [DecidableEq V] {m : ℕ} {P Q : Path V 2 m}

/-- Equal event lists determine the entire unmarked initial prefix. -/
theorem normalizedPrefixEq_initial (hm : 0<m)
    (hevents : explorationEventList P hm=explorationEventList Q hm) :
    NormalizedPrefixEq P Q hm (P.nextImportant 0) := by
  have h := normalized_before_first_important P Q hm
    (colorNormalizer P hm) (colorNormalizer Q hm) initialColor nextColor
    (normalizer_freshNormalization P hm) (normalizer_freshNormalization Q hm)
    (normalColor_root P hm) (normalColor_root Q hm)
    (nextImportant_eq_of_eventList_eq hm hevents 0)
  refine ⟨h.1,?_⟩
  rintro ⟨i,b⟩ hi
  cases b with
  | false => exact (h.2 i hi).2
  | true => exact (h.2 i hi).1

/-- Join an already reconstructed prefix to a fresh interval. Only the
first outgoing label is read from the sparse mark. -/
theorem normalizedPrefixEq_fresh_interval (hm : 0<m) (a b : ℕ)
    (hab : a ≤ b) (hbm : b ≤ m) (hp : NormalizedPrefixEq P Q hm a)
    (hfresh : ∀ i : Fin m, a ≤ i.val → i.val<b → P.FirstVisit i ∧ Q.FirstVisit i)
    (hfirst : ∀ i : Fin m, i.val=a → normalColor P hm (i,true)=normalColor Q hm (i,true)) :
    NormalizedPrefixEq P Q hm b := by
  have hstart : P.vertexName hm ⟨a,by omega⟩=Q.vertexName hm ⟨a,by omega⟩ :=
    hp.1 _ le_rfl
  have h := normalized_fresh_run P Q hm
    (colorNormalizer P hm) (colorNormalizer Q hm) initialColor nextColor
    (normalizer_freshNormalization P hm) (normalizer_freshNormalization Q hm)
    a b hab hbm hfresh hstart hfirst
  constructor
  · intro j hj
    by_cases hja : j.val ≤ a
    · exact hp.1 j hja
    · exact h.1 j (by omega) hj
  · rintro ⟨i,c⟩ hi
    by_cases hia : i.val<a
    · exact hp.2 (i,c) hia
    · have hc := h.2 i (by omega) hi
      cases c with
      | false => exact hc.2
      | true => exact hc.1

/-- After the reconstructed old-tree run, the actual exploration split and
the mark's final color determine the whole remaining fresh run. -/
theorem normalizedPrefixEq_after_treeStop (hm : 0<m) (i : Fin m)
    (hevents : explorationEventList P hm=explorationEventList Q hm)
    (hmark : explorationMark P hm i=explorationMark Q hm i)
    (hstop : treeStop P i=treeStop Q i)
    (hp : NormalizedPrefixEq P Q hm (treeStop P i)) :
    NormalizedPrefixEq P Q hm (P.nextImportant (i.val+1)) := by
  have hnext := nextImportant_eq_of_eventList_eq hm hevents (i.val+1)
  have hbounds := P.nextImportant_bounds (i.val+1) (by omega)
  have hswitch := P.firstFresh_bounds (i.val+1) (P.nextImportant (i.val+1)) hbounds.1
  apply normalizedPrefixEq_fresh_interval hm (treeStop P i)
    (P.nextImportant (i.val+1)) hswitch.2 hbounds.2 hp
  · intro j hsj hjb
    have hP := (P.exploration_block_split (i.val+1) (by omega)).2.2 j hsj hjb
    have hsjQ : treeStop Q i ≤ j.val := by rw [←hstop]; exact hsj
    have hQ := (Q.exploration_block_split (i.val+1) (by omega)).2.2 j
      hsjQ (by simpa only [←hnext] using hjb)
    exact ⟨hP,hQ⟩
  · intro j hjs
    have hsP : treeStop P i<m := by rw [←hjs]; exact j.isLt
    have hsQ : treeStop Q i<m := by simpa only [←hstop] using hsP
    have hc := congrArg (fun x : ExplorationMark m => x.2.2.2.2) hmark
    simp only [explorationMark,dif_pos hsP,dif_pos hsQ] at hc
    have hjP : (⟨treeStop P i,hsP⟩ : Fin m)=j := Fin.ext hjs.symm
    have hjQ : (⟨treeStop Q i,hsQ⟩ : Fin m)=j := Fin.ext (hstop.symm.trans hjs.symm)
    simpa only [hjP,hjQ] using hc

end Nonadditivity.HaarPathClasses
