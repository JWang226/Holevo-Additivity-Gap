/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathRefined
import Nonadditivity.HaarPathInternalColors

/-! # Row and column permutations from colored dart matching

A color-preserving dart bijection that fixes the core incidence labels gives
separate permutations of vertex labels for every signed color. The assertion
uses reducedness of the actual paths at their degree-two internal vertices.
Reversal compatibility then supplies the independent row/column permutations
of each Haar matrix family.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathColorRelabel
open HaarPathGraph HaarPathProfiles HaarPathClasses
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
variable {P Q : Path V d m} (h : SamePattern P Q)
variable (F : {q // q∈P.darts} ≃ {q // q∈Q.darts})
variable (hcolor : ∀ q, color (F q).val=color q.val)
variable (hcore : ∀ q, source q.val∈P.coreVertices →
  source (F q).val=h.vertexPerm (source q.val))
variable (hcoreiff : ∀ q, source (F q).val∈Q.coreVertices ↔ source q.val∈P.coreVertices)
include h hcolor hcore hcoreiff

/-- On a single signed-color fibre, the source-label equality pattern is
preserved. This is the precise compatibility needed to extend labels to a
permutation; it does not assume a global vertex bijection on chain interiors. -/
theorem source_kernel_iff_of_color_eq (q r : {q // q∈P.darts})
    (hc : color q.val=color r.val) :
    source q.val=source r.val ↔ source (F q).val=source (F r).val := by
  constructor
  · intro hs
    by_cases hq : source q.val∈P.coreVertices
    · rw [hcore q hq,hcore r (hs ▸ hq),hs]
    · have he : q=r := Subtype.ext
        (P.internal_color_injective q.property r.property hq hs hc)
      exact congrArg (fun a => source (F a).val) he
  · intro hs
    by_cases hq : source (F q).val∈Q.coreVertices
    · have hr : source (F r).val∈Q.coreVertices := hs ▸ hq
      rw [hcore q ((hcoreiff q).mp hq),hcore r ((hcoreiff r).mp hr)] at hs
      exact h.vertexPerm.injective hs
    · have he : F q=F r := Subtype.ext
        (Q.internal_color_injective (F q).property (F r).property hq hs
          ((hcolor q).trans (hc.trans (hcolor r).symm)))
      exact congrArg (fun a => source a.val) (F.injective he)

/-- A genuine permutation of the whole vertex alphabet for each signed color. -/
theorem exists_color_source_perms :
    ∃ κ : Color d → Equiv.Perm V, ∀ q : {q // q∈P.darts},
      κ (color q.val) (source q.val)=source (F q).val := by
  classical
  have hex (c : Color d) : ∃ κ : Equiv.Perm V,
      ∀ q : {q : {q // q∈P.darts} // color q.val=c},
        κ (source q.val.val)=source (F q.val).val := by
    apply exists_perm_of_kernel_eq
    intro q r
    exact source_kernel_iff_of_color_eq h F hcolor hcore hcoreiff q.val r.val
      (q.property.trans r.property.symm)
  choose κ hκ using hex
  exact ⟨κ,fun q => hκ (color q.val) ⟨q,rfl⟩⟩

/-- Positive sources are row labels; sources of reversed positive darts are
column labels. The two permutations are independent for every generator. -/
theorem exists_family_entry_perms
    (hrev : ∀ q : {q // q∈P.darts},
      F ⟨reverse q.val,P.reverse_mem q.property⟩ =
        ⟨reverse (F q).val,Q.reverse_mem (F q).property⟩) :
    ∃ σ τ : Fin d → Equiv.Perm V, ∀ q : {q // q∈P.darts}, ∀ a : Fin d,
      color q.val=(a,true) →
        σ a (source q.val)=source (F q).val ∧
        τ a (source (reverse q.val))=source (reverse (F q).val) := by
  obtain ⟨κ,hκ⟩ := exists_color_source_perms h F hcolor hcore hcoreiff
  refine ⟨fun a => κ (a,true),fun a => κ (a,false),?_⟩
  intro q a hq
  constructor
  · simpa only [hq] using hκ q
  · have hr : color (reverse q.val)=(a,false) := by
      have hqa := congrArg Prod.fst hq
      have hqb := congrArg Prod.snd hq
      simp only [color] at hqa hqb
      simp only [color,reverse,hqa,hqb,Bool.not_true]
    have he := hκ ⟨reverse q.val,P.reverse_mem q.property⟩
    simpa only [hr,hrev] using he

end Nonadditivity.HaarPathColorRelabel
