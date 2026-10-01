/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainReverseAddress

/-! # Reversal-coherent coordinates on unoriented core edges -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

abbrev RepresentativePosition := Σ e : P.unorientedChains, Fin (P.representative e).val.length × Bool

def representativePosition (p : P.RepresentativePosition) : P.ChainPosition :=
  if p.2.2 then ⟨P.representative p.1,p.2.1⟩ else
    P.reversePosition ⟨P.representative p.1,p.2.1⟩

lemma chainLabel_representativePosition (p : P.RepresentativePosition) :
    P.chainLabel (P.representativePosition p).1=p.1 := by
  obtain ⟨e,i,b⟩ := p
  cases b <;> simp [representativePosition,reversePosition,P.label_representative]

theorem representativePosition_injective : Function.Injective P.representativePosition := by
  rintro ⟨e,i,b⟩ ⟨e',i',b'⟩ he
  have hee : e=e' := by
    simpa only [P.chainLabel_representativePosition] using congrArg (fun q => P.chainLabel q.1) he
  subst e'
  cases b <;> cases b'
  · have hh := congrArg P.reversePosition he
    simp only [representativePosition,Bool.false_eq_true,ite_false,P.reversePosition_involutive] at hh
    have hi : i=i' := by cases hh; rfl
    subst i'; rfl
  · have hh := congrArg Sigma.fst he
    change P.coreChainReverse (P.representative e)=P.representative e at hh
    exact (P.coreChainReverse_ne_self _ hh).elim
  · have hh := congrArg Sigma.fst he
    change P.representative e=P.coreChainReverse (P.representative e) at hh
    exact (P.coreChainReverse_ne_self _ hh.symm).elim
  · have hi : i=i' := by cases he; rfl
    subst i'; rfl

theorem representativePosition_surjective : Function.Surjective P.representativePosition := by
  rintro ⟨c,i⟩
  have hex : ∃ e : P.unorientedChains,
      c=P.representative e ∨ c=P.coreChainReverse (P.representative e) :=
    ⟨P.chainLabel c,P.eq_representative_or_reverse c⟩
  obtain ⟨e,hc | hc⟩ := hex
  · subst c
    exact ⟨⟨e,i,true⟩,rfl⟩
  · subst c
    let j : Fin (P.representative e).val.length :=
      (Fin.cast (P.coreChainReverse_length (P.representative e)) i).rev
    refine ⟨⟨e,j,false⟩,?_⟩
    change P.reversePosition ⟨P.representative e,j⟩=⟨P.coreChainReverse (P.representative e),i⟩
    have hj : Fin.cast (P.coreChainReverse_length (P.representative e)).symm j.rev=i := by
      apply Fin.ext
      simp only [j,Fin.val_cast,Fin.val_rev]
      have hi : i.val < (P.representative e).val.length :=
        lt_of_lt_of_eq i.isLt (P.coreChainReverse_length _)
      omega
    exact congrArg (fun k => Sigma.mk (P.coreChainReverse (P.representative e)) k) hj

/-- Each graph dart is exactly one representative position and one orientation. -/
def representativePositionEquiv : P.RepresentativePosition ≃ P.darts :=
  (Equiv.ofBijective P.representativePosition
    ⟨P.representativePosition_injective,P.representativePosition_surjective⟩).trans P.positionEquiv

@[simp] theorem representativePositionEquiv_apply (p : P.RepresentativePosition) :
    P.representativePositionEquiv p=P.positionDart (P.representativePosition p) := rfl

/-- Its value formula makes reversal independent of the chain-position index. -/
theorem representativePositionEquiv_val (e : P.unorientedChains)
    (i : Fin (P.representative e).val.length) (b : Bool) :
    (P.representativePositionEquiv ⟨e,i,b⟩).val =
      if b then (P.representative e).val.get i else reverse ((P.representative e).val.get i) := by
  cases b
  · rw [representativePositionEquiv_apply]
    change (P.positionDart (P.reversePosition ⟨P.representative e,i⟩)).val=_
    rw [P.positionDart_reversePosition]
    rfl
  · rfl

theorem representativePositionEquiv_reverse (e : P.unorientedChains)
    (i : Fin (P.representative e).val.length) (b : Bool) :
    P.representativePositionEquiv ⟨e,i,!b⟩=
      ⟨reverse (P.representativePositionEquiv ⟨e,i,b⟩).val,
        P.reverse_mem (P.representativePositionEquiv ⟨e,i,b⟩).property⟩ := by
  apply Subtype.ext
  simp only [P.representativePositionEquiv_val]
  cases b <;> simp

end Nonadditivity.HaarPathGraph.Path
