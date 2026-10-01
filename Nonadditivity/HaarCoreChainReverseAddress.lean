/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainAddress

/-! # Reversal in literal core-chain position coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

@[simp] theorem coreChainReverse_length (c : P.CoreChain) :
    (P.coreChainReverse c).val.length=c.val.length := by
  change (c.val.reverse.map reverse).length=c.val.length
  simp

def reversePosition (p : P.ChainPosition) : P.ChainPosition :=
  ⟨P.coreChainReverse p.1, Fin.cast (P.coreChainReverse_length p.1).symm p.2.rev⟩

/-- The precise reversed address is the reversed chain and the reversed
finite index. This includes one-edge chains and colored loops. -/
theorem positionDart_reversePosition (p : P.ChainPosition) :
    P.positionDart (P.reversePosition p) =
      ⟨reverse (P.positionDart p).val,P.reverse_mem (P.positionDart p).property⟩ := by
  obtain ⟨c,i⟩ := p
  apply Subtype.ext
  change (c.val.reverse.map reverse).get _ = reverse (c.val.get i)
  simp only [reversePosition,List.get_eq_getElem,List.getElem_map,List.getElem_reverse,Fin.val_cast,Fin.val_rev]
  congr 2
  have hi := i.isLt
  omega

@[simp] theorem reversePosition_involutive (p : P.ChainPosition) :
    P.reversePosition (P.reversePosition p)=p := by
  apply P.positionDart_injective
  rw [P.positionDart_reversePosition]
  apply Subtype.ext
  simp only [P.positionDart_reversePosition,reverse_reverse]

/-- Reversal of an actual dart reverses its unique complete-chain address. -/
theorem positionEquiv_symm_reverse (q : P.darts) :
    P.positionEquiv.symm ⟨reverse q.val,P.reverse_mem q.property⟩ =
      P.reversePosition (P.positionEquiv.symm q) := by
  apply P.positionEquiv.injective
  rw [Equiv.apply_symm_apply,P.positionEquiv_apply,P.positionDart_reversePosition]
  congr 1
  exact congrArg (fun z : P.darts => reverse z.val) (P.positionEquiv.apply_symm_apply q).symm

end Nonadditivity.HaarPathGraph.Path
