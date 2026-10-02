/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCoreChainWords
import Nonadditivity.HaarCoreChainReverseAddress
import Nonadditivity.HaarPathProfileReverse

/-! # Reversing an arbitrary word in an actual core-chain profile

The chosen reduced word on one orientation determines a word in the actual
opposite profile. This is a map of literal finite profile families, with the
precise reversed index formula and inverse free-group evaluation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathProfiles HaarProfileCoefficient

theorem ofFn_flip_rev {d j k : ℕ} (hj : j=k) (w : Fin k → Color d) :
    List.ofFn (fun i : Fin j => flipColor (w (Fin.cast hj i.rev))) =
      FreeGroup.invRev (List.ofFn w) := by
  subst j
  apply List.ext_getElem
  · simp [FreeGroup.invRev]
  · intro i hi hj
    simp only [List.getElem_ofFn,FreeGroup.invRev,List.getElem_map,
      List.getElem_reverse,List.length_map,List.length_ofFn,Fin.cast_refl]
    apply congrArg flipColor
    apply congrArg w
    apply Fin.ext
    simp only [id_eq,Fin.val_rev]
    omega

variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

def reverseProfileWord (c : P.CoreChain)
    (w : Words d c.val.length (P.coreChainProfile c).val) :
    Words d (P.coreChainReverse c).val.length
      (P.coreChainProfile (P.coreChainReverse c)).val := by
  refine ⟨fun i => flipColor (w.val (Fin.cast (P.coreChainReverse_length c) i.rev)),?_⟩
  rw [ofFn_flip_rev]
  refine ⟨reduced_invRev w.property.1,?_,?_,?_⟩
  · rw [P.coreChainProfile_reverse_first]
    simp only [FreeGroup.invRev,List.head?_reverse,List.getLast?_map,
      w.property.2.2.1,Option.map_some]
    rfl
  · rw [P.coreChainProfile_reverse_last]
    simp only [FreeGroup.invRev,List.getLast?_reverse,List.head?_map,
      w.property.2.1,Option.map_some]
    rfl
  · intro a
    rw [P.coreChainProfile_reverse_count]
    change ((List.ofFn w.val).map flipColor).reverse.count a = _
    rw [List.count_reverse]
    rw [←flipColor_involutive a,
      List.count_map_of_injective _ flipColor flipColor_involutive.injective,
      flipColor_involutive]
    exact w.property.2.2.2 _

@[simp] theorem reverseProfileWord_val (c : P.CoreChain)
    (w : Words d c.val.length (P.coreChainProfile c).val)
    (i : Fin (P.coreChainReverse c).val.length) :
    (P.reverseProfileWord c w).val i =
      flipColor (w.val (Fin.cast (P.coreChainReverse_length c) i.rev)) := rfl

theorem reverseProfileWord_ofFn (c : P.CoreChain)
    (w : Words d c.val.length (P.coreChainProfile c).val) :
    List.ofFn (P.reverseProfileWord c w).val = FreeGroup.invRev (List.ofFn w.val) :=
  ofFn_flip_rev _ _

@[simp] theorem reverseProfileWord_word (c : P.CoreChain)
    (w : Words d c.val.length (P.coreChainProfile c).val) :
    word (P.reverseProfileWord c w)=(word w)⁻¹ := by
  unfold word
  rw [P.reverseProfileWord_ofFn,FreeGroup.inv_mk]

/-- Reversing the chosen signed word twice restores its literal letter list. -/
theorem reverseProfileWord_twice_ofFn (c : P.CoreChain)
    (w : Words d c.val.length (P.coreChainProfile c).val) :
    List.ofFn (P.reverseProfileWord (P.coreChainReverse c) (P.reverseProfileWord c w)).val =
      List.ofFn w.val := by
  rw [P.reverseProfileWord_ofFn,P.reverseProfileWord_ofFn,FreeGroup.invRev_invRev]

/-- The actual profile-family elements are involutive, allowing for the
dependent equality between the twice-reversed chain and the original chain. -/
theorem reverseProfileWord_involutive (c : P.CoreChain)
    (w : Words d c.val.length (P.coreChainProfile c).val) :
    HEq (P.reverseProfileWord (P.coreChainReverse c) (P.reverseProfileWord c w)) w := by
  have hh (c' : P.CoreChain) (he : c'=c)
      (w' : Words d c'.val.length (P.coreChainProfile c').val)
      (hw : List.ofFn w'.val=List.ofFn w.val) : HEq w' w := by
    subst c'
    exact heq_of_eq (Subtype.ext (List.ofFn_injective hw))
  exact hh _ (P.coreChainReverse_involutive c) _ (P.reverseProfileWord_twice_ofFn c w)

end Nonadditivity.HaarPathGraph.Path
