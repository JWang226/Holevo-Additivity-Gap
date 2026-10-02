/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChainProfiles

/-! # Reversal of actual core-chain profiles

One orientation's profile determines the other, allowing one profile per
unoriented chain in the refined quotient count.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathProfiles
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {d m : ℕ}

theorem coreChainProfile_first (P : Path V d m) (c : P.CoreChain) :
    (P.coreChainProfile c).val.first = color (c.val.head (P.toCore_nonempty c.property.1)) := rfl

theorem coreChainProfile_last (P : Path V d m) (c : P.CoreChain) :
    (P.coreChainProfile c).val.last = color (c.val.getLast (P.toCore_nonempty c.property.1)) := by
  obtain ⟨a,l,he,ha⟩ := c.property.2
  simp [coreChainProfile,he,wordProfile,←List.map_cons,List.getLast_map]

theorem coreChainProfile_count (P : Path V d m) (c : P.CoreChain) (a : Color d) :
    (P.coreChainProfile c).val.count a = (c.val.map color).count a := by
  obtain ⟨b,l,he,hb⟩ := c.property.2
  simp [coreChainProfile,he,wordProfile]
  simp only [List.count_eq_countP,Bool.beq_eq_decide_eq]

theorem flipColor_involutive : Function.Involutive (@flipColor d) := by
  intro c
  simp [flipColor]

theorem coreChainProfile_reverse_first (P : Path V d m) (c : P.CoreChain) :
    (P.coreChainProfile (P.coreChainReverse c)).val.first =
      flipColor (P.coreChainProfile c).val.last := by
  rw [coreChainProfile_first,coreChainProfile_last]
  change color ((c.val.reverse.map reverse).head _) = _
  rw [List.head_map,List.head_reverse]
  rfl

theorem coreChainProfile_reverse_last (P : Path V d m) (c : P.CoreChain) :
    (P.coreChainProfile (P.coreChainReverse c)).val.last =
      flipColor (P.coreChainProfile c).val.first := by
  rw [coreChainProfile_first,coreChainProfile_last]
  change color ((c.val.reverse.map reverse).getLast _) = _
  rw [List.getLast_map,List.getLast_reverse]
  rfl

theorem coreChainProfile_reverse_count (P : Path V d m) (c : P.CoreChain) (a : Color d) :
    (P.coreChainProfile (P.coreChainReverse c)).val.count a =
      (P.coreChainProfile c).val.count (flipColor a) := by
  rw [coreChainProfile_count,coreChainProfile_count]
  have he : (P.coreChainReverse c).val.map color = (c.val.map color).reverse.map flipColor := by
    change (c.val.reverse.map reverse).map color = _
    simp only [List.map_map,List.map_reverse]
    rfl
  rw [he,←flipColor_involutive a]
  rw [List.count_map_of_injective _ flipColor flipColor_involutive.injective]
  rw [List.count_reverse,flipColor_involutive]

/-- Cross-path form used by the actual refined quotient encoding. -/
theorem coreChainProfile_reverse_eq_of_profile_eq
    (P : Path V d m) (Q : Path W d m) (c : P.CoreChain) (e : Q.CoreChain)
    (h : P.coreChainProfile c = Q.coreChainProfile e) :
    P.coreChainProfile (P.coreChainReverse c) = Q.coreChainProfile (Q.coreChainReverse e) := by
  apply Subtype.ext
  apply Profile.ext
  · rw [coreChainProfile_reverse_first,coreChainProfile_reverse_first,h]
  · rw [coreChainProfile_reverse_last,coreChainProfile_reverse_last,h]
  · funext a
    rw [coreChainProfile_reverse_count,coreChainProfile_reverse_count,h]

end Nonadditivity.HaarPathGraph.Path
