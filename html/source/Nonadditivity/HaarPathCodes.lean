/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClassData
import Mathlib.Data.List.GetD

/-! # Finite sparse codes with literal position and local-color marks

An event records its time, its target vertex, the endpoint of the following
old-tree run, and three independent local color labels. For two generators
this is exactly 64*m^3 possibilities. Padding by `none` handles the variable
number of events without an additional polynomial factor.
-/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathProfiles
variable {A : Type*}

abbrev BoundedList (A : Type*) (q : ℕ) := {l : List A // l.length ≤ q}

/-- A literal bounded list, padded with `none` to its length budget. -/
def paddedListCode (q : ℕ) (l : BoundedList A q) : Fin q → Option A :=
  fun i => l.val[i.val]?

theorem paddedListCode_injective (q : ℕ) :
    Function.Injective (@paddedListCode A q) := by
  intro l s h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < q
  · exact congrFun h ⟨i,hi⟩
  · rw [List.getElem?_eq_none (by have := l.property; omega),
      List.getElem?_eq_none (by have := s.property; omega)]

instance [Fintype A] (q : ℕ) : Fintype (BoundedList A q) :=
  Fintype.ofInjective (paddedListCode q) (paddedListCode_injective q)

theorem card_boundedList_le [Fintype A] (q : ℕ) :
    Fintype.card (BoundedList A q) ≤ (Fintype.card A+1)^q := by
  calc
    _ ≤ Fintype.card (Fin q → Option A) :=
      Fintype.card_le_of_injective _ (paddedListCode_injective q)
    _ = _ := by simp

/-- The three local colors are independent endpoint labels. This avoids
assuming that local normalization produces a globally colored path. -/
abbrev ExplorationMark (m : ℕ) :=
  Fin m × Fin m × Color 2 × Color 2 × Color 2

/-- Time, target vertex, end of old-tree run, and three local colors. -/
abbrev ExplorationEvent (m : ℕ) := Fin m × ExplorationMark m

@[simp] theorem card_explorationEvent (m : ℕ) :
    Fintype.card (ExplorationEvent m)=64*m^3 := by
  simp only [ExplorationEvent,ExplorationMark,Color,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool]
  ring

/-- The fully explicit code-space bound, including padding and variable
length. It does not refer to the unknown final path graph. -/
theorem card_explorationCodes_le (m q : ℕ) (hm : 0 < m) :
    Fintype.card (BoundedList (ExplorationEvent m) q) ≤
      128^q*m^(3*q) := by
  have hc : 64*m^3+1 ≤ 128*m^3 := by
    have hp : 0 < m^3 := pow_pos hm _
    omega
  calc
    _ ≤ (Fintype.card (ExplorationEvent m)+1)^q := card_boundedList_le q
    _ = (64*m^3+1)^q := by rw [card_explorationEvent]
    _ ≤ (128*m^3)^q := Nat.pow_le_pow_left hc _
    _ = _ := by rw [mul_pow,←pow_mul]

end Nonadditivity.HaarPathClasses
