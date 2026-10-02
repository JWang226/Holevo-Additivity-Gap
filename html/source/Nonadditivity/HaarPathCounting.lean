/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathReconstructionTree

/-! # The corrected explicit count of actual two-generator path classes

This proof reconstructs each normalized incidence pattern from its actual
sparse marks, then counts the fixed code alphabet. Both the final tree-edge
correction and the cost of independent endpoint color labels are retained.
-/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {m : ℕ}
variable {P Q : Path V 2 m}

/-- Equality of the actual event lists reconstructs the entire path class.
The induction advances from each important traversal to the next one. -/
theorem samePattern_of_eventList_eq (hm : 0 < m)
    (hevents : explorationEventList P hm=explorationEventList Q hm) : SamePattern P Q := by
  have htail : ∀ r : ℕ, ∀ i : Fin m, m-i.val=r → i∈P.importantTimes →
      NormalizedPrefixEq P Q hm i.val → NormalizedPrefixEq P Q hm m := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro i hri hi hp
        have hb := P.nextImportant_bounds (i.val+1) (by omega)
        have hblock := normalizedPrefixEq_block hm i hevents hi hp
        by_cases hend : P.nextImportant (i.val+1)=m
        · simpa only [hend] using hblock
        · have hjm : P.nextImportant (i.val+1) < m := by omega
          let j : Fin m := ⟨P.nextImportant (i.val+1),hjm⟩
          exact ih (m-j.val) (by dsimp [j]; omega) j rfl
            (P.nextImportant_is_important (i.val+1) hjm) hblock
  have hinit := normalizedPrefixEq_initial hm hevents
  have hb := P.nextImportant_bounds 0 (by omega)
  apply normalizedPrefixEq_full hm
  by_cases hend : P.nextImportant 0=m
  · simpa only [hend] using hinit
  · have hjm : P.nextImportant 0 < m := by omega
    let j : Fin m := ⟨P.nextImportant 0,hjm⟩
    exact htail (m-j.val) j rfl (P.nextImportant_is_important 0 hjm) hinit

/-- The sparse code is injective on the genuine vertex/local-color quotient,
including loops, parallel edges, and non-cyclically reduced closed paths. -/
theorem classExplorationCode_injective [Fintype V] (hm : 0 < m) (δ : ℕ) :
    Function.Injective (@classExplorationCode V _ m _ δ hm) := by
  intro C D he
  have hl : explorationEventList (classRepresentative hm C) hm =
      explorationEventList (classRepresentative hm D) hm := congrArg Subtype.val he
  have hp := samePattern_of_eventList_eq hm hl
  apply Subtype.ext
  calc
    C.val = Quotient.mk _ (classRepresentative hm C) := (Quotient.out_eq C.val).symm
    _ = Quotient.mk _ (classRepresentative hm D) := Quotient.sound hp
    _ = D.val := Quotient.out_eq D.val

/-- A fully explicit corrected BC5.3 bound for the two-generator problem.
Here δ=2χ is the actual integer defect, and all constants include local
color normalization and the variable number of important events. -/
theorem card_defectClass_le [Fintype V] (hm : 0 < m) (δ : ℕ) :
    Fintype.card (DefectClass V m δ hm) ≤ 128^(δ+2)*m^(3*δ+6) := by
  calc
    _ ≤ Fintype.card (BoundedList (ExplorationEvent m) (δ+2)) :=
      Fintype.card_le_of_injective _ (classExplorationCode_injective hm δ)
    _ ≤ 128^(δ+2)*m^(3*(δ+2)) := card_explorationCodes_le m (δ+2) hm
    _ = _ := by congr 2

end Nonadditivity.HaarPathClasses
