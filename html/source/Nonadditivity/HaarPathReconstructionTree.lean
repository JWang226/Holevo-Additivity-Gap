/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathReconstructionFresh
import Nonadditivity.HaarPathNormalizedTreeColors

/-! # Reconstructing each complete block of sparse exploration data -/
noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
variable {V : Type*} [DecidableEq V] {m : ℕ} {P Q : Path V 2 m}

/-- The marked endpoint determines the old-tree run, its length, and both
local labels of every step. Only the already decoded prefix is used. -/
theorem normalizedPrefixEq_to_treeStop (hm : 0 < m) (i : Fin m)
    (hmark : explorationMark P hm i=explorationMark Q hm i)
    (hp : NormalizedPrefixEq P Q hm (i.val+1)) :
    treeStop P i=treeStop Q i ∧ NormalizedPrefixEq P Q hm (treeStop P i) := by
  have hP := P.exploration_block_split (i.val+1) (by omega)
  have hQ := Q.exploration_block_split (i.val+1) (by omega)
  have hbP := treeStop_bounds P i
  have hbQ := treeStop_bounds Q i
  have hend : P.vertexName hm ⟨treeStop P i,by omega⟩ =
      Q.vertexName hm ⟨treeStop Q i,by omega⟩ :=
    congrArg (fun x : ExplorationMark m => x.2.1) hmark
  obtain ⟨hs,hv,hc⟩ := normalized_old_tree_reconstruction P Q hm
    (colorNormalizer P hm) (colorNormalizer Q hm)
    (i.val+1) (treeStop P i) (treeStop Q i)
    hbP.1 hbQ.1 hbP.2 hbQ.2
    (fun j haj hjs => (hP.2.1 j haj hjs).2)
    (fun j haj hjs => (hP.2.1 j haj hjs).1)
    (fun j haj hjs => (hQ.2.1 j haj hjs).2)
    (fun j haj hjs => (hQ.2.1 j haj hjs).1)
    hp.1 hp.2 hend
  refine ⟨hs,?_,?_⟩
  · intro j hj
    by_cases hja : j.val ≤ i.val+1
    · exact hp.1 j hja
    · exact hv j (by omega) hj
  · rintro ⟨j,b⟩ hj
    by_cases hja : j.val < i.val+1
    · exact hp.2 (j,b) hja
    · exact hc j (by omega) hj b

/-- One full important-edge / old-tree / fresh-run block is reconstructed
from its literal sparse mark and previously known data. -/
theorem normalizedPrefixEq_block (hm : 0 < m) (i : Fin m)
    (hevents : explorationEventList P hm=explorationEventList Q hm)
    (hi : i∈P.importantTimes) (hp : NormalizedPrefixEq P Q hm i.val) :
    NormalizedPrefixEq P Q hm (P.nextImportant (i.val+1)) := by
  have hmark := explorationMark_eq_of_eventList_eq hm hevents i hi
  have hp' := normalizedPrefixEq_extend_mark hm i hp hmark
  obtain ⟨hstop,hpstop⟩ := normalizedPrefixEq_to_treeStop hm i hmark hp'
  exact normalizedPrefixEq_after_treeStop hm i hevents hmark hstop hpstop

end Nonadditivity.HaarPathClasses
