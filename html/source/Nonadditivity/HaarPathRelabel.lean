/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathWeights

/-! # Invariance of Haar path weights under row and column relabeling

Independent permutations of rows and columns preserve each Haar law. This
is the analytic invariance needed when matching the internal vertices of
chains with the same signed-color profile.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathWeights
open MeasureTheory HaarModel HaarMoments HaarFourthMoments
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {N : ℕ}

@[simp] theorem mul_rowPermutation_entry (e : Equiv.Perm (Fin (N+1)))
    (i j : Fin (N+1)) (U : LocalUnitary N) :
    ((U * rowPermutation e.symm : LocalUnitary N) : Mat N) i j = (U : Mat N) i (e j) := by
  change ((U : Mat N) * (e⁻¹).permMatrix ℂ) i j = _
  simp only [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

def relabelEntries (σ τ : Equiv.Perm (Fin (N+1))) (L : List (Entry N)) : List (Entry N) :=
  L.map (fun e => (σ e.1,τ e.2))

lemma listMonomial_relabel (σ τ : Equiv.Perm (Fin (N+1))) (L R : List (Entry N))
    (U : LocalUnitary N) :
    listMonomial (relabelEntries σ τ L) (relabelEntries σ τ R) U =
      listMonomial L R (rowPermutation σ * U * rowPermutation τ.symm) := by
  simp only [listMonomial,entryProduct,relabelEntries,List.map_map,
    mul_rowPermutation_entry,rowPermutation_mul_entry]
  rfl

/-- No degree or dimension restriction is needed for row/column invariance. -/
theorem integral_listMonomial_relabel (σ τ : Equiv.Perm (Fin (N+1))) (L R : List (Entry N)) :
    (∫ U : LocalUnitary N, listMonomial (relabelEntries σ τ L) (relabelEntries σ τ R) U ∂haar N) =
      ∫ U : LocalUnitary N, listMonomial L R U ∂haar N := by
  simp_rw [listMonomial_relabel]
  rw [integral_mul_left_eq_self (μ := haar N)
    (fun U => listMonomial L R (U * rowPermutation τ.symm)) (rowPermutation σ)]
  exact integral_mul_right_eq_self (μ := haar N) (listMonomial L R) (rowPermutation τ.symm)

lemma listMonomial_eq_of_perm {L L' R R' : List (Entry N)} (hL : L.Perm L') (hR : R.Perm R')
    (U : LocalUnitary N) : listMonomial L R U=listMonomial L' R' U := by
  unfold listMonomial entryProduct
  rw [(hL.map _).prod_eq, (hR.map _).prod_eq]

/-- Actual Haar path expectations depend only on the two signed entry
multisets, up to an independent row and column permutation in each family. -/
theorem integral_signedProduct_eq_of_family_relabel (L R : List (SignedEntry N))
    (σ τ : Fin 2 → Equiv.Perm (Fin (N+1)))
    (h : ∀ a : Fin 2, ∀ b : Bool,
      (selected (a,b) R).Perm (relabelEntries (σ a) (τ a) (selected (a,b) L))) :
    (∫ U : LocalUnitary N × LocalUnitary N, signedProduct R U ∂(haar N).prod (haar N)) =
      ∫ U : LocalUnitary N × LocalUnitary N, signedProduct L U ∂(haar N).prod (haar N) := by
  simp_rw [signedProduct_eq]
  rw [integral_prod_mul,integral_prod_mul]
  congr 1
  · simp_rw [listMonomial_eq_of_perm (h 0 true) (h 0 false)]
    exact integral_listMonomial_relabel _ _ _ _
  · simp_rw [listMonomial_eq_of_perm (h 1 true) (h 1 false)]
    exact integral_listMonomial_relabel _ _ _ _

end Nonadditivity.HaarPathWeights
