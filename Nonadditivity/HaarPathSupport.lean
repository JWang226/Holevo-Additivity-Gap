/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathBalance
import Nonadditivity.HaarPathLocalPhase

/-! # Vanishing of Haar path weights with too many vertices -/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathWeights
open MeasureTheory HaarModel HaarFourthMoments HaarPathLocalPhase
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {N m : ℕ} (P : HaarPathGraph.Path (Fin (N+1)) 2 m)

lemma rowCount_positive_pathEntries (a : Fin 2) (v : Fin (N+1)) :
    rowCount (selected (a,true) (pathEntries P)) v=P.outgoingCount (a,true) v := by
  rw [pathEntries, selected_rowCount_ofFn, HaarPathGraph.Path.outgoingCount]
  congr 1
  ext i
  cases hb : (P.colors i).2 <;> simp [hb,and_comm] <;>
    intro hc <;> have he := congrArg Prod.snd hc <;> simp [hb] at he

lemma rowCount_negative_pathEntries (a : Fin 2) (v : Fin (N+1)) :
    rowCount (selected (a,false) (pathEntries P)) v=P.incomingCount (a,false) v := by
  rw [pathEntries, selected_rowCount_ofFn, HaarPathGraph.Path.incomingCount]
  congr 1
  ext i
  cases hb : (P.colors i).2 <;> simp [hb,and_comm] <;>
    intro hc <;> have he := congrArg Prod.snd hc <;> simp [hb] at he

lemma columnCount_positive_pathEntries (a : Fin 2) (v : Fin (N+1)) :
    columnCount (selected (a,true) (pathEntries P)) v=P.incomingCount (a,true) v := by
  rw [pathEntries, selected_columnCount_ofFn, HaarPathGraph.Path.incomingCount]
  congr 1
  ext i
  cases hb : (P.colors i).2 <;> simp [hb,and_comm] <;>
    intro hc <;> have he := congrArg Prod.snd hc <;> simp [hb] at he

lemma columnCount_negative_pathEntries (a : Fin 2) (v : Fin (N+1)) :
    columnCount (selected (a,false) (pathEntries P)) v=P.outgoingCount (a,false) v := by
  rw [pathEntries, selected_columnCount_ofFn, HaarPathGraph.Path.outgoingCount]
  congr 1
  ext i
  cases hb : (P.colors i).2 <;> simp [hb,and_comm] <;>
    intro hc <;> have he := congrArg Prod.snd hc <;> simp [hb] at he

/-- Nonvanishing of the actual product Haar integral implies the precise
vertex-by-color balance used in the reduced-path combinatorics. -/
theorem locallyBalanced_of_integral_ne_zero
    (h : (∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N)) ≠ 0) :
    P.LocallyBalanced := by
  have hf : ∀ a : Fin 2,
      (∫ U : LocalUnitary N,
        listMonomial (selected (a,true) (pathEntries P)) (selected (a,false) (pathEntries P)) U
          ∂haar N) ≠ 0 := by
    simp_rw [pathProduct_eq,signedProduct_eq] at h
    rw [integral_prod_mul] at h
    intro a
    fin_cases a
    · exact (mul_ne_zero_iff.mp h).1
    · exact (mul_ne_zero_iff.mp h).2
  intro c v
  obtain ⟨a,b⟩ := c
  have hc := counts_eq_of_integral_ne_zero _ _ (hf a) v
  rw [rowCount_positive_pathEntries, rowCount_negative_pathEntries,
    columnCount_positive_pathEntries,columnCount_negative_pathEntries] at hc
  cases b
  · exact hc.2.symm
  · exact hc.1

/-- The same nonzero integral enforces even path length, independently of the
graph-theoretic argument. -/
theorem even_length_of_integral_ne_zero
    (h : (∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N)) ≠ 0) :
    Even m := by
  have hb : ∀ a : Fin 2,
      (selected (a,true) (pathEntries P)).length=(selected (a,false) (pathEntries P)).length := by
    intro a
    by_contra ha
    apply h
    simp_rw [pathProduct_eq]
    exact integral_signedProduct_eq_zero_of_unbalanced _ a ha
  have hs := selected_lengths (pathEntries P)
  rw [pathEntries_length] at hs
  have h0 := hb 0
  have h1 := hb 1
  refine ⟨(selected (0,true) (pathEntries P)).length+(selected (1,true) (pathEntries P)).length,?_⟩
  omega

/-- The support restriction in BC Corollary 5.5, proved for the actual Haar
expectation and without a matrix-size hypothesis. -/
theorem integral_pathProduct_eq_zero_of_vertices_gt
    (hv : m/2 < P.vertices.card) :
    (∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N))=0 := by
  by_contra hn
  have h := P.vertices_le_half_of_balanced (locallyBalanced_of_integral_ne_zero P hn)
    (even_length_of_integral_ne_zero P hn)
  omega

end Nonadditivity.HaarPathWeights
