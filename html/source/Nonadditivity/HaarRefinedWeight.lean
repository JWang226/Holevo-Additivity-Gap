/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarChainReindex
import Nonadditivity.HaarProfilePermutations
import Nonadditivity.HaarPathWeightTransport

/-! # Haar weights are constant on actual refined path classes

Equal complete-chain profiles give endpoint-fixed permutations of the positions
inside each unoriented core edge. They preserve reversal and directed traversal
multiplicity. Independent row and column Haar invariance then identifies the
literal expectations, without a weight-invariance hypothesis.
-/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles HaarProfilePermutations
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}
variable {P Q : Path V d m}

namespace SamePattern

def dartEquiv (h : SamePattern P Q) : P.darts ≃ Q.darts where
  toFun q := ⟨h.dartPerm q.val,(h.dartPerm_mem_iff q.val).mpr q.property⟩
  invFun q := ⟨h.dartPerm.symm q.val,(h.dartPerm_mem_iff _).mp (by simpa using q.property)⟩
  left_inv := by intro q; apply Subtype.ext; exact h.dartPerm.symm_apply_apply q.val
  right_inv := by intro q; apply Subtype.ext; exact h.dartPerm.apply_symm_apply q.val

@[simp] theorem dartEquiv_val (h : SamePattern P Q) (q : P.darts) :
    (h.dartEquiv q).val=h.dartPerm q.val := rfl

theorem dartEquiv_count (h : SamePattern P Q) (q : P.darts) :
    P.traversalList.count q.val=Q.traversalList.count (h.dartEquiv q).val := by
  rw [dartEquiv_val,←h.traversalList_map,List.count_map_of_injective _ _ h.dartPerm.injective]

end SamePattern
namespace RefinedPattern

def positionPerm (h : RefinedPattern P Q) (e : P.unorientedChains) :
    Equiv.Perm (Fin (P.representative e).val.length) :=
  Classical.choose (exists_coreChain_positionPerm h (P.representative e))

theorem positionPerm_color (h : RefinedPattern P Q) (e : P.unorientedChains)
    (i : Fin (P.representative e).val.length) :
    color (h.samePattern.dartPerm ((P.representative e).val.get (h.positionPerm e i)))=
      color ((P.representative e).val.get i) :=
  (Classical.choose_spec (exists_coreChain_positionPerm h (P.representative e))).1 i

theorem positionPerm_fix (h : RefinedPattern P Q) (e : P.unorientedChains)
    (i : Fin (P.representative e).val.length)
    (hi : i.val=0 ∨ i.val+1=(P.representative e).val.length) : h.positionPerm e i=i :=
  (Classical.choose_spec (exists_coreChain_positionPerm h (P.representative e))).2 i hi

/-- An actual dart bijection, built from profile equality alone. -/
def weightDartEquiv (h : RefinedPattern P Q) : P.darts ≃ Q.darts :=
  (P.chainReindex h.positionPerm).trans h.samePattern.dartEquiv

@[simp] theorem weightDartEquiv_val (h : RefinedPattern P Q) (q : P.darts) :
    (h.weightDartEquiv q).val=h.samePattern.dartPerm (P.chainReindex h.positionPerm q).val := rfl

theorem weightDartEquiv_color (h : RefinedPattern P Q) (q : P.darts) :
    color (h.weightDartEquiv q).val=color q.val := by
  obtain ⟨⟨e,i,b⟩,rfl⟩ := P.representativePositionEquiv.surjective q
  rw [h.weightDartEquiv_val,P.chainReindex_apply_position]
  simp only [P.representativePositionEquiv_val]
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    rw [h.samePattern.dartPerm_reverse (P.toCore_mem (P.representative e).property.1 (List.get_mem _ _))]
    exact congrArg (fun c : Color d => flipColor c) (h.positionPerm_color e i)
  · exact h.positionPerm_color e i

theorem weightDartEquiv_core (h : RefinedPattern P Q) (q : P.darts)
    (hq : source q.val∈P.coreVertices) :
    source (h.weightDartEquiv q).val=h.samePattern.vertexPerm (source q.val) := by
  rw [h.weightDartEquiv_val,P.chainReindex_fixed_core _ h.positionPerm_fix q hq]
  exact h.samePattern.source_dartPerm q.property

theorem weightDartEquiv_core_iff (h : RefinedPattern P Q) (q : P.darts) :
    source (h.weightDartEquiv q).val∈Q.coreVertices ↔ source q.val∈P.coreVertices := by
  rw [h.weightDartEquiv_val,h.samePattern.source_dartPerm (P.chainReindex h.positionPerm q).property,
    h.samePattern.vertexPerm_mem_core_iff]
  exact P.chainReindex_mem_core_iff _ h.positionPerm_fix q

theorem weightDartEquiv_reverse (h : RefinedPattern P Q) (q : P.darts) :
    h.weightDartEquiv ⟨reverse q.val,P.reverse_mem q.property⟩ =
      ⟨reverse (h.weightDartEquiv q).val,Q.reverse_mem (h.weightDartEquiv q).property⟩ := by
  apply Subtype.ext
  rw [h.weightDartEquiv_val,P.chainReindex_reverse]
  exact h.samePattern.dartPerm_reverse (P.chainReindex h.positionPerm q).property

theorem weightDartEquiv_count (h : RefinedPattern P Q) (q : P.darts) :
    P.traversalList.count q.val=Q.traversalList.count (h.weightDartEquiv q).val :=
  (P.chainReindex_count h.positionPerm q).trans
    (h.samePattern.dartEquiv_count (P.chainReindex h.positionPerm q))

/-- BC Lemma 5.7 for the literal pair-Haar path integral. No invariance premise
or dimension restriction is needed. -/
theorem integral_pathProduct_eq {N m : ℕ} {P Q : Path (Fin (N+1)) 2 m}
    (h : RefinedPattern P Q) :
    (∫ U : HaarModel.LocalUnitary N × HaarModel.LocalUnitary N,
      HaarPathWeights.pathProduct P U ∂(HaarModel.haar N).prod (HaarModel.haar N)) =
    ∫ U : HaarModel.LocalUnitary N × HaarModel.LocalUnitary N,
      HaarPathWeights.pathProduct Q U ∂(HaarModel.haar N).prod (HaarModel.haar N) := by
  exact HaarPathWeightTransport.integral_pathProduct_eq_of_dart_transport h.samePattern
    h.weightDartEquiv h.weightDartEquiv_color h.weightDartEquiv_core
    h.weightDartEquiv_core_iff h.weightDartEquiv_reverse (by
      intro q
      simpa only [List.count, Bool.beq_eq_decide_eq] using h.weightDartEquiv_count q)

end RefinedPattern
end Nonadditivity.HaarPathClasses
