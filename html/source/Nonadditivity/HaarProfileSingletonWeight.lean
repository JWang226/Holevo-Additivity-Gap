/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfilePatternBound
import Nonadditivity.NoncommutativeCSSingletons
import Nonadditivity.HaarChainMultiplicity

/-! # Exact two-generator singleton weight in endpoint skeletons -/
noncomputable section
open scoped BigOperators
namespace Nonadditivity.NoncommutativeCS.EndpointSkeleton
variable {I : Type*}

def singletonLength {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (size : I → ℕ) : ℕ :=
  match P with
  | .done _ => 0
  | .first _ P => P.singletonLength size
  | .last _ P => P.singletonLength size
  | .middle _ P => P.singletonLength size
  | .singleton i P => size i + P.singletonLength size

theorem sqrt_four_nat_pow (k : ℕ) :
    Real.sqrt (((2*2)^k : ℕ) : ℝ) = (2:ℝ)^k := by
  have he : (((2*2)^k : ℕ) : ℝ) = ((2:ℝ)^k)^2 := by
    calc
      _ = ((2:ℝ)^2)^k := by norm_num
      _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm 2 k]
  rw [he,Real.sqrt_sq (by positivity)]

/-- Each once-used chain costs exactly two to the power of its length. -/
theorem singletonWeight_two {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (size : I → ℕ) :
    P.singletonWeight size 2 = (2:ℝ)^P.singletonLength size := by
  induction P with
  | done => simp [singletonWeight,singletonLength]
  | first i P ih => exact ih
  | last p P ih => exact ih
  | middle v P ih => exact ih
  | singleton i P ih =>
      simp only [singletonWeight,singletonLength,ih,sqrt_four_nat_pow,pow_add,mul_comm]

theorem singletonLength_eq_map_sum {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (size : I → ℕ) :
    P.singletonLength size=(P.singletonLabels.map size).sum := by
  induction P <;> simp_all [singletonLength,singletonLabels]

/-- The singleton cost records literal once-occurring labels, independently
of how the valid endpoint skeleton was obtained. -/
theorem singletonLength_eq_sum_count_one [DecidableEq I]
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.profileLabels.Nodup) (size : I → ℕ) :
    P.singletonLength size = ∑ i ∈ P.word.toFinset.filter (fun i => P.word.count i=1), size i := by
  rw [singletonLength_eq_map_sum,HaarPathMultiplicity.sum_occurrence_weights]
  have hh : (∑ i ∈ P.singletonLabels.toFinset, P.singletonLabels.count i • size i) =
      ∑ i ∈ P.singletonLabels.toFinset, size i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [List.count_eq_one_of_mem (P.singletonLabels_nodup hP) (List.mem_toFinset.mp hi),one_nsmul]
  rw [hh,P.closed_singletonLabels_toFinset hP]

/-- The skeleton's singleton exponent is the original path's exact
singleton-edge count. -/
theorem singletonLength_chain_labels {V : Type*} [DecidableEq V] {d t : ℕ}
    (P : HaarPathGraph.Path V d t) (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList)
    (R : EndpointSkeleton P.unorientedChains
      (Fin.elim0 : Fin 0 → P.unorientedChains) (Fin.elim0 : Fin 0 → P.unorientedChains))
    (hR : R.profileLabels.Nodup) (hw : R.word=cs.map P.chainLabel) :
    R.singletonLength (fun e => (P.representative e).val.length) =
      (HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  classical
  have hc : (cs.map P.chainLabel).toFinset=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    obtain ⟨c,hc,he⟩ := P.chainLabels_cover cs hcs e
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨c,hc,he⟩)
  rw [R.singletonLength_eq_sum_count_one hR,hw,hc]
  simpa only [List.count_eq_countP,Bool.beq_eq_decide_eq] using
    (P.singletonEdges_card_eq_chain_lengths cs hcs).symm

theorem singletonWeight_chain_labels {V : Type*} [DecidableEq V] {t : ℕ}
    (P : HaarPathGraph.Path V 2 t) (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList)
    (R : EndpointSkeleton P.unorientedChains
      (Fin.elim0 : Fin 0 → P.unorientedChains) (Fin.elim0 : Fin 0 → P.unorientedChains))
    (hR : R.profileLabels.Nodup) (hw : R.word=cs.map P.chainLabel) :
    R.singletonWeight (fun e => (P.representative e).val.length) 2 =
      (2:ℝ)^(HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  rw [R.singletonWeight_two,R.singletonLength_chain_labels P cs hcs hR hw]

/-- The endpoint compiler reads factors in reverse order. Reversing the
occurrence list leaves the exact singleton budget unchanged. -/
theorem singletonWeight_chain_labels_reverse {V : Type*} [DecidableEq V] {t : ℕ}
    (P : HaarPathGraph.Path V 2 t) (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList)
    (R : EndpointSkeleton P.unorientedChains
      (Fin.elim0 : Fin 0 → P.unorientedChains) (Fin.elim0 : Fin 0 → P.unorientedChains))
    (hR : R.profileLabels.Nodup) (hw : R.word=(cs.map P.chainLabel).reverse) :
    R.singletonWeight (fun e => (P.representative e).val.length) 2 =
      (2:ℝ)^(HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  classical
  rw [R.singletonWeight_two]
  congr 1
  have hc : (cs.map P.chainLabel).toFinset=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro e
    obtain ⟨c,hc,he⟩ := P.chainLabels_cover cs hcs e
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨c,hc,he⟩)
  rw [R.singletonLength_eq_sum_count_one hR,hw]
  simp only [List.toFinset_reverse,List.count_reverse,hc]
  simpa only [List.count_eq_countP,Bool.beq_eq_decide_eq] using
    (P.singletonEdges_card_eq_chain_lengths cs hcs).symm

theorem coefficient_exponent_chain_le {V : Type*} [DecidableEq V] {d t : ℕ}
    (P : HaarPathGraph.Path V d t) :
    6*Fintype.card P.unorientedChains-1 ≤ 9*P.defectTwice+11 := by
  rw [Fintype.card_coe]
  have h := P.twice_card_unorientedChains_le_defect
  omega

end Nonadditivity.NoncommutativeCS.EndpointSkeleton
