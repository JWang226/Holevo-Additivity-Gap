/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathRefinedCounting
import Nonadditivity.HaarOperatorPathSum
import Nonadditivity.HaarPathScalarSummation

/-! # Actual statistics and cardinalities for the nonzero refined classes -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] instBEqOfDecidableEq
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathMultiplicity
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

def refinedSingletonCount (C : RefinedClass V d m) : ℕ :=
  (singletonEdges (Quotient.out C).edgeList).card

def refinedVertexCount (C : RefinedClass V d m) : ℕ :=
  (Quotient.out C).vertices.card

def refinedVertexDeficit (C : RefinedClass V d m) : ℕ :=
  m/2-refinedVertexCount C

theorem refinedSingletonCount_le (C : RefinedClass V d m) :
    refinedSingletonCount C ≤ m := by
  have h := Finset.card_filter_le (Quotient.out C).edgeList.toFinset
    (fun e => (Quotient.out C).edgeList.count e=1)
  have hl := List.toFinset_card_le (Quotient.out C).edgeList
  rw [(Quotient.out C).edgeList_length] at hl
  exact h.trans hl

theorem refinedVertexDeficit_le (C : RefinedClass V d m) :
    refinedVertexDeficit C ≤ m/2 := Nat.sub_le _ _

theorem classDefectTwice_refined_eq (C : RefinedClass V d m) (hm : 0 < m) :
    classDefectTwice hm (refinedToCoarse C)=(Quotient.out C).defectTwice := by
  have hc : (Quotient.mk pathSetoid (Quotient.out C) : PathClass V d m)=
      refinedToCoarse C := by
    rw [←refinedToCoarse_mk,Quotient.out_eq]
  rw [←hc]
  rfl

/-- On the nonvanishing range, the integer graph defect is exactly the
singleton count plus twice the vertex deficit. -/
theorem refined_defect_identity (C : RefinedClass V d m) (hm : 0 < m)
    (ht : Even m) (hv : refinedVertexCount C ≤ m/2) :
    classDefectTwice hm (refinedToCoarse C)=
      refinedSingletonCount C+2*refinedVertexDeficit C := by
  rw [classDefectTwice_refined_eq]
  exact HaarMomentConstants.graph_defect_eq_singletons_add_twice_deficit
    (HaarMomentConstants.even_length_deficit_identity ht hv)

end Nonadditivity.HaarPathClasses

namespace Nonadditivity.HaarOperatorPathBridge
open HaarPathGraph HaarPathClasses HaarPathWeights HaarMomentConstants
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual refined classes whose representative has nonzero Haar weight. -/
def activeRefinedClasses (N t : ℕ) : Finset (RefinedClass (Fin (N+1)) 2 t) :=
  Finset.univ.filter (fun C => pathWeight (Quotient.out C) ≠ 0)

@[simp] theorem mem_activeRefinedClasses {N t : ℕ} (C : RefinedClass (Fin (N+1)) 2 t) :
    C ∈ activeRefinedClasses N t ↔ pathWeight (Quotient.out C) ≠ 0 := by
  simp [activeRefinedClasses]

theorem active_refined_even {N t : ℕ} {C : RefinedClass (Fin (N+1)) 2 t}
    (hC : C ∈ activeRefinedClasses N t) : Even t :=
  even_length_of_integral_ne_zero (Quotient.out C) ((mem_activeRefinedClasses C).mp hC)

theorem active_refined_vertices_le {N t : ℕ} {C : RefinedClass (Fin (N+1)) 2 t}
    (hC : C ∈ activeRefinedClasses N t) : refinedVertexCount C ≤ t/2 := by
  have hn := (mem_activeRefinedClasses C).mp hC
  exact (Quotient.out C).vertices_le_half_of_balanced
    (locallyBalanced_of_integral_ne_zero (Quotient.out C) hn)
    (active_refined_even hC)

theorem active_refined_defect_identity {N t : ℕ} (ht : 0 < t)
    {C : RefinedClass (Fin (N+1)) 2 t} (hC : C ∈ activeRefinedClasses N t) :
    classDefectTwice ht (refinedToCoarse C)=
      refinedSingletonCount C+2*refinedVertexDeficit C :=
  refined_defect_identity C ht (active_refined_even hC) (active_refined_vertices_le hC)

/-- The actual class statistics lie in the finite rectangle used by the
scalar geometric sums. -/
theorem active_refined_stats {N t : ℕ} {C : RefinedClass (Fin (N+1)) 2 t}
    (_hC : C ∈ activeRefinedClasses N t) :
    refinedSingletonCount C < t+1 ∧ refinedVertexDeficit C < t/2+1 := by
  exact ⟨Nat.lt_succ_of_le (refinedSingletonCount_le C),
    Nat.lt_succ_of_le (refinedVertexDeficit_le C)⟩

/-- Actual fixed-statistic fibres inject into the counted fixed-defect
quotient, supplying the scalar summation's cardinality bound. -/
theorem card_active_refined_fibre_le {N t : ℕ} (ht : 0 < t) (e r : ℕ) :
    ((activeRefinedClasses N t).filter
      (fun C => refinedSingletonCount C=e ∧ refinedVertexDeficit C=r)).card ≤
        128^(e+2*r+2)*t^(3*(e+2*r)+6)*(4*t^2)^(3*(e+2*r)+4) := by
  apply card_refined_subfamily_le ht (e+2*r)
  intro C hC
  obtain ⟨hC,he,hr⟩ := Finset.mem_filter.mp hC
  rw [active_refined_defect_identity ht hC,he,hr]

theorem card_active_refined_fibre_le_majorant {N t : ℕ} (ht : 0 < t) (e r : ℕ) :
    (((activeRefinedClasses N t).filter
      (fun C => refinedSingletonCount C=e ∧ refinedVertexDeficit C=r)).card:ℝ) ≤
        refinedClassCountMajorant t e r := by
  unfold refinedClassCountMajorant
  exact_mod_cast card_active_refined_fibre_le (N := N) ht e r

/-- All hypotheses concerning class counts and statistics in the scalar
summation are now discharged for the genuine nonzero refined classes. -/
theorem norm_sum_active_refined_le {E : Type*} [NormedAddCommGroup E]
    {N t : ℕ} (ht : 0 < t) (term : RefinedClass (Fin (N+1)) 2 t → E)
    {p scale : ℝ} (hp : 0 ≤ p) (htp : (t:ℝ) ≤ p) (hscale : 0 ≤ scale)
    (hterm : ∀ C ∈ activeRefinedClasses N t, ‖term C‖ ≤
      refinedClassWeightMajorant p (N+1) t (refinedSingletonCount C)
        (refinedVertexDeficit C)*scale) :
    ‖∑ C ∈ activeRefinedClasses N t, term C‖ ≤
      encodingMajorant p (N+1) t (t+1) (t/2+1)*scale := by
  apply norm_sum_classes_le_encodingMajorant (activeRefinedClasses N t)
    refinedSingletonCount refinedVertexDeficit term hp (by positivity)
    (by exact_mod_cast ht) htp hscale (t+1) (t/2+1)
  · intro C hC
    exact active_refined_stats hC
  · intro e _ r _
    exact card_active_refined_fibre_le_majorant ht e r
  · exact hterm

/-- Moment-sized rectangle, matching `OnePairLengthBounds` exactly. -/
theorem norm_sum_active_refined_le_moment {E : Type*} [NormedAddCommGroup E]
    {N p t : ℕ} (ht : 0 < t) (htp : t ≤ p)
    (term : RefinedClass (Fin (N+1)) 2 t → E)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hterm : ∀ C ∈ activeRefinedClasses N t, ‖term C‖ ≤
      refinedClassWeightMajorant p (N+1) t (refinedSingletonCount C)
        (refinedVertexDeficit C)*scale) :
    ‖∑ C ∈ activeRefinedClasses N t, term C‖ ≤
      encodingMajorant p (N+1) t (p+1) (p+1)*scale := by
  apply norm_sum_classes_le_encodingMajorant (activeRefinedClasses N t)
    refinedSingletonCount refinedVertexDeficit term (by positivity) (by positivity)
    (by exact_mod_cast ht) (by exact_mod_cast htp) hscale (p+1) (p+1)
  · intro C hC
    have hs := active_refined_stats hC
    have hh := Nat.div_le_self t 2
    omega
  · intro e _ r _
    exact card_active_refined_fibre_le_majorant ht e r
  · exact hterm

end Nonadditivity.HaarOperatorPathBridge
