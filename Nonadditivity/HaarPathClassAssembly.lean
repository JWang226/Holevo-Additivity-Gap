/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClassSums
import Nonadditivity.HaarPathClassStats
import Nonadditivity.HaarPathWeightBudget
import Nonadditivity.HaarRefinedWeight

/-! # The complete actual path-class summation

All quotient counts, graph statistics, scalar weights, and finite sums are
discharged here. The two analytic class inputs are isolated as the equality of
actual Haar weights and the bound on actual grouped operator coefficients.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarOperatorPathBridge
open HaarPathGraph HaarPathClasses HaarMomentConstants
open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The normalized literal path sum is bounded by the prescribed encoding
majorant as soon as its two actual class estimates are supplied. -/
theorem norm_normalized_pathOperatorSum_le_of_refined_estimates
    {N p t : ℕ} (hp : 2 ≤ p) (ht : 0 < t) (htp : t ≤ p)
    (hN : 2^80*(p:ℝ)^80 ≤ N+1)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hw : ∀ P Q : Path (Fin (N+1)) 2 t, RefinedPattern P Q → pathWeight P=pathWeight Q)
    (hb : ∀ P : Path (Fin (N+1)) 2 t, pathWeight P ≠ 0 →
      ‖refinedCoefficientSum A p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*scale)) :
    ‖(1/(N+1:ℂ)) • pathOperatorSum N A p t‖ ≤
      encodingMajorant p (N+1) t (p+1) (p+1)*scale := by
  classical
  let term : RefinedClass (Fin (N+1)) 2 t → E →L[ℂ] E := fun C =>
    (1/(N+1:ℂ)) • (pathWeight (Quotient.out C) • refinedCoefficientSum A p (Quotient.out C))
  have hs : (∑ C, term C)=∑ C ∈ activeRefinedClasses N t, term C := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro C _ hC
    have hz : pathWeight (Quotient.out C)=0 := by
      by_contra hn
      exact hC ((mem_activeRefinedClasses C).mpr hn)
    simp only [term,hz,zero_smul,smul_zero]
  rw [pathOperatorSum_eq_weighted_refinedSum N A p t hw,Finset.smul_sum]
  change ‖∑ C, term C‖ ≤ _
  rw [hs]
  apply norm_sum_active_refined_le_moment ht htp term hscale
  intro C hC
  have hn := (mem_activeRefinedClasses C).mp hC
  exact normalized_pathWeight_smul_norm_le hp ht htp hN (Quotient.out C) hn
    (refinedCoefficientSum A p (Quotient.out C)) hscale (hb (Quotient.out C) hn)

/-- Equivalent unnormalized form for the established trace-to-path bridge. -/
theorem norm_pathOperatorSum_le_of_refined_estimates
    {N p t : ℕ} (hp : 2 ≤ p) (ht : 0 < t) (htp : t ≤ p)
    (hN : 2^80*(p:ℝ)^80 ≤ N+1)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hw : ∀ P Q : Path (Fin (N+1)) 2 t, RefinedPattern P Q → pathWeight P=pathWeight Q)
    (hb : ∀ P : Path (Fin (N+1)) 2 t, pathWeight P ≠ 0 →
      ‖refinedCoefficientSum A p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*scale)) :
    ‖pathOperatorSum N A p t‖ ≤
      (N+1:ℝ)*(encodingMajorant p (N+1) t (p+1) (p+1)*scale) := by
  have h := norm_normalized_pathOperatorSum_le_of_refined_estimates hp ht htp hN A hscale hw hb
  have hn : ‖(N:ℂ)+1‖=(N:ℝ)+1 := by exact_mod_cast Complex.norm_natCast (N+1)
  rw [norm_smul,norm_div,norm_one,hn,one_div_mul_eq_div] at h
  exact (div_le_iff₀ (by positivity : (0:ℝ) < N+1)).mp h |>.trans_eq (mul_comm _ _)

/-- Equality of the actual Haar weights on every genuine refined class. -/
theorem pathWeight_eq_of_refined {N t : ℕ} {P Q : Path (Fin (N+1)) 2 t}
    (h : RefinedPattern P Q) : pathWeight P=pathWeight Q :=
  h.integral_pathProduct_eq

/-- Every combinatorial and Haar-integral input is discharged; only the
actual grouped operator coefficient estimate is required. -/
theorem norm_normalized_pathOperatorSum_le_of_coefficient_bound
    {N p t : ℕ} (hp : 2 ≤ p) (ht : 0 < t) (htp : t ≤ p)
    (hN : 2^80*(p:ℝ)^80 ≤ N+1)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hb : ∀ P : Path (Fin (N+1)) 2 t, pathWeight P ≠ 0 →
      ‖refinedCoefficientSum A p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*scale)) :
    ‖(1/(N+1:ℂ)) • pathOperatorSum N A p t‖ ≤
      encodingMajorant p (N+1) t (p+1) (p+1)*scale :=
  norm_normalized_pathOperatorSum_le_of_refined_estimates hp ht htp hN A hscale
    (fun _ _ h => pathWeight_eq_of_refined h) hb

theorem norm_pathOperatorSum_le_of_coefficient_bound
    {N p t : ℕ} (hp : 2 ≤ p) (ht : 0 < t) (htp : t ≤ p)
    (hN : 2^80*(p:ℝ)^80 ≤ N+1)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hb : ∀ P : Path (Fin (N+1)) 2 t, pathWeight P ≠ 0 →
      ‖refinedCoefficientSum A p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*scale)) :
    ‖pathOperatorSum N A p t‖ ≤
      (N+1:ℝ)*(encodingMajorant p (N+1) t (p+1) (p+1)*scale) :=
  norm_pathOperatorSum_le_of_refined_estimates hp ht htp hN A hscale
    (fun _ _ h => pathWeight_eq_of_refined h) hb

end Nonadditivity.HaarOperatorPathBridge
