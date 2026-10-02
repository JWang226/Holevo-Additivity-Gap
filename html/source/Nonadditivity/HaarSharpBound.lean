/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarSharpSummation
import Nonadditivity.HaarPrescribedBound

/-! # The one-pair Haar bound at the original dimension threshold

Chronological weighted class counting replaces the loose padded-list bound.
The statement uses the actual Haar integral with all remaining free factors.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarSharpBound
open HaarOperatorPathBridge HaarPathGraph HaarPathClasses HaarMomentConstants
  HaarOperatorCurry HaarOnePairAssembly HaarWordExpansion HaarIteratedMoments
  HaarMixedWordExpansion HaarTensorReplacement MeasureTheory ProductHaagerupProduct
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_path_sum_bound {N p t : ℕ} (hp : 2≤p) (ht : 0<t) (htp : t≤p)
    (hN : 2^32*(p:ℝ)^80≤N+1)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E)
    {scale : ℝ} (hscale : 0≤scale)
    (hb : ∀ P : Path (Fin (N+1)) 2 t, pathWeight P≠0 →
      ‖refinedCoefficientSum A p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*scale)) :
    ‖(1/(N+1:ℂ)) • pathOperatorSum N A p t‖ ≤
      (4096*(p:ℝ)^25/(N+1)*(1+64/(p:ℝ))^p)*scale := by
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
  rw [pathOperatorSum_eq_weighted_refinedSum N A p t (fun _ _ h => pathWeight_eq_of_refined h),
    Finset.smul_sum]
  change ‖∑ C, term C‖ ≤ _
  rw [hs]
  calc
    _ ≤ ∑ C ∈ activeRefinedClasses N t, ‖term C‖ := norm_sum_le _ _
    _ ≤ ∑ C ∈ activeRefinedClasses N t,
        refinedClassWeightMajorant p (N+1) t
          (refinedSingletonCount C) (refinedVertexDeficit C)*scale := by
      apply Finset.sum_le_sum
      intro C hC
      have hn := (mem_activeRefinedClasses C).mp hC
      exact HaarSharpPathWeight.normalized_pathWeight_smul_norm_le hp ht htp hN
        (Quotient.out C) hn (refinedCoefficientSum A p (Quotient.out C)) hscale
        (hb (Quotient.out C) hn)
    _ = (∑ C ∈ activeRefinedClasses N t,
        refinedClassWeightMajorant p (N+1) t
          (refinedSingletonCount C) (refinedVertexDeficit C))*scale := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (HaarSharpSummation.sum_active_weights_le hp ht htp hN) hscale

theorem mixed_length_bound {N p : ℕ} (hp : 2≤p) (hN : 2^32*(p:ℝ)^80≤N+1)
    (j : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MatrixPolynomial (ProductHaagerupProduct.GroupIndex (Fin 2) (j+1)) ι)
    (hlinear : ∀ w ∈ f.support, RadiusLe 1 w) (t : ℕ) (ht : t ∈ Finset.Icc 1 p) :
    ‖mixedLengthContribution (pairMeasure N) (pairMatrix N) f p t‖ ≤
      (4096*(p:ℝ)^25/(N+1)*(1+64/(p:ℝ))^p)*‖regularEval f‖^p := by
  have ht0 := (Finset.mem_Icc.mp ht).1
  have htp := (Finset.mem_Icc.mp ht).2
  have hA := operatorCurry_linear f (fun w hw => (hlinear w hw).1)
  have hb : ∀ P : Path (Fin (N+1)) 2 t, pathWeight P≠0 →
      ‖refinedCoefficientSum (operatorCurry f) p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*‖regularEval f‖^p) := by
    intro P _
    have h := coefficient_bound (operatorCurry f) hA p (by omega) P ht0
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,operatorCurry_norm,mul_assoc] using h
  have h := normalized_path_sum_bound hp ht0 htp hN
    (operatorCurry f) (pow_nonneg (norm_nonneg _) p) hb
  have he : ‖(N:ℂ)+1‖=(N:ℝ)+1 := by exact_mod_cast Complex.norm_natCast (N+1)
  rw [norm_smul,norm_div,norm_one,he,one_div_mul_eq_div] at h
  exact mixedLengthContribution_le_of_pathSum N p t ht0 f
    ((div_le_iff₀ (by positivity : (0:ℝ)<N+1)).mp h |>.trans_eq (mul_comm _ _))

/-- The original `2^32 p^80` moment range is recovered with the corrected
path and coefficient estimates, with no analytic premise. -/
theorem onePairTraceBound {N p : ℕ} (hp : 2≤p)
    (hN : 2^32*(p:ℝ)^80≤N+1) : OnePairTraceBound N p := by
  intro j ι _ _ _ f hf hlinear
  have he := integral_mixed_error_by_length (pairMeasure N) (pairMatrix N) f p
    (fun w hw => (hlinear w hw).1) (integrable_pair_word_trace N)
  have hi := (continuous_mixed_moment N p j f).integrable_of_hasCompactSupport
    (μ := pairMeasure N) (HasCompactSupport.of_compactSpace _)
  have hre := congrArg Complex.re he
  rw [Complex.sub_re,Complex.re_sum] at hre
  have hir := integral_re hi
  simp only [RCLike.re_eq_complex_re] at hir
  change (∫ U : Pair N, (vacuumTrace ((partialEval (pairMatrix N U) f)^p)).re
    ∂pairMeasure N) ≤ _
  rw [hir]
  have hb : (∑ t ∈ Finset.Icc 1 p,
      (mixedLengthContribution (pairMeasure N) (pairMatrix N) f p t).re) ≤
      (N+1:ℝ)^(-(1/2:ℝ))*‖regularEval f‖^p := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc 1 p,
          (4096*(p:ℝ)^25/(N+1)*(1+64/(p:ℝ))^p)*‖regularEval f‖^p := by
        apply Finset.sum_le_sum
        intro t ht
        exact (Complex.re_le_norm _).trans (mixed_length_bound hp hN j ι f hlinear t ht)
      _ = (4096*(p:ℝ)^26/(N+1)*(1+64/(p:ℝ))^p)*‖regularEval f‖^p := by
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
          nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (HaarSharpConstants.sharp_final_error_bound hp hN) (pow_nonneg (norm_nonneg _) p)
  linarith

end Nonadditivity.HaarSharpBound
