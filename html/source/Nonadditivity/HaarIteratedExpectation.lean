/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarIteratedMoments

/-! # The explicit expected-norm factor for literal Haar replacement

Jensen is applied only to the continuous one-coordinate norm. This avoids any
extra integrability assumptions about the recursively integrated expression.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Nonadditivity.HaarIteratedMoments
open MeasureTheory HaarModel HaarWordExpansion HaarTensorReplacement
open HaarHybridMoments HaarTensorConstants ProductHaagerupProduct HaarMomentExpectation
open scoped BigOperators Matrix Matrix.Norms.L2Operator

theorem iteratedExpectation_le (N p : ℕ) (hp : Even p) (hp2 : 2 ≤ p)
    (hone : OnePairTraceBound N p) (j : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) j) ι)
    (hf : IsSelfAdjoint (regularEval f))
    (hlinear : ∀ w ∈ f.support, RadiusLe 1 w) :
    iteratedMoment N 1 j f ≤ ‖regularEval f‖ *
      (replacementMultiplier (Fintype.card ι) (N+1) p j)^(1/(p:ℝ)) := by
  induction j generalizing ι with
  | zero => simp [iteratedMoment, replacementMultiplier, triangle]
  | succ j ih =>
    let C := replacementMultiplier ((Fintype.card ι : ℝ)*(N+1)) (N+1) p j
    let S : ℝ := 2*(Fintype.card ι:ℝ)*(N+1)*(p:ℝ)^(3*j)*
      (1+(N+1:ℝ)^(-(1/2:ℝ)))
    have hC : 0 ≤ C := by unfold C replacementMultiplier; positivity
    have hS : 0 ≤ S := by unfold S; positivity
    have hi : ∀ U : Pair N,
        iteratedMoment N 1 j
          (partialEval (representationMatrix (pairRepresentation N U)) f) ≤
        C^(1/(p:ℝ)) * ‖regularEval (partialEval (representationMatrix (pairRepresentation N U)) f)‖ := by
      intro U
      have hl : ∀ w ∈ (partialEval (representationMatrix (pairRepresentation N U)) f).support,
          RadiusLe 1 w := by
        intro w hw
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (partialEval_support _ f hw)
        exact (hlinear v hv).2
      simpa only [C, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, mul_comm] using ih _ (partialEval_selfAdjoint _ f hf) hl
    have hintp := integrable_partial_regularNorm_pow (pairMeasure N)
      (fun U => representationMatrix (pairRepresentation N U))
      (continuous_pairRepresentation N) f p
    have hint : Integrable (fun U : Pair N =>
        ‖regularEval (partialEval (representationMatrix (pairRepresentation N U)) f)‖)
          (pairMeasure N) := by
      simpa only [pow_one] using integrable_partial_regularNorm_pow (pairMeasure N)
        (fun U => representationMatrix (pairRepresentation N U))
        (continuous_pairRepresentation N) f 1
    have hstep : (∫ U : Pair N,
        ‖regularEval (partialEval (representationMatrix (pairRepresentation N U)) f)‖^p
          ∂pairMeasure N) ≤ S * ‖regularEval f‖^p := by
      simpa only [S, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        replacement_norm_moment_le (pairMeasure N) (pairRepresentation N)
          (continuous_pairRepresentation N) f hf (fun w hw => (hlinear w hw).2)
          hp hp2 ((N+1:ℝ)^(-(1/2:ℝ))) (hone j ι f hf hlinear)
    have hmean := integral_le_mul_rpow_of_moment_le (by omega : 0 < p)
      (Filter.Eventually.of_forall (fun U => norm_nonneg
        (regularEval (partialEval (representationMatrix (pairRepresentation N U)) f))))
      hint hintp hS (norm_nonneg _) hstep
    have hle := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun U => iteratedMoment_nonneg N 1 j _))
      (hint.const_mul (C^(1/(p:ℝ)))) (Filter.Eventually.of_forall hi)
    rw [integral_const_mul] at hle
    apply hle.trans
    apply (mul_le_mul_of_nonneg_left hmean (Real.rpow_nonneg hC _)).trans_eq
    calc
      _ = ‖regularEval f‖ * (C*S)^(1/(p:ℝ)) := by rw [Real.mul_rpow hC hS]; ring
      _ = _ := by
        congr 2
        exact replacementMultiplier_succ (Fintype.card ι) (N+1) p j

/-- The exact logarithmic multiplier consumed by the prescribed-dimension
channel theorem, for the literal recursively integrated Haar model. -/
theorem iteratedExpectation_prescribed_le {h : ℝ} {n N : ℕ}
    (hh : (2:ℝ)/3 ≤ h) (hn : 2 ≤ n)
    (hD : N+1 = Quantitative.dimensionChoice h n)
    (hone : OnePairTraceBound N (Quantitative.momentParameter h n))
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) n) ι)
    (hf : IsSelfAdjoint (regularEval f))
    (hlinear : ∀ w ∈ f.support, RadiusLe 1 w) :
    iteratedMoment N 1 n f ≤ ‖regularEval f‖ *
      Real.exp (Quantitative.haarLogMultiplier h n (Real.log (2*(Fintype.card ι:ℝ)))) := by
  obtain ⟨hp,hp2,_,_⟩ := Quantitative.moment_parameter_bounds (n := (n:ℝ)) hh (by exact_mod_cast hn)
  have hb := iteratedExpectation_le N (Quantitative.momentParameter h n) hp hp2 hone n f hf hlinear
  have hm : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hmult := replacementMultiplier_le (n := n) hm (show (0:ℝ) ≤ N+1 by positivity) (by omega :
    1 ≤ Quantitative.momentParameter h n)
  have hroot := Real.rpow_le_rpow
    (replacementMultiplier_nonneg (by positivity : (0:ℝ) ≤ Fintype.card ι)
      (show (0:ℝ) ≤ N+1 by positivity) (Quantitative.momentParameter h n) n)
    hmult (show 0 ≤ 1/(Quantitative.momentParameter h n:ℝ) by positivity)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have he : (N+1:ℝ) = (Quantitative.dimensionChoice h n:ℝ) := by exact_mod_cast hD
  rw [he] at hroot ⊢
  exact hroot.trans_eq (momentMultiplier_root_eq_exp hh hn (by positivity))

end Nonadditivity.HaarIteratedMoments
