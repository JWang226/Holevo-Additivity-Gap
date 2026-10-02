/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarEntryBound
import Mathlib.MeasureTheory.Integral.Prod

/-! # The explicit weight of two independent Haar entry monomials

The probability law is the actual product of normalized Haar measures.
The result includes absent families and preserves singleton suppression.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarInvariantTensor
open MeasureTheory HaarModel HaarPathMultiplicity
open scoped Matrix Matrix.Norms.L2Operator

theorem norm_pair_entry_moment_le {N p q P : ℕ}
    (hpP : p ≤ P) (hqP : q ≤ P) (hN : 16*(P:ℝ)^4 ≤ N+1)
    (i j k l : Tuple N p) (a b c d : Tuple N q) :
    ‖∫ U : LocalUnitary N × LocalUnitary N,
        HaarMixedMoments.entryMonomial i j k l U.1 *
          HaarMixedMoments.entryMonomial a b c d U.2 ∂(haar N).prod (haar N)‖ ≤
      (4/(N+1:ℝ)^(p+q)) *
        (P:ℝ)^(highMultiplicityOccurrences (entryList i j k l)/2 +
          highMultiplicityOccurrences (entryList a b c d)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^
          ((singletonEdges (entryList i j k l)).card +
            (singletonEdges (entryList a b c d)).card) := by
  rw [integral_prod_mul (μ := haar N) (ν := haar N) (HaarMixedMoments.entryMonomial i j k l)
    (HaarMixedMoments.entryMonomial a b c d), norm_mul]
  have h₁ := norm_entry_moment_le_uniform hpP hN i j k l
  have h₂ := norm_entry_moment_le_uniform hqP hN a b c d
  apply (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq
  simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The manuscript's moment range implies the entry estimate's dimension
condition with a substantial margin. -/
theorem entry_dimension_of_manuscript_range {P M : ℕ} {D : ℝ}
    (hM : 1 ≤ M) (hPM : P ≤ M) (hD : 2^32*(M:ℝ)^80 ≤ D) :
    16*(P:ℝ)^4 ≤ D := by
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hPMr : (P:ℝ) ≤ M := by exact_mod_cast hPM
  have h₁ := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ P) hPMr 4
  have h₂ := pow_le_pow_right₀ hM1 (by omega : 4 ≤ 80)
  have h₃ : 0 ≤ (M:ℝ)^80 := by positivity
  norm_num at hD
  nlinarith

theorem continuous_entryMonomial {N p q : ℕ}
    (i j : Tuple N p) (k l : Tuple N q) :
    Continuous (HaarMixedMoments.entryMonomial i j k l) := by
  unfold HaarMixedMoments.entryMonomial
  apply Continuous.mul
  · exact continuous_finset_prod _ (fun a _ => HaarMoments.continuous_entry (i a) (j a))
  · exact continuous_finset_prod _ (fun a _ => (HaarMoments.continuous_entry (k a) (l a)).star)

/-- The same bound on two distinct coordinates of the manuscript's existing
canonical Haar sample space; no change of probability model is assumed. -/
theorem norm_sample_pair_entry_moment_le {N p q P : ℕ}
    (K n : ℕ) (x y : Fin n × Fin K) (hxy : x ≠ y)
    (hpP : p ≤ P) (hqP : q ≤ P) (hN : 16*(P:ℝ)^4 ≤ N+1)
    (i j k l : Tuple N p) (a b c d : Tuple N q) :
    ‖∫ ω : Sample K n N,
        HaarMixedMoments.entryMonomial i j k l (ω x) *
          HaarMixedMoments.entryMonomial a b c d (ω y) ∂sampleMeasure K n N‖ ≤
      (4/(N+1:ℝ)^(p+q)) *
        (P:ℝ)^(highMultiplicityOccurrences (entryList i j k l)/2 +
          highMultiplicityOccurrences (entryList a b c d)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^
          ((singletonEdges (entryList i j k l)).card +
            (singletonEdges (entryList a b c d)).card) := by
  have hf := continuous_entryMonomial i j k l
  have hg := continuous_entryMonomial a b c d
  have hind := ((independent_coordinates K n N).indepFun hxy).comp hf.measurable hg.measurable
  have he := hind.integral_fun_mul_eq_mul_integral
    (hf.comp (continuous_apply x)).aestronglyMeasurable
    (hg.comp (continuous_apply y)).aestronglyMeasurable
  have hx := integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := x)
    hf.aestronglyMeasurable
  have hy := integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := y)
    hg.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [he]
  simp only [sampleMeasure]
  rw [hx, hy]
  have hb := norm_pair_entry_moment_le hpP hqP hN i j k l a b c d
  rw [integral_prod_mul (μ := haar N) (ν := haar N)
    (HaarMixedMoments.entryMonomial i j k l) (HaarMixedMoments.entryMonomial a b c d)] at hb
  exact hb

end Nonadditivity.HaarInvariantTensor
