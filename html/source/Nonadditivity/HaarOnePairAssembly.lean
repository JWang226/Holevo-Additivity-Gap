/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMixedWordExpansion
import Nonadditivity.HaarEncodingSlack
import Nonadditivity.HaarIteratedMoments

/-! # Assembling the mixed one-pair trace estimate from path-length bounds

This module assembles a bound on the actual length contributions into the
one-pair trace comparison consumed by the checked tensor induction. The length
bound itself is proved in `HaarPrescribedBound.onePairLengthBounds`. The corrected
majorant includes the extra `t^3` and all local color marks.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarOnePairAssembly
open MeasureTheory HaarWordExpansion HaarTensorReplacement HaarMixedWordExpansion
open HaarMomentConstants HaarIteratedMoments ProductHaagerupProduct
open scoped BigOperators Matrix Matrix.Norms.L2Operator

def pairMatrix (N : ℕ) (U : Pair N) := representationMatrix (pairRepresentation N U)

theorem continuous_pair_word_trace (N : ℕ) (g : FreeGroup (Fin 2)) :
    Continuous (fun U : Pair N => normalizedTrace (pairMatrix N U g)) := by
  unfold normalizedTrace Matrix.trace
  apply Continuous.div_const
  exact continuous_finset_sum _ (fun i _ => (continuous_pairRepresentation N g).matrix_elem i i)

theorem integrable_pair_word_trace (N : ℕ) (g : FreeGroup (Fin 2)) :
    Integrable (fun U : Pair N => normalizedTrace (pairMatrix N U g)) (pairMeasure N) :=
  (continuous_pair_word_trace N g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem continuous_mixed_moment (N p j : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) (j+1)) ι) :
    Continuous (fun U : Pair N => vacuumTrace ((partialEval (pairMatrix N U) f)^p)) := by
  simp only [vacuumTrace_partialEval_pow]
  apply continuous_finset_sum
  intro w hw
  split_ifs
  · exact (continuous_pair_word_trace N w.1).const_mul _
  · exact continuous_const

/-- The actual grouped path-length estimate, proved by
`HaarPrescribedDimension.onePairLengthBounds` in `HaarPrescribedBound.lean`. -/
def OnePairLengthBounds (N p : ℕ) : Prop :=
  ∀ (j : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) (j+1)) ι),
    IsSelfAdjoint (regularEval f) →
    (∀ w ∈ f.support, RadiusLe 1 w) →
    ∀ t ∈ Finset.Icc 1 p,
      ‖mixedLengthContribution (pairMeasure N) (pairMatrix N) f p t‖ ≤
        encodingMajorant p (N+1) t (p+1) (p+1) * ‖regularEval f‖^p

/-- The grouped length bounds, at the manuscript's moment range, imply the
exact one-pair hypothesis of the tensor induction. -/
theorem onePairTraceBound_of_lengthBounds {N p : ℕ} (hp : 2 ≤ p)
    (hN : 2^80*(p:ℝ)^80 ≤ N+1) (hpaths : OnePairLengthBounds N p) :
    OnePairTraceBound N p := by
  intro j ι _ _ _ f hf hlinear
  have hfirst : ∀ w ∈ f.support, FreeGroup.norm w.1 ≤ 1 := by
    intro w hw
    exact (hlinear w hw).1
  have he := integral_mixed_error_by_length (pairMeasure N) (pairMatrix N) f p hfirst
    (integrable_pair_word_trace N)
  let D : ℕ → ℝ := fun t =>
    (mixedLengthContribution (pairMeasure N) (pairMatrix N) f p t).re
  have hb := sum_encoding_errors_le hp hN
    (norm_nonneg (regularEval f)) D (fun _ => p+1) (fun _ => p+1) (by
      intro t ht
      exact (Complex.abs_re_le_norm _).trans (hpaths j ι f hf hlinear t ht))
  have hi := (continuous_mixed_moment N p j f).integrable_of_hasCompactSupport
    (μ := pairMeasure N) (HasCompactSupport.of_compactSpace _)
  have hre := congrArg Complex.re he
  rw [Complex.sub_re, Complex.re_sum] at hre
  have hir := integral_re hi
  simp only [RCLike.re_eq_complex_re] at hir
  change (∫ U : Pair N, (vacuumTrace ((partialEval (pairMatrix N U) f)^p)).re
    ∂pairMeasure N) ≤ _
  rw [hir]
  have hsum : (∫ U : Pair N, vacuumTrace ((partialEval (pairMatrix N U) f)^p)
      ∂pairMeasure N).re - (vacuumTrace (f^p)).re = ∑ t ∈ Finset.Icc 1 p, D t := hre
  have hupper := le_trans (le_abs_self (∑ t ∈ Finset.Icc 1 p, D t)) hb
  linarith

end Nonadditivity.HaarOnePairAssembly
