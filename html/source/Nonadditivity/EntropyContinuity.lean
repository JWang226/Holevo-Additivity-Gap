/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.EntropyMixtures
import Nonadditivity.HaarMomentTail
import Nonadditivity.AdjointPurity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform continuity of finite-dimensional von Neumann entropy

The modulus depends only on the output dimension and the requested entropy
error.  It is obtained from scalar uniform continuity on `[0,1]`, diagonal
pinching, and unitary invariance, without any assumed spectral continuity
or probabilistic estimate.
-/

noncomputable section

namespace Nonadditivity.EntropyContinuity

open Nonadditivity.Entropy Nonadditivity.EntropyMixtures
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A uniform scalar modulus gives a uniform modulus for finite Shannon
entropy, including boundary distributions with zero probabilities. -/
theorem exists_shannon_modulus (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ p q : ι → ℝ,
      (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, q i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, |p i - q i| ≤ δ) → |shannon p - shannon q| ≤ η := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hu := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).uniformContinuousOn_of_continuous
    Real.continuous_negMulLog.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp hu
    (η / ((Fintype.card ι : ℝ) + 1)) (div_pos hη hd)
  refine ⟨δ, hδ, fun p q hp hq hpq => ?_⟩
  rw [shannon_eq_sum_negMulLog, shannon_eq_sum_negMulLog, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (Real.negMulLog (p i) - Real.negMulLog (q i))| ≤
        ∑ i, |Real.negMulLog (p i) - Real.negMulLog (q i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, η / ((Fintype.card ι : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact hmod (p i) (hp i) (q i) (hq i) (by simpa [Real.dist_eq] using hpq i)
    _ ≤ η := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      nlinarith

lemma diagonal_mem_Icc (ρ : DensityMatrix ι) (i : ι) :
    (ρ.matrix i i).re ∈ Set.Icc (0 : ℝ) 1 := by
  have hn (j : ι) : 0 ≤ (ρ.matrix j j).re :=
    (Complex.nonneg_iff.mp ρ.positive.diag_nonneg).1
  have hs : (∑ j, (ρ.matrix j j).re) = 1 := by
    simpa only [Matrix.trace, ← Complex.re_sum, Complex.one_re] using
      congrArg Complex.re ρ.normalized
  exact ⟨hn i, hs ▸ Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)⟩

/-- Diagonal expectations of a Hermitian matrix are bounded by its genuine
Euclidean operator norm. -/
lemma abs_diagonal_re_le_opNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    |(A i i).re| ≤ ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  have hu : A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self hA.isSelfAdjoint
  have hl : -A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖-A‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self hA.neg.isSelfAdjoint
  have hu' : 0 ≤ ((algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ - A) i i).re :=
    (Complex.nonneg_iff.mp (Matrix.le_iff.mp hu).diag_nonneg).1
  have hl' : 0 ≤ ((algebraMap ℝ (Matrix ι ι ℂ) ‖-A‖ - -A) i i).re :=
    (Complex.nonneg_iff.mp (Matrix.le_iff.mp hl).diag_nonneg).1
  simp [Algebra.algebraMap_eq_smul_one, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.neg_apply] at hu' hl'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma unitaryConjugate_sub_norm (ρ σ : DensityMatrix ι)
    (U : unitary (Matrix ι ι ℂ)) :
    ‖(ρ.unitaryConjugate U).matrix - (σ.unitaryConjugate U).matrix‖ =
      ‖ρ.matrix - σ.matrix‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  change ‖(U : Matrix ι ι ℂ) * ρ.matrix * (star U : Matrix ι ι ℂ) -
    (U : Matrix ι ι ℂ) * σ.matrix * (star U : Matrix ι ι ℂ)‖ = _
  rw [← sub_mul, ← mul_sub]
  exact (CStarRing.norm_mul_coe_unitary _ (star U)).trans
    (CStarRing.norm_coe_unitary_mul U _)

/-- Uniform continuity in Euclidean operator norm of the actual spectral
von Neumann entropy on finite density matrices. -/
theorem exists_vonNeumann_opNorm_modulus (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ρ σ : DensityMatrix ι,
      ‖ρ.matrix - σ.matrix‖ ≤ δ → |ρ.vonNeumann - σ.vonNeumann| ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := exists_shannon_modulus (ι := ι) η hη
  have hone (ρ σ : DensityMatrix ι) (hclose : ‖ρ.matrix - σ.matrix‖ ≤ δ) :
      ρ.vonNeumann ≤ σ.vonNeumann + η := by
    let U := star σ.positive.isHermitian.eigenvectorUnitary
    let τ := ρ.unitaryConjugate U
    let ω := σ.unitaryConjugate U
    have hdiag : ω.matrix = Matrix.diagonal (fun i => (σ.weights i : ℂ)) :=
      σ.positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    have hcoord (i : ι) : |(τ.matrix i i).re - (ω.matrix i i).re| ≤ δ := by
      calc
        |(τ.matrix i i).re - (ω.matrix i i).re| = |((τ.matrix - ω.matrix) i i).re| := rfl
        _ ≤ ‖τ.matrix - ω.matrix‖ := abs_diagonal_re_le_opNorm _
          (τ.positive.isHermitian.sub ω.positive.isHermitian) i
        _ = ‖ρ.matrix - σ.matrix‖ := unitaryConjugate_sub_norm ρ σ U
        _ ≤ δ := hclose
    have hs := hmod (fun i => (τ.matrix i i).re) (fun i => (ω.matrix i i).re)
      (diagonal_mem_Icc τ) (diagonal_mem_Icc ω) hcoord
    have hspec : shannon (fun i => (ω.matrix i i).re) = σ.vonNeumann := by
      simp only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re]
      rfl
    rw [hspec] at hs
    have hp := DensityMatrix.vonNeumann_le_diagonal τ
    have he : τ.vonNeumann = ρ.vonNeumann := ρ.unitaryConjugate_entropy U
    have hh := (abs_le.mp hs).2
    linarith
  refine ⟨δ, hδ, fun ρ σ hclose => abs_le.mpr ⟨?_, ?_⟩⟩
  · have hrev : ‖σ.matrix - ρ.matrix‖ ≤ δ := by
      simpa only [norm_sub_rev] using hclose
    linarith [hone σ ρ hrev]
  · linarith [hone ρ σ hclose]

/-- The same uniform modulus applies to Hilbert--Schmidt perturbations. -/
theorem exists_vonNeumann_hsLength_modulus [Nonempty ι] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ρ σ : DensityMatrix ι,
      AdjointPurity.hsLength (ρ.matrix - σ.matrix) ≤ δ →
        |ρ.vonNeumann - σ.vonNeumann| ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := exists_vonNeumann_opNorm_modulus (ι := ι) η hη
  refine ⟨δ, hδ, fun ρ σ hclose => hmod ρ σ ?_⟩
  have hHerm := ρ.positive.isHermitian.sub σ.positive.isHermitian
  have hnorm := HaarMomentTail.norm_pow_le_trace_even (ρ.matrix - σ.matrix) hHerm 1
  simp only [show 2 * 1 = 2 by omega, pow_two] at hnorm
  have hs := AdjointPurity.hsLength_sq_of_isHermitian (ρ.matrix - σ.matrix) hHerm
  have hn : ‖ρ.matrix - σ.matrix‖ ≤ AdjointPurity.hsLength (ρ.matrix - σ.matrix) := by
    nlinarith [norm_nonneg (ρ.matrix - σ.matrix),
      AdjointPurity.hsLength_nonneg (ρ.matrix - σ.matrix)]
  exact hn.trans hclose

end Nonadditivity.EntropyContinuity
