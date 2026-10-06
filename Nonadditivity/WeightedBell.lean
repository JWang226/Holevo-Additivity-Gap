/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeightedBellScalar

/-! # Bell entropy for genuinely weighted random-unitary complementary channels

Nonuniform branch weights supply a strict Bell entropy margin while leaving
the output dimension unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Nonadditivity.WeightedBell

open Entropy Channels BellOutput
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

def pairedChannel (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) :
    KrausChannel (ι×ι) (ι×ι) (κ×κ) :=
  (KrausChannel.randomUnitary p hp hs U).tensor
    (KrausChannel.randomUnitary p hp hs U).conjugate

theorem pairedChannel_kraus (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) (z : κ×κ) :
    (pairedChannel p hp hs U).kraus z =
      ((Real.sqrt (p z.1)*Real.sqrt (p z.2):ℝ):ℂ) •
        (tensorUnitary (U z.1) (conjugateUnitary (U z.2)) : Matrix (ι×ι) (ι×ι) ℂ) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  change ((Real.sqrt (p z.1):ℂ)*(U z.1 : Matrix ι ι ℂ) a c)*
    star ((Real.sqrt (p z.2):ℂ)*(U z.2 : Matrix ι ι ℂ) b d) =
    ((Real.sqrt (p z.1)*Real.sqrt (p z.2):ℝ):ℂ)*
      ((U z.1 : Matrix ι ι ℂ) a c*star ((U z.2 : Matrix ι ι ℂ) b d))
  rw [star_mul]
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

/-- The literal pure-state ensemble of the weighted paired channel. -/
theorem pairedChannel_bell_matrix (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) :
    ((pairedChannel p hp hs U).output bellState).matrix =
      ∑ z : κ×κ, ((p z.1*p z.2:ℝ):ℂ) • (pairState U z).matrix := by
  simp only [KrausChannel.output_matrix,KrausChannel.map]
  apply Finset.sum_congr rfl
  intro z _
  rw [pairedChannel_kraus]
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    pairState,DensityMatrix.unitaryConjugate,Matrix.star_eq_conjTranspose]
  congr 1
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
  congr 1
  nlinarith [Real.mul_self_sqrt (hp z.1),Real.mul_self_sqrt (hp z.2)]

/-- The diagonal weighted branches coincide and merge into their squared-mass sum. -/
theorem pairedChannel_bell_eq_merged (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) :
    (pairedChannel p hp hs U).output bellState =
      DensityMatrix.mixture (WeightedBellScalar.weights p)
        (WeightedBellScalar.weights_nonneg p hp) (WeightedBellScalar.weights_sum p hs)
        (mergedStates U) := by
  apply DensityMatrix.ext
  rw [pairedChannel_bell_matrix,split_pair_sum]
  have hdiag : (∑ i : κ, ((p i*p i:ℝ):ℂ) • (bellState (ι := ι)).matrix) =
      ((∑ i, p i^2 : ℝ):ℂ) • bellState.matrix := by
    rw [← Finset.sum_smul]
    congr 1
    simp only [← Complex.ofReal_sum,pow_two]
  simp only [pairState_diagonal,hdiag,DensityMatrix.mixture_matrix,Fintype.sum_option,
    WeightedBellScalar.weights,mergedStates]

/-- Actual weighted mixed-unitary Bell entropy, including its strict nonuniform margin. -/
theorem pairedChannel_bell_entropy_le (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) :
    ((pairedChannel p hp hs U).output bellState).vonNeumann ≤
      2*Real.log (Fintype.card κ)-(∑ i, p i^2)*Real.log (Fintype.card κ) := by
  rw [pairedChannel_bell_eq_merged]
  have h := EntropyMixtures.densityMatrix_mixture_entropy_upper
    (WeightedBellScalar.weights p) (WeightedBellScalar.weights_nonneg p hp)
    (WeightedBellScalar.weights_sum p hs) (mergedStates U)
  simp_rw [mergedStates_entropy_zero] at h
  have h' : (DensityMatrix.mixture (WeightedBellScalar.weights p)
      (WeightedBellScalar.weights_nonneg p hp) (WeightedBellScalar.weights_sum p hs)
      (mergedStates U)).vonNeumann ≤ shannon (WeightedBellScalar.weights p) := by
    simpa only [mul_zero,Finset.sum_const_zero,add_zero] using h
  exact h'.trans (WeightedBellScalar.weights_shannon_le p hp hs)

/-- The weighted complementary channel obeys the same Bell bound by actual
pure-input complementary entropy equality. -/
theorem complementary_bell_entropy_le (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) :
    (((KrausChannel.randomUnitary p hp hs U).complementary.tensor
      (KrausChannel.randomUnitary p hp hs U).complementary.conjugate).output bellState).vonNeumann ≤
      2*Real.log (Fintype.card κ)-(∑ i, p i^2)*Real.log (Fintype.card κ) := by
  have hstate : (pairedChannel p hp hs U).complementary.output bellState =
      ((KrausChannel.randomUnitary p hp hs U).complementary.tensor
        (KrausChannel.randomUnitary p hp hs U).complementary.conjugate).output bellState := by
    apply DensityMatrix.ext
    rfl
  have he := (pairedChannel p hp hs U).pure_output_complementary_entropy_eq
    normalizedBellVector normalizedBellVector_normSq_sum
  rw [← bellState_eq_pureState,hstate] at he
  rw [← he]
  exact pairedChannel_bell_entropy_le p hp hs U

/-- Explicit margin over the uniform-weight Bell entropy budget. -/
theorem complementary_bell_entropy_le_with_margin
    (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1)
    (U : κ → unitary (Matrix ι ι ℂ)) :
    (((KrausChannel.randomUnitary p hp hs U).complementary.tensor
      (KrausChannel.randomUnitary p hp hs U).complementary.conjugate).output bellState).vonNeumann ≤
      2*Real.log (Fintype.card κ)-Real.log (Fintype.card κ)/(Fintype.card κ:ℝ) -
        ((∑ i, p i^2)-1/(Fintype.card κ:ℝ))*Real.log (Fintype.card κ) := by
  convert complementary_bell_entropy_le p hp hs U using 1; ring

/-- Every output of the weighted complementary channel has the prescribed
branch probabilities on its diagonal. -/
theorem complementary_output_diagonal (p : κ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (U : κ → unitary (Matrix ι ι ℂ))
    (ρ : DensityMatrix ι) (i : κ) :
    ((KrausChannel.randomUnitary p hp hs U).complementary.output ρ).matrix i i = (p i:ℂ) := by
  rw [KrausChannel.output_matrix,KrausChannel.complementary_map_entry]
  change (((Real.sqrt (p i):ℂ) • (U i : Matrix ι ι ℂ)) * ρ.matrix *
    ((Real.sqrt (p i):ℂ) • (U i : Matrix ι ι ℂ)).conjTranspose).trace = _
  have ht : ((U i : Matrix ι ι ℂ) * ρ.matrix *
      (U i : Matrix ι ι ℂ).conjTranspose).trace = 1 := by
    rw [Matrix.trace_mul_cycle,← Matrix.star_eq_conjTranspose,
      Unitary.coe_star_mul_self,Matrix.one_mul]
    exact ρ.normalized
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.trace_smul,ht,smul_eq_mul,mul_one]
  simp [← Complex.ofReal_mul,Real.mul_self_sqrt (hp i)]

end Nonadditivity.WeightedBell
