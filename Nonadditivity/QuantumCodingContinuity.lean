/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.EntropyMixtures

/-! Dimension-controlled continuity of actual spectral quantum entropy. -/
noncomputable section
namespace Nonadditivity.QuantumCodingContinuity
open Entropy EntropyMixtures
open scoped BigOperators ComplexOrder Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral calculus written with the actual eigenvector unitary. -/
def spectralMatrix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix ι ι ℂ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
      (star hA.eigenvectorUnitary : Matrix ι ι ℂ)

theorem spectralMatrix_positive {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (spectralMatrix hA f).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.PosSemidef.diagonal (fun i => by
    change (0 : ℂ) ≤ (f (hA.eigenvalues i) : ℂ)
    exact_mod_cast hf i)

theorem spectralMatrix_trace {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (spectralMatrix hA f) = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [spectralMatrix, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  simp

theorem spectralMatrix_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMatrix hA f - spectralMatrix hA g = spectralMatrix hA (fun x => f x - g x) := by
  unfold spectralMatrix
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [h]

theorem spectralMatrix_id {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    spectralMatrix hA id = A := hA.spectral_theorem.symm

def differenceHermitian (ρ σ : DensityMatrix ι) : (ρ.matrix - σ.matrix).IsHermitian :=
  ρ.positive.isHermitian.sub σ.positive.isHermitian

/-- Half the spectral trace norm of the actual difference matrix. -/
def traceDistance (ρ σ : DensityMatrix ι) : ℝ :=
  (∑ i, |(differenceHermitian ρ σ).eigenvalues i|) / 2

theorem traceDistance_nonneg (ρ σ : DensityMatrix ι) : 0 ≤ traceDistance ρ σ := by
  unfold traceDistance
  positivity

theorem difference_eigenvalues_sum (ρ σ : DensityMatrix ι) :
    ∑ i, (differenceHermitian ρ σ).eigenvalues i = 0 := by
  have h := (differenceHermitian ρ σ).trace_eq_sum_eigenvalues
  have ht : Matrix.trace (ρ.matrix - σ.matrix) = 0 := by
    rw [Matrix.trace_sub, ρ.normalized, σ.normalized, sub_self]
  rw [ht] at h
  have h' := congrArg Complex.re h
  simpa using h'.symm

theorem positive_eigenvalues_sum (ρ σ : DensityMatrix ι) :
    (∑ i, max ((differenceHermitian ρ σ).eigenvalues i) 0) = traceDistance ρ σ := by
  unfold traceDistance
  have hx (x : ℝ) : max x 0 = (|x| + x) / 2 := by
    by_cases h : 0 ≤ x
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right (le_of_not_ge h), abs_of_neg (lt_of_not_ge h)]; ring
  simp_rw [hx]
  rw [← Finset.sum_div, Finset.sum_add_distrib, difference_eigenvalues_sum, add_zero]

theorem negative_eigenvalues_sum (ρ σ : DensityMatrix ι) :
    (∑ i, max (-((differenceHermitian ρ σ).eigenvalues i)) 0) = traceDistance ρ σ := by
  unfold traceDistance
  have hx (x : ℝ) : max (-x) 0 = (|x| - x) / 2 := by
    by_cases h : 0 ≤ x
    · rw [max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge h)), abs_of_neg (lt_of_not_ge h)]; ring
  simp_rw [hx]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, difference_eigenvalues_sum, sub_zero]

def jordanPositive (ρ σ : DensityMatrix ι) : Matrix ι ι ℂ :=
  spectralMatrix (differenceHermitian ρ σ) (fun x => max x 0)

def jordanNegative (ρ σ : DensityMatrix ι) : Matrix ι ι ℂ :=
  spectralMatrix (differenceHermitian ρ σ) (fun x => max (-x) 0)

theorem jordan_difference (ρ σ : DensityMatrix ι) :
    jordanPositive ρ σ - jordanNegative ρ σ = ρ.matrix - σ.matrix := by
  unfold jordanPositive jordanNegative
  rw [spectralMatrix_sub]
  have hf : (fun x : ℝ => max x 0 - max (-x) 0) = id := by
    funext x
    change max x 0 - max (-x) 0 = x
    by_cases h : 0 ≤ x
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      ring
  rw [hf, spectralMatrix_id]

theorem jordanPositive_trace (ρ σ : DensityMatrix ι) :
    Matrix.trace (jordanPositive ρ σ) = (traceDistance ρ σ : ℂ) := by
  rw [jordanPositive, spectralMatrix_trace, positive_eigenvalues_sum]

theorem jordanNegative_trace (ρ σ : DensityMatrix ι) :
    Matrix.trace (jordanNegative ρ σ) = (traceDistance ρ σ : ℂ) := by
  rw [jordanNegative, spectralMatrix_trace, negative_eigenvalues_sum]

theorem traceDistance_zero_imp_eq (ρ σ : DensityMatrix ι) (ht : traceDistance ρ σ = 0) : ρ = σ := by
  have hs : (∑ i, |(differenceHermitian ρ σ).eigenvalues i|) = 0 := by
    unfold traceDistance at ht
    linarith
  have he (i : ι) : (differenceHermitian ρ σ).eigenvalues i = 0 := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      abs_nonneg ((differenceHermitian ρ σ).eigenvalues j)) (Finset.mem_univ i)
    rw [hs] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hD := (differenceHermitian ρ σ).spectral_theorem
  have heq : (differenceHermitian ρ σ).eigenvalues = 0 := funext he
  rw [heq] at hD
  have hz : ρ.matrix - σ.matrix = 0 := by
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using hD
  exact DensityMatrix.ext (sub_eq_zero.mp hz)

/-- The normalized positive and negative Jordan pieces are actual states. -/
def positiveJordanState (ρ σ : DensityMatrix ι) (ht : 0 < traceDistance ρ σ) : DensityMatrix ι where
  matrix := (1 / (traceDistance ρ σ : ℂ)) • jordanPositive ρ σ
  positive := (spectralMatrix_positive (differenceHermitian ρ σ) _ (fun i => le_max_right _ _)).smul
    (by exact_mod_cast (show (0 : ℝ) ≤ 1 / traceDistance ρ σ by positivity))
  normalized := by
    rw [Matrix.trace_smul, jordanPositive_trace]
    have htc : (traceDistance ρ σ : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    simp [smul_eq_mul, htc]

def negativeJordanState (ρ σ : DensityMatrix ι) (ht : 0 < traceDistance ρ σ) : DensityMatrix ι where
  matrix := (1 / (traceDistance ρ σ : ℂ)) • jordanNegative ρ σ
  positive := (spectralMatrix_positive (differenceHermitian ρ σ) _ (fun i => le_max_right _ _)).smul
    (by exact_mod_cast (show (0 : ℝ) ≤ 1 / traceDistance ρ σ by positivity))
  normalized := by
    rw [Matrix.trace_smul, jordanNegative_trace]
    have htc : (traceDistance ρ σ : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    simp [smul_eq_mul, htc]

theorem jordanState_balance (ρ σ : DensityMatrix ι) (ht : 0 < traceDistance ρ σ) :
    ρ.matrix + (traceDistance ρ σ : ℂ) • (negativeJordanState ρ σ ht).matrix =
      σ.matrix + (traceDistance ρ σ : ℂ) • (positiveJordanState ρ σ ht).matrix := by
  have htc : (traceDistance ρ σ : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [negativeJordanState, positiveJordanState, smul_smul, mul_one_div_cancel htc, one_smul]
  exact (sub_eq_sub_iff_add_eq_add.mp (jordan_difference ρ σ)).symm.trans (add_comm _ _)


/-- The two weights used in the common-mixture construction. -/
def mixWeight (t : ℝ) (b : Bool) : ℝ := if b then t / (1 + t) else 1 / (1 + t)

theorem mixWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (b : Bool) : 0 ≤ mixWeight t b := by
  cases b <;> simp only [mixWeight, Bool.false_eq_true, ↓reduceIte] <;> positivity

theorem mixWeight_sum {t : ℝ} (ht : 0 ≤ t) : (∑ b : Bool, mixWeight t b) = 1 := by
  have hd : 1 + t ≠ 0 := by linarith
  simp only [Fintype.sum_bool, mixWeight, ↓reduceIte, Bool.false_eq_true]
  field_simp
  ring

def mixingEntropy (t : ℝ) : ℝ := shannon (mixWeight t)

theorem mixingEntropy_zero : mixingEntropy 0 = 0 := by
  simp [mixingEntropy, shannon, mixWeight]

theorem mixingEntropy_le_log_two {t : ℝ} (ht : 0 ≤ t) : mixingEntropy t ≤ Real.log 2 := by
  simpa only [mixingEntropy, Fintype.card_bool, Nat.cast_ofNat] using
    shannon_le_log_card (mixWeight t) (mixWeight_nonneg ht) (mixWeight_sum ht)

/-- Entropy difference from a verified common-mixture matrix identity. -/
theorem entropy_sub_le_of_balance [Nonempty ι]
    (ρ σ P Q : DensityMatrix ι) {t : ℝ} (ht : 0 ≤ t)
    (hbalance : ρ.matrix + (t : ℂ) • Q.matrix = σ.matrix + (t : ℂ) • P.matrix) :
    ρ.vonNeumann - σ.vonNeumann ≤
      t * Real.log (Fintype.card ι) + (1 + t) * mixingEntropy t := by
  let p := mixWeight t
  let α (b : Bool) := if b then Q else ρ
  let β (b : Bool) := if b then P else σ
  let μ := DensityMatrix.mixture p (mixWeight_nonneg ht) (mixWeight_sum ht) α
  let ν := DensityMatrix.mixture p (mixWeight_nonneg ht) (mixWeight_sum ht) β
  have heq : μ = ν := by
    apply DensityMatrix.ext
    change (∑ b : Bool, (p b : ℂ) • (α b).matrix) =
      ∑ b : Bool, (p b : ℂ) • (β b).matrix
    simp only [Fintype.sum_bool, p, α, β, mixWeight, ↓reduceIte, Bool.false_eq_true,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one]
    have hb := congrArg (fun A : Matrix ι ι ℂ => (1 / (1 + (t : ℂ))) • A) hbalance
    simpa only [smul_add, smul_smul, one_div_mul_eq_div, add_comm] using hb
  have hlo := densityMatrix_mixture_entropy_concave p (mixWeight_nonneg ht)
    (mixWeight_sum ht) α
  have hup := densityMatrix_mixture_entropy_upper p (mixWeight_nonneg ht)
    (mixWeight_sum ht) β
  change (∑ b : Bool, p b * (α b).vonNeumann) ≤ μ.vonNeumann at hlo
  change ν.vonNeumann ≤ mixingEntropy t + ∑ b : Bool, p b * (β b).vonNeumann at hup
  rw [heq] at hlo
  have hc := hlo.trans hup
  simp only [Fintype.sum_bool, p, α, β, mixWeight, ↓reduceIte, Bool.false_eq_true] at hc
  have hd : 0 < 1 + t := by positivity
  have hc' := mul_le_mul_of_nonneg_left hc hd.le
  field_simp at hc'
  have hp := P.vonNeumann_le_log_dim
  have hq := Q.vonNeumann_nonneg
  have hh := mul_le_mul_of_nonneg_left hp ht
  have hq' := mul_nonneg ht hq
  nlinarith

/-- Quantitative continuity of actual quantum entropy in half spectral trace norm.
The binary mixing term is kept exact; no dimension-dependent modulus is hidden. -/
theorem vonNeumann_traceDistance_bound [Nonempty ι] (ρ σ : DensityMatrix ι) :
    |ρ.vonNeumann - σ.vonNeumann| ≤
      traceDistance ρ σ * Real.log (Fintype.card ι) +
        (1 + traceDistance ρ σ) * mixingEntropy (traceDistance ρ σ) := by
  have ht := traceDistance_nonneg ρ σ
  by_cases hz : traceDistance ρ σ = 0
  · have heq := traceDistance_zero_imp_eq ρ σ hz
    rw [heq]
    simp only [sub_self, abs_zero]
    have hz' : traceDistance σ σ = 0 := by simpa only [heq] using hz
    rw [hz', mixingEntropy_zero]
    simp
  · have hpos : 0 < traceDistance ρ σ := lt_of_le_of_ne ht (Ne.symm hz)
    have hb := jordanState_balance ρ σ hpos
    apply abs_le.mpr
    constructor
    · have h := entropy_sub_le_of_balance σ ρ (negativeJordanState ρ σ hpos)
        (positiveJordanState ρ σ hpos) ht hb.symm
      linarith
    · exact entropy_sub_le_of_balance ρ σ (positiveJordanState ρ σ hpos)
        (negativeJordanState ρ σ hpos) ht hb

/-- A convenient blocklength bound: the only dimensional term is distance times log dimension. -/
theorem vonNeumann_traceDistance_bound_log_two [Nonempty ι] (ρ σ : DensityMatrix ι) :
    |ρ.vonNeumann - σ.vonNeumann| ≤
      traceDistance ρ σ * Real.log (Fintype.card ι) +
        (1 + traceDistance ρ σ) * Real.log 2 := by
  apply (vonNeumann_traceDistance_bound ρ σ).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (mixingEntropy_le_log_two (traceDistance_nonneg ρ σ))
      (show 0 ≤ 1 + traceDistance ρ σ by linarith [traceDistance_nonneg ρ σ]))


/-- The half trace norm of a difference of normalized states is at most one. -/
theorem traceDistance_le_one (ρ σ : DensityMatrix ι) : traceDistance ρ σ ≤ 1 := by
  let V := star (differenceHermitian ρ σ).eigenvectorUnitary
  let α := ρ.unitaryConjugate V
  let β := σ.unitaryConjugate V
  have hdiag : α.matrix - β.matrix =
      Matrix.diagonal (fun i => ((differenceHermitian ρ σ).eigenvalues i : ℂ)) := by
    change (V : Matrix ι ι ℂ) * ρ.matrix * (star V : Matrix ι ι ℂ) -
      (V : Matrix ι ι ℂ) * σ.matrix * (star V : Matrix ι ι ℂ) = _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    exact (differenceHermitian ρ σ).conjStarAlgAut_star_eigenvectorUnitary
  have he (i : ι) : (α.matrix i i).re - (β.matrix i i).re =
      (differenceHermitian ρ σ).eigenvalues i := by
    have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hdiag
    simpa using h
  have hn (i : ι) : 0 ≤ (α.matrix i i).re :=
    (Complex.nonneg_iff.mp α.positive.diag_nonneg).1
  have hm (i : ι) : 0 ≤ (β.matrix i i).re :=
    (Complex.nonneg_iff.mp β.positive.diag_nonneg).1
  have hs : (∑ i, (α.matrix i i).re) = 1 := by
    simpa only [Matrix.trace, ← Complex.re_sum, Complex.one_re] using
      congrArg Complex.re α.normalized
  rw [← positive_eigenvalues_sum]
  calc
    _ ≤ ∑ i, (α.matrix i i).re := by
      apply Finset.sum_le_sum
      intro i _
      apply max_le
      · rw [← he]; exact sub_le_self _ (hm i)
      · exact hn i
    _ = 1 := hs

/-- A uniform additive constant, useful when the output dimension grows exponentially. -/
theorem vonNeumann_traceDistance_bound_uniform [Nonempty ι] (ρ σ : DensityMatrix ι) :
    |ρ.vonNeumann - σ.vonNeumann| ≤
      traceDistance ρ σ * Real.log (Fintype.card ι) + 2 * Real.log 2 := by
  apply (vonNeumann_traceDistance_bound_log_two ρ σ).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right
  · linarith [traceDistance_le_one ρ σ]
  · exact Real.log_nonneg (by norm_num)

end Nonadditivity.QuantumCodingContinuity
