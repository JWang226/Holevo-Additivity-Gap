/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarModel
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! # Actual trace moments control operator-norm upper tails

The matrix norm throughout is the Euclidean operator norm. The moment is
the literal (unnormalized) matrix trace. These results prove the elementary
last step of the high-moment method; they do not supply the Haar high-moment
estimate, which remains the random-matrix input.
-/

noncomputable section

namespace Nonadditivity.HaarMomentTail

open MeasureTheory Filter
open scoped Matrix Matrix.Norms.L2Operator Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of any power, computed using the actual Hermitian spectral theorem. -/
theorem trace_pow_re_eq_sum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (q : ℕ) :
    (A ^ q).trace.re = ∑ i, hA.eigenvalues i ^ q := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hs : A = Unitary.conjStarAlgAut ℂ _ U D := hA.spectral_theorem
  have ht : (A ^ q).trace = (D ^ q).trace := by
    rw [hs, ← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [ht]
  simp [D, Matrix.diagonal_pow, Matrix.trace_diagonal, ← Complex.ofReal_pow]

/-- An even trace moment dominates the corresponding power of the actual
operator norm, without a dimension factor for the unnormalized trace. -/
theorem norm_pow_le_trace_even [Nonempty ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℕ) :
    ‖A‖ ^ (2 * p) ≤ (A ^ (2 * p)).trace.re := by
  classical
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  let f : ι → ℂ := fun i => (hA.eigenvalues i : ℂ)
  have hn : ‖A‖ = ‖f‖ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [StarAlgEquiv.norm_map, Matrix.l2_opNorm_diagonal]
    rfl
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖f i‖)
    Finset.univ_nonempty
  have hm : ‖f‖ = ‖f i‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ _)))
    (norm_le_pi_norm f i)
  rw [hn, hm, trace_pow_re_eq_sum A hA]
  have he : ‖f i‖ ^ (2 * p) = hA.eigenvalues i ^ (2 * p) := by
    simp only [f, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs]
  rw [he]
  exact Finset.single_le_sum (f := fun j => hA.eigenvalues j ^ (2 * p))
    (fun j _ => by dsimp; rw [pow_mul]; positivity) (Finset.mem_univ i)

/-- Pointwise trace moments are nonnegative for every Hermitian matrix. -/
theorem trace_even_nonneg (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (p : ℕ) :
    0 ≤ (A ^ (2 * p)).trace.re := by
  rw [trace_pow_re_eq_sum A hA]
  exact Finset.sum_nonneg fun i _ => by rw [pow_mul]; positivity

/-- Markov's inequality with the true matrix trace moment. The probability
law is arbitrary, so this applies in particular to the canonical Haar law. -/
theorem measure_norm_ge_le_trace_moment [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Matrix ι ι ℂ) (hX : ∀ ω, (X ω).IsHermitian)
    (hmeas : Measurable (fun ω => ‖X ω‖)) (p : ℕ) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ ‖X ω‖} ≤
      (∫⁻ ω, ENNReal.ofReal ((X ω ^ (2 * p)).trace.re) ∂μ) /
        ENNReal.ofReal t ^ (2 * p) := by
  have hsubset : {ω | t ≤ ‖X ω‖} ⊆
      {ω | ENNReal.ofReal t ^ (2 * p) ≤ ENNReal.ofReal ‖X ω‖ ^ (2 * p)} := by
    intro ω hω
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hω) _
  calc
    μ {ω | t ≤ ‖X ω‖} ≤
        μ {ω | ENNReal.ofReal t ^ (2 * p) ≤ ENNReal.ofReal ‖X ω‖ ^ (2 * p)} :=
      measure_mono hsubset
    _ ≤ (∫⁻ ω, ENNReal.ofReal ‖X ω‖ ^ (2 * p) ∂μ) /
        ENNReal.ofReal t ^ (2 * p) :=
      meas_ge_le_lintegral_div (hmeas.ennreal_ofReal.pow_const _).aemeasurable
        (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr ht)))
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ _ := by
      gcongr with ω
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_pow_le_trace_even (X ω) (hX ω) p)

/-- Normalized trace version, displaying the dimension cost in the high
moment method. This is the actual cardinality of the matrix index type. -/
theorem measure_norm_ge_le_normalized_trace_moment [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Matrix ι ι ℂ) (hX : ∀ ω, (X ω).IsHermitian)
    (hmeas : Measurable (fun ω => ‖X ω‖)) (p : ℕ) {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ ‖X ω‖} ≤
      (Fintype.card ι : ℝ≥0∞) *
        (∫⁻ ω, ENNReal.ofReal ((X ω ^ (2 * p)).trace.re / Fintype.card ι) ∂μ) /
        ENNReal.ofReal t ^ (2 * p) := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have he (ω : Ω) : ENNReal.ofReal ((X ω ^ (2 * p)).trace.re) =
      (Fintype.card ι : ℝ≥0∞) *
        ENNReal.ofReal ((X ω ^ (2 * p)).trace.re / Fintype.card ι) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hb := measure_norm_ge_le_trace_moment μ X hX hmeas p ht
  simp_rw [he] at hb
  rwa [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)] at hb

/-- A varying moment order is permitted. A proved vanishing trace-moment
ratio supplies the required one-sided operator-norm convergence. -/
theorem upper_tail_tendsto_zero_of_trace_moments
    {Ω : ℕ → Type*} {ι : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)] [∀ N, Fintype (ι N)]
    [∀ N, DecidableEq (ι N)] [∀ N, Nonempty (ι N)]
    (μ : ∀ N, Measure (Ω N)) (X : ∀ N, Ω N → Matrix (ι N) (ι N) ℂ)
    (hX : ∀ N ω, (X N ω).IsHermitian)
    (hmeas : ∀ N, Measurable (fun ω => ‖X N ω‖)) (p : ℕ → ℕ)
    {t : ℝ} (ht : 0 < t)
    (hmoment : Tendsto
      (fun N => (∫⁻ ω, ENNReal.ofReal ((X N ω ^ (2 * p N)).trace.re) ∂μ N) /
        ENNReal.ofReal t ^ (2 * p N)) atTop (nhds 0)) :
    Tendsto (fun N => μ N {ω | t ≤ ‖X N ω‖}) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmoment
    (fun _ => bot_le) (fun N => measure_norm_ge_le_trace_moment
      (μ N) (X N) (hX N) (hmeas N) (p N) ht)

/-- Canonical independent Haar specialization. All measurability and
Hermitian-preservation obligations are discharged for the actual channel
adjoint. Only the asymptotic high-trace estimate is a premise. -/
theorem canonical_upper_tail_of_trace_moments
    {K : ℕ} [NeZero K] (n : ℕ)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) (hA : A.IsHermitian)
    (p : ℕ → ℕ) {t : ℝ} (ht : 0 < t)
    (hmoment : Tendsto (fun N =>
      (∫⁻ ω, ENNReal.ofReal
        ((((BlockConstruction.blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A)
          ^ (2 * p N)).trace.re) ∂HaarModel.sampleMeasure K n N) /
          ENNReal.ofReal t ^ (2 * p N)) atTop (nhds 0)) :
    Tendsto (fun N => HaarModel.sampleMeasure K n N {ω | t ≤
      ‖(BlockConstruction.blockChannel (HaarModel.sampleUnitary K n N ω) n).adjointMap A‖})
      atTop (nhds 0) := by
  apply upper_tail_tendsto_zero_of_trace_moments
    (fun N => HaarModel.sampleMeasure K n N)
    (fun N ω => (BlockConstruction.blockChannel
      (HaarModel.sampleUnitary K n N ω) n).adjointMap A)
    (fun N ω => Channels.KrausChannel.adjointMap_isHermitian _ A hA)
    (fun N => HaarModel.measurable_blockAdjoint_norm n N A) p ht hmoment

end Nonadditivity.HaarMomentTail
