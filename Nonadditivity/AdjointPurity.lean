/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Entropy
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Concrete state expectations and the adjoint-to-purity bridge

The norm on matrices in this file is the Euclidean operator norm. The
Hilbert--Schmidt length is defined by the actual matrix trace, independently
of the operator norm instance. The state expectation bound is proved from
positive semidefiniteness and trace normalization.
-/

noncomputable section

namespace Nonadditivity.AdjointPurity

open Nonadditivity.Entropy
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Even though a product of positive matrices need not be positive,
its trace is nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hQ : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have htrace := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [Matrix.trace_mul_cycle, hQ, CFC.sqrt_mul_sqrt_self A hA.nonneg] at htrace
  exact htrace

/-- A normalized density matrix evaluates every Hermitian observable below
its operator norm. This supplies the missing input-state estimate. -/
theorem state_expectation_re_le_opNorm (ρ : DensityMatrix ι)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (ρ.matrix * A).trace.re ≤ ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  have hupper : A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (A := Matrix ι ι ℂ) hA.isSelfAdjoint
  have htrace := trace_mul_nonneg ρ.positive (Matrix.le_iff.mp hupper)
  have hscalar : (ρ.matrix * algebraMap ℝ (Matrix ι ι ℂ) ‖A‖).trace = (‖A‖ : ℂ) := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, ρ.normalized]
  have hre : 0 ≤ (ρ.matrix * (algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ - A)).trace.re :=
    (RCLike.nonneg_iff.mp htrace).1
  rw [Matrix.mul_sub, Matrix.trace_sub, hscalar, Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- The absolute state expectation estimate in the manuscript. -/
theorem abs_state_expectation_re_le_opNorm (ρ : DensityMatrix ι)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    |(ρ.matrix * A).trace.re| ≤ ‖A‖ := by
  have hu := state_expectation_re_le_opNorm ρ A hA
  have hl := state_expectation_re_le_opNorm ρ (-A) hA.neg
  simp only [Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re, norm_neg] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Hermitian state-observable trace pairings are real even when the two
matrices do not commute. -/
theorem state_expectation_im_eq_zero (ρ : DensityMatrix ι)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : (ρ.matrix * A).trace.im = 0 := by
  have hstar : star ((ρ.matrix * A).trace) = (ρ.matrix * A).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hA.eq, ρ.positive.isHermitian.eq, Matrix.trace_mul_comm]
  have him := congrArg Complex.im hstar
  change -(ρ.matrix * A).trace.im = (ρ.matrix * A).trace.im at him
  linarith

/-- Literal complex absolute-value version of the normalized state bound. -/
theorem norm_state_expectation_le_opNorm (ρ : DensityMatrix ι)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ‖(ρ.matrix * A).trace‖ ≤ ‖A‖ := by
  have hreal : (ρ.matrix * A).trace = ((ρ.matrix * A).trace.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using state_expectation_im_eq_zero ρ A hA
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_state_expectation_re_le_opNorm ρ A hA

/-- The actual Hilbert--Schmidt length computed by matrix multiplication. -/
def hsLength (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt ((A.conjTranspose * A).trace.re)

omit [DecidableEq ι] in
theorem hsLength_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hsLength A :=
  Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem trace_conjTranspose_mul_self_re_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ (A.conjTranspose * A).trace.re :=
  (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

omit [DecidableEq ι] in
theorem hsLength_sq (A : Matrix ι ι ℂ) :
    hsLength A ^ 2 = (A.conjTranspose * A).trace.re :=
  Real.sq_sqrt (trace_conjTranspose_mul_self_re_nonneg A)

omit [DecidableEq ι] in
theorem hsLength_sq_of_isHermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hsLength A ^ 2 = (A * A).trace.re := by
  rw [hsLength_sq, hA.eq]

/-- The channel's matrix-trace adjoint certificate bounds the genuine
centered Hilbert--Schmidt length. The state expectation bound is a theorem
above, rather than an assumption in this statement. -/
theorem centered_hsLength_le_of_adjoint_certificate [Nonempty ι]
    (ρ : DensityMatrix κ) (Y : DensityMatrix ι)
    (adjoint : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hhermitian : ∀ A, A.IsHermitian → (adjoint A).IsHermitian)
    (hduality : ∀ A, A.IsHermitian → A.trace = 0 →
      (Y.matrix * A).trace = (ρ.matrix * adjoint A).trace)
    (hcertificate : ∀ A, A.IsHermitian → A.trace = 0 →
      ‖adjoint A‖ ≤ t * hsLength A) : hsLength Y.centered ≤ t := by
  have hHerm := Y.centered_isHermitian
  have htrace := Y.centered_trace_zero
  have hsq : hsLength Y.centered ^ 2 ≤ t * hsLength Y.centered := by
    calc
      hsLength Y.centered ^ 2 = (Y.centered * Y.centered).trace.re :=
        hsLength_sq_of_isHermitian _ hHerm
      _ = (Y.matrix * Y.centered).trace.re := by rw [Y.centered_trace_pairing]
      _ = (ρ.matrix * adjoint Y.centered).trace.re := by rw [hduality _ hHerm htrace]
      _ ≤ ‖adjoint Y.centered‖ :=
        state_expectation_re_le_opNorm ρ _ (hhermitian _ hHerm)
      _ ≤ t * hsLength Y.centered := hcertificate _ hHerm htrace
  nlinarith [hsLength_nonneg Y.centered]

/-- Both conclusions of Lemma `purity`, from a concrete matrix-trace adjoint
relation and a genuine operator-to-Hilbert--Schmidt norm certificate. -/
theorem purity_and_entropy_of_adjoint_certificate [Nonempty ι]
    (ρ : DensityMatrix κ) (Y : DensityMatrix ι)
    (adjoint : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hhermitian : ∀ A, A.IsHermitian → (adjoint A).IsHermitian)
    (hduality : ∀ A, A.IsHermitian → A.trace = 0 →
      (Y.matrix * A).trace = (ρ.matrix * adjoint A).trace)
    (hcertificate : ∀ A, A.IsHermitian → A.trace = 0 →
      ‖adjoint A‖ ≤ t * hsLength A) :
    Y.purity ≤ 1 / (Fintype.card ι : ℝ) + t ^ 2 ∧
      Real.log (Fintype.card ι) - Real.log (1 + (Fintype.card ι : ℝ) * t ^ 2) ≤
        Y.vonNeumann := by
  have hlength := centered_hsLength_le_of_adjoint_certificate ρ Y adjoint ht
    hhermitian hduality hcertificate
  apply Y.purity_and_entropy_of_centered_bound t
  rw [← hsLength_sq_of_isHermitian _ Y.centered_isHermitian]
  exact pow_le_pow_left₀ (hsLength_nonneg Y.centered) hlength 2

/-- Instantiation for ordinary complex linear maps with the standard trace
duality. The output is supplied as an actual normalized positive density
matrix, so no hidden output-positivity premise is used. -/
theorem channel_output_purity_and_entropy [Nonempty ι]
    (channel : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (adjoint : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (ρ : DensityMatrix κ) (Y : DensityMatrix ι)
    (houtput : channel ρ.matrix = Y.matrix) {t : ℝ} (ht : 0 ≤ t)
    (hhermitian : ∀ A, A.IsHermitian → (adjoint A).IsHermitian)
    (hduality : ∀ X A, (channel X * A).trace = (X * adjoint A).trace)
    (hcertificate : ∀ A, A.IsHermitian → A.trace = 0 →
      ‖adjoint A‖ ≤ t * hsLength A) :
    Y.purity ≤ 1 / (Fintype.card ι : ℝ) + t ^ 2 ∧
      Real.log (Fintype.card ι) - Real.log (1 + (Fintype.card ι : ℝ) * t ^ 2) ≤
        Y.vonNeumann := by
  apply purity_and_entropy_of_adjoint_certificate ρ Y adjoint ht hhermitian _ hcertificate
  intro A _ _
  rw [← houtput]
  exact hduality ρ.matrix A

end Nonadditivity.AdjointPurity
