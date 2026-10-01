/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.AdjointPurity
import Nonadditivity.Channels
import Nonadditivity.Net
import Nonadditivity.QuantumHolevo
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Concrete Hilbert--Schmidt observable space and channel realizations

Observables are represented by their entries in a genuine Euclidean space,
whose norm is proved equal to the trace-defined Hilbert--Schmidt length.
The channel adjoint's output uses the Euclidean operator norm on matrices.
These distinct norms are never selected through competing matrix instances.
-/

noncomputable section

namespace Nonadditivity.FiniteRealization

open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.AdjointPurity
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators

set_option backward.isDefEq.respectTransparency false

variable {ι D η : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype η]

/-- Matrices stored as Euclidean vectors of entries, with the HS norm. -/
abbrev EntrySpace (ι : Type*) := EuclideanSpace ℂ (ι × ι)

def entriesToMatrix (x : EntrySpace ι) : Matrix ι ι ℂ := fun i j => x (i, j)

def matrixToEntries (A : Matrix ι ι ℂ) : EntrySpace ι :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem entriesToMatrix_matrixToEntries (A : Matrix ι ι ℂ) :
    entriesToMatrix (matrixToEntries A) = A := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matrixToEntries_entriesToMatrix (x : EntrySpace ι) :
    matrixToEntries (entriesToMatrix x) = x := rfl

omit [DecidableEq ι] in
/-- The Euclidean norm of the entry vector is exactly the trace HS length. -/
theorem norm_matrixToEntries_eq_hsLength (A : Matrix ι ι ℂ) :
    ‖matrixToEntries A‖ = hsLength A := by
  have htrace : (A.conjTranspose * A).trace.re = ∑ ij : ι × ι, ‖A ij.1 ij.2‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hnorm := EuclideanSpace.norm_sq_eq (matrixToEntries A)
  have hsq := hsLength_sq A
  rw [htrace] at hsq
  change ‖matrixToEntries A‖ ^ 2 = ∑ ij : ι × ι, ‖A ij.1 ij.2‖ ^ 2 at hnorm
  nlinarith [norm_nonneg (matrixToEntries A), hsLength_nonneg A]

/-- Real-linear conversion is required because Hermitian matrices form a
real vector space. -/
def entriesToMatrixLinear : EntrySpace ι →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := entriesToMatrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The concrete real subspace of traceless Hermitian HS observables. -/
def observableSubmodule (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℝ (EntrySpace ι) where
  carrier := {x | (entriesToMatrix x).IsHermitian ∧ (entriesToMatrix x).trace = 0}
  zero_mem' := by
    change (entriesToMatrix (0 : EntrySpace ι)).IsHermitian ∧
      (entriesToMatrix (0 : EntrySpace ι)).trace = 0
    change (0 : Matrix ι ι ℂ).IsHermitian ∧ (0 : Matrix ι ι ℂ).trace = 0
    simp
  add_mem' := by
    intro x y hx hy
    constructor
    · change (entriesToMatrix x + entriesToMatrix y).IsHermitian
      exact hx.1.add hy.1
    · change (entriesToMatrix x + entriesToMatrix y).trace = 0
      simp [Matrix.trace_add, hx.2, hy.2]
  smul_mem' := by
    intro r x hx
    have hsmul : entriesToMatrix (r • x) = (r : ℂ) • entriesToMatrix x := rfl
    change (entriesToMatrix (r • x)).IsHermitian ∧ (entriesToMatrix (r • x)).trace = 0
    rw [hsmul]
    constructor
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, hx.1.eq]
      simp
    · simp [Matrix.trace_smul, hx.2]

abbrev ObservableSpace (ι : Type*) [Fintype ι] [DecidableEq ι] := observableSubmodule ι

def observableMatrix (x : ObservableSpace ι) : Matrix ι ι ℂ := entriesToMatrix x.val

theorem observableMatrix_isHermitian (x : ObservableSpace ι) :
    (observableMatrix x).IsHermitian := x.property.1

theorem observableMatrix_trace_zero (x : ObservableSpace ι) :
    (observableMatrix x).trace = 0 := x.property.2

theorem observable_norm_eq_hsLength (x : ObservableSpace ι) :
    ‖x‖ = hsLength (observableMatrix x) := by
  change ‖x.val‖ = hsLength (entriesToMatrix x.val)
  simpa using norm_matrixToEntries_eq_hsLength (entriesToMatrix x.val)

/-- The channel adjoint restricted to actual HS observables, with operator
norm in its codomain. Continuity follows from the concrete finite dimension. -/
def adjointOnObservables (T : KrausChannel D ι η) :
    ObservableSpace ι →L[ℝ] Matrix D D ℂ :=
  ((T.adjointLinearMap.restrictScalars ℝ).comp
    (entriesToMatrixLinear.comp (observableSubmodule ι).subtype)).toContinuousLinearMap

@[simp] theorem adjointOnObservables_apply (T : KrausChannel D ι η)
    (x : ObservableSpace ι) :
    adjointOnObservables T x = T.adjointMap (observableMatrix x) := rfl

/-- Turn a matrix satisfying the manuscript's test conditions into an actual
element of the finite-dimensional real observable space. -/
def matrixObservable (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (htrace : A.trace = 0) :
    ObservableSpace ι :=
  ⟨matrixToEntries A, by
    change (entriesToMatrix (matrixToEntries A)).IsHermitian ∧
      (entriesToMatrix (matrixToEntries A)).trace = 0
    simpa only [entriesToMatrix_matrixToEntries] using And.intro hA htrace⟩

@[simp] theorem observableMatrix_matrixObservable (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    observableMatrix (matrixObservable A hA htrace) = A := rfl

/-- A norm certificate for the actual restricted continuous map implies
the precise matrix certificate used by the channel entropy theorem. -/
theorem matrix_certificate_of_observable_bound (T : KrausChannel D ι η) (C : ℝ)
    (hbound : ∀ x : ObservableSpace ι, ‖adjointOnObservables T x‖ ≤ C * ‖x‖) :
    ∀ A : Matrix ι ι ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ C * hsLength A := by
  intro A hA htrace
  have h := hbound (matrixObservable A hA htrace)
  simpa only [adjointOnObservables_apply, observable_norm_eq_hsLength,
    observableMatrix_matrixObservable] using h

/-- The generic finite-net theorem instantiated with concrete Kraus channels,
concrete HS observables, and the actual matrix operator norm. -/
theorem eventually_exists_kraus_certificate
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {D : ν → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    {η : ν → Type*} [∀ i, Fintype (η i)]
    (μ : (i : ν) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (T : (i : ν) → Ω i → KrausChannel (D i) ι (η i)) (l : Filter ν)
    (limitNorm : Matrix ι ι ℂ → ℝ) {κ c : ℝ} (hκ : 1 < κ) (hc : 0 < c)
    (hlimit : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 → limitNorm A ≤ c)
    (hconvergence : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      ∀ ε : ℝ, 0 < ε → Filter.Tendsto
      (fun i => μ i {ω | ε ≤ |‖(T i ω).adjointMap A‖ - limitNorm A|}) l (nhds 0)) :
    Filter.Eventually (fun i => ∃ ω, ∀ A : Matrix ι ι ℂ, A.IsHermitian → A.trace = 0 →
      ‖(T i ω).adjointMap A‖ ≤ κ * c * hsLength A) l := by
  have hcertificate := eventually_exists_kappa_norm_certificate μ
    (fun i ω => adjointOnObservables (T i ω)) l
    (fun x => limitNorm (observableMatrix x)) hκ hc
    (fun x hx => hlimit (observableMatrix x) (observableMatrix_isHermitian x)
      (observableMatrix_trace_zero x) (by rwa [← observable_norm_eq_hsLength]))
    (fun x hx ε hε => by
      simpa only [adjointOnObservables_apply] using hconvergence (observableMatrix x)
        (observableMatrix_isHermitian x) (observableMatrix_trace_zero x)
        (by rwa [← observable_norm_eq_hsLength]) ε hε)
  exact hcertificate.mono fun i ⟨ω, hω⟩ =>
    ⟨ω, matrix_certificate_of_observable_bound (T i ω) (κ * c) hω⟩

/-- The actual operator norm of the adjoint from traceless Hermitian HS
observables controls the actual channel Holevo information. -/
theorem holevo_le_of_restricted_adjoint_opNorm [Nonempty D] [Nonempty ι]
    (T : KrausChannel D ι η) {t : ℝ} (ht : 0 ≤ t)
    (hbound : ‖adjointOnObservables T‖ ≤ t) :
    T.holevo ≤ Real.log (1 + (Fintype.card ι : ℝ) * t ^ 2) := by
  apply T.holevo_le_of_adjoint_certificate ht
  apply matrix_certificate_of_observable_bound T t
  intro x
  exact ((adjointOnObservables T).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg x))

/-- Complete finite realization step: the external free bound and strong
convergence produce concrete Kraus channels satisfying uniform output
purity/entropy estimates and the actual single-use Holevo upper bound. -/
theorem eventually_exists_kraus_entropy_and_holevo [Nonempty ι]
    {ν : Type*} {Ω : ν → Type*} [∀ i, MeasurableSpace (Ω i)]
    {D : ν → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    {η : ν → Type*} [∀ i, Fintype (η i)]
    (μ : (i : ν) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (T : (i : ν) → Ω i → KrausChannel (D i) ι (η i)) (l : Filter ν)
    (limitNorm : Matrix ι ι ℂ → ℝ) {κ c : ℝ} (hκ : 1 < κ) (hc : 0 < c)
    (hlimit : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 → limitNorm A ≤ c)
    (hconvergence : ∀ A, A.IsHermitian → A.trace = 0 → hsLength A = 1 →
      ∀ ε : ℝ, 0 < ε → Filter.Tendsto
      (fun i => μ i {ω | ε ≤ |‖(T i ω).adjointMap A‖ - limitNorm A|}) l (nhds 0)) :
    Filter.Eventually (fun i => ∃ ω,
      (∀ ρ : DensityMatrix (D i),
        ((T i ω).output ρ).purity ≤ 1 / (Fintype.card ι : ℝ) + (κ * c) ^ 2 ∧
        Real.log (Fintype.card ι) - Real.log (1 + (Fintype.card ι : ℝ) * (κ * c) ^ 2) ≤
          ((T i ω).output ρ).vonNeumann) ∧
      (T i ω).holevo ≤ Real.log (1 + (Fintype.card ι : ℝ) * (κ * c) ^ 2)) l := by
  have hcertificate := eventually_exists_kraus_certificate μ T l limitNorm hκ hc
    hlimit hconvergence
  have ht : 0 ≤ κ * c := mul_nonneg (by linarith) (le_of_lt hc)
  exact hcertificate.mono fun i ⟨ω, hω⟩ => ⟨ω,
    (fun ρ => (T i ω).output_purity_and_entropy_of_certificate ht hω ρ),
    (T i ω).holevo_le_of_adjoint_certificate ht hω⟩

end Nonadditivity.FiniteRealization
