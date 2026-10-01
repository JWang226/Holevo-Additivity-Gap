/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ComplementaryAdjoint
import Nonadditivity.Qualitative
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The canonical independent Haar unitary sampling model

The probability spaces and their unitary random variables are constructed
here. Strong convergence is the remaining explicit analytic proposition,
formulated for these concrete sampled block channels.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarModel

open MeasureTheory ProbabilityTheory Channels.KrausChannel BlockConstruction Entropy
open scoped Matrix Topology

/-- The finite unitary group in local dimension `N+1`. -/
abbrev LocalUnitary (N : ℕ) := unitary (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

open scoped Matrix.Norms.Elementwise in
instance localUnitaryCompact (N : ℕ) : CompactSpace (LocalUnitary N) := by
  apply isCompact_iff_compactSpace.mp
  exact Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun U hU =>
      entrywise_sup_norm_bound_of_unitary hU⟩)

open scoped Matrix.Norms.L2Operator

instance localUnitaryMeasurable (N : ℕ) : MeasurableSpace (LocalUnitary N) :=
  borel (LocalUnitary N)

instance localUnitaryBorel (N : ℕ) : BorelSpace (LocalUnitary N) := ⟨rfl⟩

/-- Normalized Haar measure on the compact complex unitary group. -/
def haar (N : ℕ) : Measure (LocalUnitary N) := Measure.haarMeasure ⊤

instance haarProbability (N : ℕ) : IsProbabilityMeasure (haar N) := by
  constructor
  exact Measure.haarMeasure_self

instance haarInvariant (N : ℕ) : Measure.IsHaarMeasure (haar N) := by
  unfold haar
  infer_instance

/-- One independent Haar unitary for every block/branch pair. -/
abbrev Sample (K n N : ℕ) := (Fin n × Fin K) → LocalUnitary N

/-- The actual joint law, the finite product of normalized Haar measures. -/
def sampleMeasure (K n N : ℕ) : Measure (Sample K n N) :=
  Measure.pi (fun _ => haar N)

instance sampleProbability (K n N : ℕ) : IsProbabilityMeasure (sampleMeasure K n N) := by
  unfold sampleMeasure
  infer_instance

/-- The coordinate random unitaries are independent under their joint law. -/
theorem independent_coordinates (K n N : ℕ) :
    iIndepFun (fun a : Fin n × Fin K => fun ω : Sample K n N => ω a)
      (sampleMeasure K n N) := by
  exact iIndepFun_pi (μ := fun _ => haar N) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)

/-- Every coordinate has exactly the normalized Haar marginal. -/
theorem coordinate_law (K n N : ℕ) (a : Fin n × Fin K) :
    (sampleMeasure K n N).map (fun ω => ω a) = haar N :=
  (measurePreserving_eval (fun _ : Fin n × Fin K => haar N) a).map_eq

/-- Extend the sampled blocks by identities beyond the fixed block length. -/
def sampleUnitary (K n N : ℕ) (ω : Sample K n N) (j : ℕ) (a : Fin K) :
    LocalUnitary N :=
  if h : j < n then ω (⟨j, h⟩, a) else 1

theorem sampleUnitary_coordinate (K n N : ℕ) (ω : Sample K n N)
    (j : Fin n) (a : Fin K) : sampleUnitary K n N ω j a = ω (j, a) := by
  simp [sampleUnitary]

theorem continuous_sampleUnitary (K n N j : ℕ) (a : Fin K) :
    Continuous (fun ω : Sample K n N => sampleUnitary K n N ω j a) := by
  unfold sampleUnitary
  split
  · exact continuous_apply _
  · exact continuous_const

/-- Every ordered tensor word is a continuous matrix polynomial of the
sampled unitary coordinates. -/
theorem continuous_tensorWord (K n N r : ℕ) (a : TensorChainIndex (Fin K) r) :
    Continuous (fun ω : Sample K n N => tensorWord (sampleUnitary K n N ω) r a) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    apply continuous_matrix
    intro i j
    change Continuous (fun ω : Sample K n N =>
      tensorWord (sampleUnitary K n N ω) r a.1 i.1 j.1 *
        (sampleUnitary K n N ω r a.2 :
          Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) i.2 j.2)
    exact ((ih a.1).matrix_elem _ _).mul
      ((continuous_subtype_val.comp (continuous_sampleUnitary K n N r a.2)).matrix_elem _ _)

variable {K : ℕ} [NeZero K]

/-- The concrete fixed-observable block adjoint is continuous. The proof
uses its checked normalized tensor-word polynomial identity. -/
theorem continuous_blockAdjoint (n N : ℕ)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    Continuous (fun ω : Sample K n N =>
      (blockChannel (sampleUnitary K n N ω) n).adjointMap A) := by
  simp_rw [blockChannel_adjoint_eq_tensor_polynomial]
  apply Continuous.const_smul
  apply continuous_finset_sum
  intro a _
  apply continuous_finset_sum
  intro b _
  exact ((continuous_tensorWord K n N n a).matrix_conjTranspose.matrix_mul
    (continuous_tensorWord K n N n b)).const_smul _

/-- The genuine operator norm, with the matrix `L2Operator` instance,
is a measurable random variable for every fixed observable. -/
theorem measurable_blockAdjoint_norm (n N : ℕ)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    Measurable (fun ω : Sample K n N =>
      ‖(blockChannel (sampleUnitary K n N ω) n).adjointMap A‖) :=
  (continuous_blockAdjoint n N A).norm.measurable

/-- In particular, the exact strong-convergence failure events are Borel. -/
theorem measurableSet_norm_deviation (n N : ℕ)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) (δ : ℝ) :
    MeasurableSet {ω : Sample K n N | δ ≤
      |‖(blockChannel (sampleUnitary K n N ω) n).adjointMap A‖ -
        FreeBridge.outputFreeNorm K n A|} := by
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp
      ((measurable_blockAdjoint_norm n N A).sub measurable_const))

/-- The remaining deep strong-convergence assertion, now stated for the
canonical independent normalized Haar model and the actual free comparison
operator. All probability, sampling and measurability data are fixed. -/
def HaarStrongConvergence (K n : ℕ) [NeZero K] : Prop :=
  ∀ A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ,
    A.IsHermitian → A.trace = 0 → AdjointPurity.hsLength A = 1 →
    ∀ δ : ℝ, 0 < δ → Filter.Tendsto
      (fun N => sampleMeasure K n N {ω | δ ≤
        |‖(blockChannel (sampleUnitary K n N ω) n).adjointMap A‖ -
          FreeBridge.outputFreeNorm K n A|})
      Filter.atTop (nhds 0)

/-- Actual finite channel realization from just the two external analytic
statements, with canonical Haar sampling and no probability-model premises. -/
theorem qualitative_realization_of_CY_and_Haar_strong_convergence
    (n : ℕ) (hK : 2 ≤ K) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hCY : FreeModel.CollinsYounBound K n) (hBC : HaarStrongConvergence K n) :
    ∃ N ω,
      (Conversion.converted (blockChannel (sampleUnitary K n N ω) n)).holevo ≤
        (n : ℝ) * Real.log (1 + 9 / (K : ℝ)) + ε ∧
      (n : ℝ) * Real.log K / (K : ℝ) ≤
        ((Conversion.converted (blockChannel (sampleUnitary K n N ω) n)).tensor
          (Conversion.converted (blockChannel (sampleUnitary K n N ω) n))).holevo ∧
      (n : ℝ) * BlockScalars.gapCoefficient K - 2 * ε ≤
        ((Conversion.converted (blockChannel (sampleUnitary K n N ω) n)).tensor
          (Conversion.converted (blockChannel (sampleUnitary K n N ω) n))).holevo -
            2 * (Conversion.converted (blockChannel (sampleUnitary K n N ω) n)).holevo := by
  exact Qualitative.qualitative_realization_of_CY_and_strong_convergence
    n hK hn hε (sampleMeasure K n) (sampleUnitary K n) Filter.atTop hCY hBC

end Nonadditivity.HaarModel
