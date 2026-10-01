/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarOperatorCurry
import Nonadditivity.HaarMixedWordExpansion

/-! # The contractive vacuum functional on mixed operator coefficients

The normalized matrix vacuum state is defined on the actual bounded operators
of the untouched factors. Applying it to a grouped operator length contribution
recovers the scalar mixed moment contribution exactly.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarVacuumFunctional
open HaarWordExpansion HaarOperatorCurry HaarMixedWordExpansion RegularCoefficientEnergy
open MeasureTheory
open scoped ENNReal BigOperators Matrix Matrix.Norms.L2Operator

variable {G H ι : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι]

def vacuumFunctional (T : Hilbert H ι →L[ℂ] Hilbert H ι) : ℂ :=
  (∑ i : ι, T (lp.single 2 (1:H) (EuclideanSpace.single i 1)) 1 i) / Fintype.card ι

theorem vacuumFunctional_coordinate_le (T : Hilbert H ι →L[ℂ] Hilbert H ι) (i : ι) :
    ‖T (lp.single 2 (1:H) (EuclideanSpace.single i 1)) 1 i‖ ≤ ‖T‖ := by
  let x : CoefficientSpace ι := EuclideanSpace.single i 1
  let e : Hilbert H ι := lp.single 2 (1:H) x
  have hx : ‖x‖ = 1 := by simp [x, EuclideanSpace.norm_single]
  have he : ‖e‖ = 1 := by
    simp [e, lp.norm_single (by norm_num : (0:ℝ≥0∞)<2), hx]
  change ‖T e 1 i‖ ≤ ‖T‖
  calc
    _ ≤ ‖T e 1‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T e‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖T‖ := by rw [he, mul_one]

theorem vacuumFunctional_norm_le [Nonempty ι] (T : Hilbert H ι →L[ℂ] Hilbert H ι) :
    ‖vacuumFunctional T‖ ≤ ‖T‖ := by
  have hc : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  unfold vacuumFunctional
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ i : ι, ‖T (lp.single 2 (1:H) (EuclideanSpace.single i 1)) 1 i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖T‖ := Finset.sum_le_sum (fun i _ => vacuumFunctional_coordinate_le T i)
    _ = _ := by simp [mul_comm]

theorem vacuumFunctional_sum {J : Type} (s : Finset J)
    (T : J → Hilbert H ι →L[ℂ] Hilbert H ι) :
    vacuumFunctional (∑ j ∈ s, T j) = ∑ j ∈ s, vacuumFunctional (T j) := by
  simp only [vacuumFunctional, ContinuousLinearMap.sum_apply, lp.coeFn_sum,
    Finset.sum_apply, WithLp.ofLp_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem vacuumFunctional_smul (c : ℂ) (T : Hilbert H ι →L[ℂ] Hilbert H ι) :
    vacuumFunctional (c • T) = c * vacuumFunctional T := by
  simp only [vacuumFunctional, ContinuousLinearMap.smul_apply, lp.coeFn_smul,
    Pi.smul_apply, WithLp.ofLp_smul, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem vacuumFunctional_regularEval (f : MatrixPolynomial H ι) :
    vacuumFunctional (regularEval f) = vacuumTrace f := by
  unfold vacuumFunctional vacuumTrace normalizedTrace Matrix.trace
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [regularEval_vacuum]
  change ((f 1) *ᵥ Pi.single i 1) i = f 1 i i
  simp

omit [DecidableEq G] in
theorem vacuumFunctional_operatorCurry_coefficient (f : MatrixPolynomial (G × H) ι) (g : G) :
    vacuumFunctional (operatorCurry f g) = normalizedTrace (f (g,1)) := by
  rw [operatorCurry_apply, vacuumFunctional_regularEval]
  rfl

omit [DecidableEq H] in
theorem identitySlice_support_subset (f : MatrixPolynomial (G × H) ι) :
    (identitySlice f).support ⊆ (MonoidAlgebra.curryRingEquiv f).support := by
  intro g hg
  by_contra hn
  have hz := Finsupp.notMem_support_iff.mp hn
  apply Finsupp.mem_support_iff.mp hg
  change MonoidAlgebra.curryRingEquiv f g 1 = 0
  rw [hz]
  rfl

section Length
variable {α Ω ν : Type} [DecidableEq α] [MeasurableSpace Ω]
  [Fintype ν] [DecidableEq ν]
  (μ : Measure Ω) (ρ : Ω → FreeGroup α →* Matrix ν ν ℂ)

def operatorLengthContribution (f : MatrixPolynomial (FreeGroup α × H) ι) (p t : ℕ) :
    Hilbert H ι →L[ℂ] Hilbert H ι :=
  ∑ g ∈ ((MonoidAlgebra.curryRingEquiv (f^p)).support.erase 1).filter
      (fun g => FreeGroup.norm g=t),
    (∫ ω, normalizedTrace (ρ ω g) ∂μ) • operatorCurry (f^p) g

/-- Trace is taken after the operator coefficients have been grouped. -/
theorem mixedLengthContribution_eq_vacuum (f : MatrixPolynomial (FreeGroup α × H) ι)
    (p t : ℕ) :
    mixedLengthContribution μ ρ f p t = vacuumFunctional (operatorLengthContribution μ ρ f p t) := by
  unfold operatorLengthContribution
  rw [vacuumFunctional_sum]
  simp only [vacuumFunctional_smul, vacuumFunctional_operatorCurry_coefficient]
  have hcomm (g : FreeGroup α) :
      (∫ ω, normalizedTrace (ρ ω g) ∂μ) * normalizedTrace ((f^p) (g,1)) =
      normalizedTrace ((f^p) (g,1)) * (∫ ω, normalizedTrace (ρ ω g) ∂μ) := mul_comm _ _
  simp_rw [hcomm]
  unfold mixedLengthContribution
  apply Finset.sum_subset
  · intro g hg
    obtain ⟨hg,ht⟩ := Finset.mem_filter.mp hg
    obtain ⟨hne,hg⟩ := Finset.mem_erase.mp hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
      ⟨hne,identitySlice_support_subset (f^p) hg⟩,ht⟩
  · intro g hg hn
    obtain ⟨hg,ht⟩ := Finset.mem_filter.mp hg
    have hne := (Finset.mem_erase.mp hg).1
    have hs : g ∉ (identitySlice (f^p)).support := by
      intro hs
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne,hs⟩,ht⟩)
    have hz := Finsupp.notMem_support_iff.mp hs
    change (f^p) (g,1) = 0 at hz
    simp [hz, normalizedTrace]

/-- A bound on the grouped operator sum controls the actual scalar trace
contribution with no coefficient-dimension loss. -/
theorem norm_mixedLengthContribution_le [Nonempty ι]
    (f : MatrixPolynomial (FreeGroup α × H) ι) (p t : ℕ) :
    ‖mixedLengthContribution μ ρ f p t‖ ≤ ‖operatorLengthContribution μ ρ f p t‖ := by
  rw [mixedLengthContribution_eq_vacuum]
  exact vacuumFunctional_norm_le _

end Length
end Nonadditivity.HaarVacuumFunctional
