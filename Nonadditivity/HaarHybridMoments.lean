/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarTensorReplacement
import Nonadditivity.HaarMomentExpectation

/-! # One actual tensor replacement from a one-pair trace estimate

The operator norm and vacuum trace below are evaluated after a literal matrix
substitution. Compactness supplies all Bochner-integrability obligations. The
only analytic hypothesis in the replacement estimate is the one-pair trace
moment comparison itself.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarHybridMoments
open MeasureTheory HaarWordExpansion HaarTensorReplacement ProductHaagerupProduct
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker

variable {G H ι ν : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

def termLinear (g : G) : Matrix ι ι ℂ →ₗ[ℂ]
    (RegularCoefficientEnergy.Hilbert G ι →L[ℂ] RegularCoefficientEnergy.Hilbert G ι) where
  toFun A := RegularFactorization.term A g
  map_add' := fun A B => RegularFactorization.term_add A B g
  map_smul' := by
    intro c A
    ext f h i
    change ((c • A) *ᵥ (f (g⁻¹*h)).ofLp) i = c * (A *ᵥ (f (g⁻¹*h)).ofLp) i
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

theorem continuous_term (g : G) :
    Continuous (fun A : Matrix ι ι ℂ => RegularFactorization.term A g) :=
  (termLinear g).continuous_of_finiteDimensional

variable {Ω : Type} [TopologicalSpace Ω]

theorem continuous_partial_regularEval (ρ : Ω → G →* Matrix ν ν ℂ)
    (hρ : ∀ g, Continuous (fun ω => ρ ω g)) (f : MatrixPolynomial (G × H) ι) :
    Continuous (fun ω => regularEval (partialEval (ρ ω) f)) := by
  simp only [partialEval_eq_sum, map_sum, regularEval_single]
  apply continuous_finset_sum
  intro w hw
  apply (continuous_term w.2).comp
  apply continuous_matrix
  intro a b
  exact continuous_const.mul ((hρ w.1).matrix_elem a.2 b.2)

theorem continuous_partial_vacuumMoment (ρ : Ω → G →* Matrix ν ν ℂ)
    (hρ : ∀ g, Continuous (fun ω => ρ ω g)) (f : MatrixPolynomial (G × H) ι) (p : ℕ) :
    Continuous (fun ω => (vacuumTrace ((partialEval (ρ ω) f)^p)).re) := by
  simp only [vacuumTrace_partialEval_pow]
  apply Complex.continuous_re.comp
  apply continuous_finset_sum
  intro w hw
  split_ifs with h
  · apply Continuous.const_mul
    unfold normalizedTrace Matrix.trace
    apply Continuous.div_const
    exact continuous_finset_sum _ (fun i hi => (hρ w.1).matrix_elem i i)
  · exact continuous_const

section Integrable
variable [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integrable_partial_regularNorm_pow (ρ : Ω → G →* Matrix ν ν ℂ)
    (hρ : ∀ g, Continuous (fun ω => ρ ω g)) (f : MatrixPolynomial (G × H) ι) (p : ℕ) :
    Integrable (fun ω => ‖regularEval (partialEval (ρ ω) f)‖^p) μ :=
  ((continuous_partial_regularEval ρ hρ f).norm.pow p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_partial_vacuumMoment (ρ : Ω → G →* Matrix ν ν ℂ)
    (hρ : ∀ g, Continuous (fun ω => ρ ω g)) (f : MatrixPolynomial (G × H) ι) (p : ℕ) :
    Integrable (fun ω => (vacuumTrace ((partialEval (ρ ω) f)^p)).re) μ :=
  (continuous_partial_vacuumMoment ρ hρ f p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Integrable

section Replacement
variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty ι] [Nonempty ν]
  [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A concrete one-pair trace comparison implies the next hybrid norm-moment
bound, with the actual enlarged coefficient dimension. -/
theorem replacement_norm_moment_le {j p : ℕ}
    (ρ : Ω → G →* unitary (Matrix ν ν ℂ))
    (hρ : ∀ g, Continuous (fun ω => (ρ ω g : Matrix ν ν ℂ)))
    (f : MatrixPolynomial (G × GroupIndex α j) ι)
    (hf : IsSelfAdjoint (regularEval f))
    (hlinear : ∀ w ∈ f.support, RadiusLe 1 w.2)
    (hp : Even p) (hp2 : 2 ≤ p) (ε : ℝ)
    (htrace : (∫ ω, (vacuumTrace ((partialEval (representationMatrix (ρ ω)) f)^p)).re ∂μ) ≤
      (vacuumTrace (f^p)).re + ε * ‖regularEval f‖^p) :
    (∫ ω, ‖regularEval (partialEval (representationMatrix (ρ ω)) f)‖^p ∂μ) ≤
      (2*(Fintype.card ι:ℝ)*Fintype.card ν*(p:ℝ)^(3*j)) *
        (1+ε) * ‖regularEval f‖^p := by
  let C : ℝ := 2*(Fintype.card ι:ℝ)*Fintype.card ν*(p:ℝ)^(3*j)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcont : ∀ g, Continuous (fun ω => representationMatrix (ρ ω) g) := hρ
  have hnorm := integrable_partial_regularNorm_pow μ _ hcont f p
  have hmoment := integrable_partial_vacuumMoment μ _ hcont f p
  have hpt : ∀ ω, ‖regularEval (partialEval (representationMatrix (ρ ω)) f)‖^p ≤
      C * (vacuumTrace ((partialEval (representationMatrix (ρ ω)) f)^p)).re := by
    intro ω
    have hl : ∀ w ∈ (partialEval (representationMatrix (ρ ω)) f).support,
        RadiusLe 1 w := by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (partialEval_support _ f hw)
      exact hlinear v hv
    have hb := ProductMomentBridge.norm_pow_le_two_card_moment
      (partialEval (representationMatrix (ρ ω)) f) (partialEval_selfAdjoint (ρ ω) f hf)
      hl hp hp2
    simpa only [C, Fintype.card_prod, Nat.cast_mul, mul_assoc] using hb
  have hi := integral_mono hnorm (hmoment.const_mul C) hpt
  rw [integral_const_mul] at hi
  have ht := mul_le_mul_of_nonneg_left
    (htrace.trans (add_le_add (vacuumTrace_pow_re_le f p) le_rfl)) hC
  exact hi.trans (ht.trans_eq (by dsimp [C]; ring))

end Replacement
end Nonadditivity.HaarHybridMoments
