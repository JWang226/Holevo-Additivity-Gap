/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarCanonicalTransport
import Nonadditivity.HaarFiniteSymmetry
import Nonadditivity.StructuredHaarConsequences

/-! # The canonical prescribed-dimension expectation from one-pair moments

All tensor replacement, basis transport, Haar law regrouping, self-adjointness,
Jensen, and scalar dimension factors are proved. The sole analytic input here
is the explicit one-pair trace bound for arbitrary remaining free factors.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Nonadditivity.HaarIteratedMoments
open HaarWordExpansion HaarTensorReplacement HaarTensorConstants ProductMomentBridge
open ProductHaagerupProduct MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator BigOperators

theorem ofPolynomial_support_subset {G : Type} [Group G] [DecidableEq G]
    (P : PolynomialReduction.Polynomial G) : (ofPolynomial P).support ⊆ P.support := by
  intro g hg
  by_contra hn
  apply (Finsupp.mem_support_iff.mp hg)
  unfold ofPolynomial
  change (∑ w ∈ P.support, (Finsupp.single w (P.coefficient w) :
    G →₀ Matrix P.Index P.Index ℂ)) g = 0
  simp only [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro w hw
  have hne : w ≠ g := fun he => hn (he ▸ hw)
  simp [hne]

theorem canonicalExpectation_prescribed_le {h : ℝ} {n N : ℕ}
    (hh : (2:ℝ)/3 ≤ h) (hn : 2 ≤ n)
    (hD : N+1 = Quantitative.dimensionChoice h n)
    (hone : OnePairTraceBound N (Quantitative.momentParameter h n))
    (P : PolynomialReduction.Polynomial (Fin n → FreeGroup (Fin 2)))
    (hlinear : ∀ w ∈ P.support, ∀ r, FreeGroup.norm (w r) ≤ 1)
    (hsymm : ∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
      (ρ : (Fin n → FreeGroup (Fin 2)) →* unitary (Matrix ν ν ℂ)),
      (P.finiteEval ρ).IsHermitian) :
    (∫ ω : HaarModel.Sample 2 n N,
      ‖P.finiteEval (StructuredHaarModel.sampleRepresentation n N ω)‖
        ∂HaarModel.sampleMeasure 2 n N) ≤ ‖P.regularEval‖ *
      Real.exp (Quantitative.haarLogMultiplier h n (Real.log (2*(Fintype.card P.Index:ℝ)))) := by
  let φ := functionGroupHom (Fin 2) n
  let f := transportPolynomial φ (ofPolynomial P)
  have hs : IsSelfAdjoint (regularEval f) := by
    apply transportPolynomial_selfAdjoint
    rw [regularEval_ofPolynomial]
    exact HaarFiniteSymmetry.polynomial_regular_selfAdjoint_of_finite P hlinear hsymm
  have hl : ∀ w ∈ f.support, RadiusLe 1 w := by
    intro w hw
    have him : w ∈ (ofPolynomial P).support.image φ :=
      Finsupp.mapDomain_support hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp him
    exact radius_functionGroupHom v (hlinear v (ofPolynomial_support_subset P hv))
  have hb := iteratedExpectation_prescribed_le hh hn hD hone f hs hl
  have he := canonicalMoment_eq_iteratedMoment N 1 n (ofPolynomial P)
  simp only [pow_one, finiteEval_ofPolynomial] at he
  rw [← he] at hb
  have hnorm : ‖regularEval f‖ = ‖P.regularEval‖ := by
    rw [transportPolynomial_regular_norm φ (functionGroupHom_injective n), regularEval_ofPolynomial]
  rwa [hnorm] at hb

/-- The exact remaining expectation interface used by the finite channel
construction follows from the single one-pair moment statement. -/
theorem explicitHaarExpectation_of_onePairTraceBound {K n : ℕ}
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hone : OnePairTraceBound (StructuredHaarConsequences.sampleSize K n)
      (Quantitative.momentParameter (Real.log K) n)) :
    StructuredHaarConsequences.ExplicitHaarExpectation K n := by
  intro P hlinear hsymm
  have hKreal : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hlogK := Real.log_le_log (by norm_num : (0:ℝ)<2) hKreal
  have hh : (2:ℝ)/3 ≤ Real.log (K:ℝ) := by linarith [Real.log_two_gt_d9]
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2:ℝ) ≤ n by linarith)
  apply canonicalExpectation_prescribed_le hh hn2
    (StructuredHaarConsequences.sampleSize_add_one K n) hone P _ hsymm
  intro w hw r
  rcases hlinear w hw with rfl | ⟨x,rfl | rfl⟩
  · simp
  · simp only [ProductPolynomialReduction.generator, Pi.inv_apply, FreeGroup.norm_inv_eq,
      apply_ite FreeGroup.norm, FreeGroup.norm_of, FreeGroup.norm_one]
    split_ifs <;> omega
  · simp only [ProductPolynomialReduction.generator, Pi.inv_apply, FreeGroup.norm_inv_eq,
      apply_ite FreeGroup.norm, FreeGroup.norm_of, FreeGroup.norm_one]
    split_ifs <;> omega

end Nonadditivity.HaarIteratedMoments
