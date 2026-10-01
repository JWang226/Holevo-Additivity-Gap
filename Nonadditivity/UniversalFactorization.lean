/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.UniversalFactorizationGram
import Nonadditivity.UniversalFactorizationPolynomialDilation

/-!
The finite-set factorization holds with the same explicit coefficients for
all unitary representations on nonzero complete complex Hilbert spaces,
including infinite-dimensional spaces. The nonzero-space condition is
necessary for the additive scalar norm identity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.UniversalFactorization
open FiniteSetFactorization
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
universe u

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Nontrivial E] [Nonempty ι]

/-- The exact factor norm identity in every nonzero Hilbert-space representation. -/
theorem padded_dilation_norm_sq (π : G →* unitary (E →L[ℂ] E))
    (S : Finset G) (hS : (1 : G) ∈ S) (a : G → Matrix ι ι ℂ) :
    ‖padded π S hS (dilationCoefficient a)‖ ^ 2 =
      ‖polynomial π (Linearization.differenceSupport S) a‖ + theta S (dilationCoefficient a) := by
  rw [padded_norm_sq π S hS (dilationCoefficient a)
    (fun w _ => dilationCoefficient_inverse a w)]
  exact shifted_dilation_polynomial_norm π (Linearization.differenceSupport S)
    (fun _ hw => Linearization.inv_mem_differenceSupport hw) a _ (theta_nonneg S _)

theorem padded_dilation_norm_identity (π : G →* unitary (E →L[ℂ] E))
    (S : Finset G) (hS : (1 : G) ∈ S) (a : G → Matrix ι ι ℂ) :
    ‖polynomial π (Linearization.differenceSupport S) a‖ =
      ‖padded π S hS (dilationCoefficient a)‖ ^ 2 - theta S (dilationCoefficient a) := by
  linarith [padded_dilation_norm_sq π S hS a]

/-- The quantitative backward transfer now applies to every Hilbert-space representation. -/
theorem regular_error_transfer (π : G →* unitary (E →L[ℂ] E))
    (S : Finset G) (hS : (1 : G) ∈ S) (a : G → Matrix ι ι ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hQ : ‖padded π S hS (dilationCoefficient a)‖ ≤
      (1 + ε) * ‖RegularFactorization.padded S hS (dilationCoefficient a)‖) :
    ‖polynomial π (Linearization.differenceSupport S) a‖ ≤
      (1 + 6 * (S.card : ℝ) * ε) *
        ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) a‖ := by
  have hB : (1 : ℝ) ≤ S.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, hS⟩
  exact Linearization.backward_error_transfer _ _ _ _
    (theta S (dilationCoefficient a)) (S.card : ℝ) ε
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (theta_nonneg S _) hB hε hε1
    (padded_dilation_norm_sq π S hS a)
    (RegularFactorization.padded_dilation_norm_sq S hS a)
    (theta_dilation_le_card_mul_regularNorm S hS a) hQ

/-- A single explicit coefficient family and scalar work simultaneously for
all unitary representations, with arbitrary Hilbert dimension. -/
theorem exists_universal_factorization (S : Finset G) (hS : (1 : G) ∈ S)
    (a : G → Matrix ι ι ℂ) :
    ∃ (θ : ℝ)
      (b : Support S → Matrix (Support S × (ι ⊕ ι)) (Support S × (ι ⊕ ι)) ℂ),
      0 ≤ θ ∧ θ ≤ (S.card : ℝ) *
        ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) a‖ ∧
      ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) a‖ =
        ‖∑ g : Support S, RegularFactorization.term (b g) g.val‖ ^ 2 - θ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] (π : G →* unitary (H →L[ℂ] H)),
        ‖polynomial π (Linearization.differenceSupport S) a‖ =
          ‖∑ g : Support S, term π (b g) g.val‖ ^ 2 - θ := by
  refine ⟨theta S (dilationCoefficient a), paddedCoefficient S hS (dilationCoefficient a),
    theta_nonneg S _, theta_dilation_le_card_mul_regularNorm S hS a,
    RegularFactorization.padded_dilation_norm_identity S hS a, ?_⟩
  intro H _ _ _ _ π
  exact padded_dilation_norm_identity π S hS a

end Nonadditivity.UniversalFactorization
