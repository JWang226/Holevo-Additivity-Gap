/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ShortEmbeddingNorm
import Nonadditivity.MatrixRegularRestriction

/-! # Logarithmic degree reduction at every matrix size

These theorems combine the proved short free-group embedding with complete
operator norm preservation for actual vector-valued regular polynomials.
Coefficient transport is literal extension by zero to the embedded support.
-/

noncomputable section

namespace Nonadditivity.MatrixShortEmbedding

open scoped BigOperators
open Nonadditivity.FreeModel Nonadditivity.ShortEmbeddingNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The logarithmic substitution preserves the genuine regular norm at every matrix size. -/
theorem logarithmicEmbedding_matrixPolynomial_norm_eq (K : ℕ) (hK : 2 ≤ K)
    (S : Finset (FreeGroup (Fin K))) (c : FreeGroup (Fin K) → Matrix ι ι ℂ) :
    ‖RegularCoefficientEnergy.regularPolynomial
      (S.image (FreeEmbedding.logarithmicEmbedding K hK))
      (Function.extend (FreeEmbedding.logarithmicEmbedding K hK) c 0)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial S c‖ :=
  MatrixRegularRestriction.matrixPolynomial_injective_norm_eq _
    (FreeEmbedding.logarithmicEmbedding_injective K hK) S c

/-- Exact matrix-level degree reduction: both support degree and norm are checked. -/
theorem matrix_logarithmic_substitution (K : ℕ) (hK : 2 ≤ K)
    (S : Finset (FreeGroup (Fin K))) (c : FreeGroup (Fin K) → Matrix ι ι ℂ)
    (d : ℕ) (hdegree : ∀ w ∈ S, FreeGroup.norm w ≤ d) :
    (∀ v ∈ S.image (FreeEmbedding.logarithmicEmbedding K hK),
      FreeGroup.norm v ≤ (2 * Nat.log 2 (K - 1) + 1) * d) ∧
    ‖RegularCoefficientEnergy.regularPolynomial
      (S.image (FreeEmbedding.logarithmicEmbedding K hK))
      (Function.extend (FreeEmbedding.logarithmicEmbedding K hK) c 0)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial S c‖ := by
  constructor
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (logarithmicEmbedding_norm_le K hK w).trans
      (Nat.mul_le_mul_left _ (hdegree w hw))
  · exact logarithmicEmbedding_matrixPolynomial_norm_eq K hK S c

/-- Tensor-product free-group substitution preserves the matrix coefficient regular norm. -/
theorem productLogarithmicEmbedding_matrixPolynomial_norm_eq (K n : ℕ) (hK : 2 ≤ K)
    (S : Finset (ProductFreeGroup K n)) (c : ProductFreeGroup K n → Matrix ι ι ℂ) :
    ‖RegularCoefficientEnergy.regularPolynomial (S.image (productLogarithmicEmbedding K n hK))
      (Function.extend (productLogarithmicEmbedding K n hK) c 0)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial S c‖ :=
  MatrixRegularRestriction.matrixPolynomial_injective_norm_eq _
    (productLogarithmicEmbedding_injective K n hK) S c

/-- The full product-group matrix substitution with degree bounded in each factor. -/
theorem product_matrix_logarithmic_substitution (K n : ℕ) (hK : 2 ≤ K)
    (S : Finset (ProductFreeGroup K n)) (c : ProductFreeGroup K n → Matrix ι ι ℂ)
    (d : ℕ) (hdegree : ∀ w ∈ S, ∀ j, FreeGroup.norm (w j) ≤ d) :
    (∀ v ∈ S.image (productLogarithmicEmbedding K n hK), ∀ j,
      FreeGroup.norm (v j) ≤ (2 * Nat.log 2 (K - 1) + 1) * d) ∧
    ‖RegularCoefficientEnergy.regularPolynomial (S.image (productLogarithmicEmbedding K n hK))
      (Function.extend (productLogarithmicEmbedding K n hK) c 0)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial S c‖ := by
  constructor
  · intro v hv j
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (logarithmicEmbedding_norm_le K hK (w j)).trans
      (Nat.mul_le_mul_left _ (hdegree w hw j))
  · exact productLogarithmicEmbedding_matrixPolynomial_norm_eq K n hK S c

/-- The same exact matrix norm theorem also respects total product-word degree. -/
theorem product_matrix_total_degree_substitution (K n : ℕ) (hK : 2 ≤ K)
    (S : Finset (ProductFreeGroup K n)) (c : ProductFreeGroup K n → Matrix ι ι ℂ)
    (d : ℕ) (hdegree : ∀ w ∈ S, (∑ j, FreeGroup.norm (w j)) ≤ d) :
    (∀ v ∈ S.image (productLogarithmicEmbedding K n hK),
      (∑ j, FreeGroup.norm (v j)) ≤ (2 * Nat.log 2 (K - 1) + 1) * d) ∧
    ‖RegularCoefficientEnergy.regularPolynomial (S.image (productLogarithmicEmbedding K n hK))
      (Function.extend (productLogarithmicEmbedding K n hK) c 0)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial S c‖ := by
  constructor
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (productLogarithmicEmbedding_total_norm_le K n hK w).trans
      (Nat.mul_le_mul_left _ (hdegree w hw))
  · exact productLogarithmicEmbedding_matrixPolynomial_norm_eq K n hK S c

end Nonadditivity.MatrixShortEmbedding
