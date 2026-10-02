/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FreeEmbedding
import Nonadditivity.RegularRestriction

/-!
# Exact norm preservation for the logarithmic free-group substitution

The concrete short-word embedding is coupled to the actual regular-representation
operators. Both word-degree control and norm preservation are proved here,
including the coordinatewise embedding of product free groups.
-/

noncomputable section

namespace Nonadditivity.ShortEmbeddingNorm

open scoped BigOperators
open Nonadditivity.FreeModel Nonadditivity.RegularRestriction

/-- A uniform generator-length bound controls the length of every reduced word. -/
theorem norm_hom_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (φ : FreeGroup α →* FreeGroup β) (L : ℕ)
    (hgen : ∀ i, FreeGroup.norm (φ (FreeGroup.of i)) ≤ L) (x : FreeGroup α) :
    FreeGroup.norm (φ x) ≤ L * FreeGroup.norm x := by
  have hlist : ∀ l : List (α × Bool),
      FreeGroup.norm (FreeGroup.lift (fun i => φ (FreeGroup.of i)) (FreeGroup.mk l)) ≤
        L * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      rw [FreeGroup.lift_mk] at ih ⊢
      simp only [List.map_cons, List.prod_cons]
      have hc : FreeGroup.norm (cond c.2 (φ (FreeGroup.of c.1))
          (φ (FreeGroup.of c.1))⁻¹) ≤ L := by
        cases c.2 <;> simp [hgen c.1]
      calc
        FreeGroup.norm _ ≤ FreeGroup.norm _ + FreeGroup.norm _ :=
          FreeGroup.norm_mul_le _ _
        _ ≤ L + L * l.length := Nat.add_le_add hc ih
        _ = L * (c :: l).length := by simp [Nat.mul_add, Nat.add_comm]
  calc
    FreeGroup.norm (φ x) =
        FreeGroup.norm (FreeGroup.lift (fun i => φ (FreeGroup.of i)) (FreeGroup.mk x.toWord)) := by
      rw [FreeGroup.mk_toWord]
      exact congrArg FreeGroup.norm (FreeGroup.lift_unique φ (fun _ => rfl))
    _ ≤ L * x.toWord.length := hlist _
    _ = L * FreeGroup.norm x := rfl

/-- The sharp logarithmic generator bound extends to every word. -/
theorem logarithmicEmbedding_norm_le (K : ℕ) (hK : 2 ≤ K)
    (x : FreeGroup (Fin K)) :
    FreeGroup.norm (FreeEmbedding.logarithmicEmbedding K hK x) ≤
      (2 * Nat.log 2 (K - 1) + 1) * FreeGroup.norm x :=
  norm_hom_le _ _ (FreeEmbedding.norm_logarithmicEmbedding_of_le K hK) x

/-- The actual short-word substitution preserves the norm of every finite scalar polynomial. -/
theorem logarithmicEmbedding_regularPolynomial_norm_eq (K : ℕ) (hK : 2 ≤ K)
    {I : Type*} [Fintype I] (w : I → FreeGroup (Fin K)) (a : I → ℂ) :
    ‖regularPolynomial (fun i => FreeEmbedding.logarithmicEmbedding K hK (w i)) a‖ =
      ‖regularPolynomial w a‖ :=
  regularPolynomial_injective_norm_eq _ (FreeEmbedding.logarithmicEmbedding_injective K hK) w a

/-- Degree reduction and actual operator norm preservation in one checked statement. -/
theorem logarithmic_substitution (K : ℕ) (hK : 2 ≤ K)
    {I : Type*} [Fintype I] (w : I → FreeGroup (Fin K)) (a : I → ℂ)
    (d : ℕ) (hdegree : ∀ i, FreeGroup.norm (w i) ≤ d) :
    (∀ i, FreeGroup.norm (FreeEmbedding.logarithmicEmbedding K hK (w i)) ≤
      (2 * Nat.log 2 (K - 1) + 1) * d) ∧
    ‖regularPolynomial (fun i => FreeEmbedding.logarithmicEmbedding K hK (w i)) a‖ =
      ‖regularPolynomial w a‖ := by
  constructor
  · intro i
    exact (logarithmicEmbedding_norm_le K hK (w i)).trans
      (Nat.mul_le_mul_left _ (hdegree i))
  · exact logarithmicEmbedding_regularPolynomial_norm_eq K hK w a

/-- The short embedding in every free-group factor. -/
def productLogarithmicEmbedding (K n : ℕ) (hK : 2 ≤ K) :
    ProductFreeGroup K n →* (Fin n → FreeGroup Bool) where
  toFun x j := FreeEmbedding.logarithmicEmbedding K hK (x j)
  map_one' := by ext j; exact map_one _
  map_mul' x y := by ext j; exact map_mul _ _ _

theorem productLogarithmicEmbedding_injective (K n : ℕ) (hK : 2 ≤ K) :
    Function.Injective (productLogarithmicEmbedding K n hK) := by
  intro x y hxy
  funext j
  apply FreeEmbedding.logarithmicEmbedding_injective K hK
  exact congrFun hxy j

/-- Product-group scalar regular polynomials keep their exact norm after substitution. -/
theorem productLogarithmicEmbedding_regularPolynomial_norm_eq (K n : ℕ) (hK : 2 ≤ K)
    {I : Type*} [Fintype I] (w : I → ProductFreeGroup K n) (a : I → ℂ) :
    ‖regularPolynomial (fun i => productLogarithmicEmbedding K n hK (w i)) a‖ =
      ‖regularPolynomial w a‖ :=
  regularPolynomial_injective_norm_eq _ (productLogarithmicEmbedding_injective K n hK) w a

/-- The full product free-group short substitution, with degree in each coordinate. -/
theorem product_logarithmic_substitution (K n : ℕ) (hK : 2 ≤ K)
    {I : Type*} [Fintype I] (w : I → ProductFreeGroup K n) (a : I → ℂ)
    (d : ℕ) (hdegree : ∀ i j, FreeGroup.norm (w i j) ≤ d) :
    (∀ i j, FreeGroup.norm (productLogarithmicEmbedding K n hK (w i) j) ≤
      (2 * Nat.log 2 (K - 1) + 1) * d) ∧
    ‖regularPolynomial (fun i => productLogarithmicEmbedding K n hK (w i)) a‖ =
      ‖regularPolynomial w a‖ := by
  constructor
  · intro i j
    exact (logarithmicEmbedding_norm_le K hK (w i j)).trans
      (Nat.mul_le_mul_left _ (hdegree i j))
  · exact productLogarithmicEmbedding_regularPolynomial_norm_eq K n hK w a

/-- The total reduced-word length is controlled by the same logarithmic factor. -/
theorem productLogarithmicEmbedding_total_norm_le (K n : ℕ) (hK : 2 ≤ K)
    (x : ProductFreeGroup K n) :
    (∑ j, FreeGroup.norm (productLogarithmicEmbedding K n hK x j)) ≤
      (2 * Nat.log 2 (K - 1) + 1) * ∑ j, FreeGroup.norm (x j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => logarithmicEmbedding_norm_le K hK (x j))

/-- The actual normalized block comparison polynomial after short substitution. -/
def gammaShort {K n : ℕ} (hK : 2 ≤ K)
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    Hilbert (Fin n → FreeGroup Bool) →L[ℂ] Hilbert (Fin n → FreeGroup Bool) :=
  (1 / ((K : ℂ) ^ n)) •
    ∑ a : Branch K n, ∑ b : Branch K n,
      A a b • leftRegular (productLogarithmicEmbedding K n hK
        ((branchWord a)⁻¹ * branchWord b))

/-- The actual short substitution has exactly the original block comparison norm. -/
theorem gammaShort_norm_eq {K n : ℕ} (hK : 2 ≤ K)
    (A : Matrix (Branch K n) (Branch K n) ℂ) : ‖gammaShort hK A‖ = freeNorm A := by
  have hpoly := productLogarithmicEmbedding_regularPolynomial_norm_eq K n hK
    (fun p : Branch K n × Branch K n => (branchWord p.1)⁻¹ * branchWord p.2)
    (fun p => A p.1 p.2)
  simp only [regularPolynomial, Fintype.sum_prod_type] at hpoly
  simp only [gammaShort, freeNorm, gamma, norm_smul]
  rw [hpoly]

/-- Every block-polynomial support word has the exact logarithmic degree bound. -/
theorem gammaShort_coordinate_degree {K n : ℕ} (hK : 2 ≤ K)
    (a b : Branch K n) (j : Fin n) :
    FreeGroup.norm (productLogarithmicEmbedding K n hK
      ((branchWord a)⁻¹ * branchWord b) j) ≤ 2 * (2 * Nat.log 2 (K - 1) + 1) := by
  have hword : FreeGroup.norm (((branchWord a)⁻¹ * branchWord b : ProductFreeGroup K n) j) ≤ 2 := by
    change FreeGroup.norm ((FreeGroup.of (a j))⁻¹ * FreeGroup.of (b j)) ≤ 2
    simpa using FreeGroup.norm_mul_le (FreeGroup.of (a j))⁻¹ (FreeGroup.of (b j))
  exact (logarithmicEmbedding_norm_le K hK (((branchWord a)⁻¹ * branchWord b) j)).trans
    (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2 * Nat.log 2 (K - 1) + 1) hword)

/-- Exact norm preservation and logarithmic support degree for the block comparison model. -/
theorem block_degree_reduction {K n : ℕ} (hK : 2 ≤ K)
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    ‖gammaShort hK A‖ = freeNorm A ∧
    ∀ a b : Branch K n, ∀ j : Fin n,
      FreeGroup.norm (productLogarithmicEmbedding K n hK
        ((branchWord a)⁻¹ * branchWord b) j) ≤ 2 * (2 * Nat.log 2 (K - 1) + 1) :=
  ⟨gammaShort_norm_eq hK A, gammaShort_coordinate_degree hK⟩

end Nonadditivity.ShortEmbeddingNorm
