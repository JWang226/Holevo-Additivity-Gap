/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FreeModel
import Nonadditivity.PositiveLinearization
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Coefficient energy of an actual regular-representation polynomial

Evaluation on a vector supported at the group identity isolates every
coefficient into a distinct orthogonal coordinate of the vector-valued
square-summable Hilbert space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularCoefficientEnergy

open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

abbrev VectorHilbert (G E : Type*) [NormedAddCommGroup E] := lp (fun _ : G => E) 2

section Lift

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem square_bound (T : E →L[ℂ] E) (x : E) :
    ‖T x‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖x‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 2

/-- Apply a bounded coefficient operator independently at every coordinate. -/
def liftFunction (T : E →L[ℂ] E) (f : VectorHilbert G E) : VectorHilbert G E :=
  ⟨fun g => T (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => square_bound T (f g))
      ?_
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)⟩

@[simp] theorem liftFunction_apply (T : E →L[ℂ] E) (f : VectorHilbert G E) (g : G) :
    liftFunction T f g = T (f g) := rfl

theorem liftFunction_norm_le (T : E →L[ℂ] E) (f : VectorHilbert G E) :
    ‖liftFunction T f‖ ≤ ‖T‖ * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    (∑' g, ‖T (f g)‖ ^ 2) ≤ ∑' g, ‖T‖ ^ 2 * ‖f g‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · exact fun g => square_bound T (f g)
      · simpa only [liftFunction_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
          (liftFunction T f).property.summable (by norm_num)
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)
    _ = (‖T‖ * ‖f‖) ^ 2 := by
      rw [tsum_mul_left, mul_pow]
      congr 1
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum (by norm_num) f).symm

def liftOperator (T : E →L[ℂ] E) : VectorHilbert G E →L[ℂ] VectorHilbert G E :=
  LinearMap.mkContinuous
    { toFun := liftFunction T
      map_add' := by intro f h; ext g; simp
      map_smul' := by intro c f; ext g; simp }
    ‖T‖ (liftFunction_norm_le T)

@[simp] theorem liftOperator_apply (T : E →L[ℂ] E) (f : VectorHilbert G E) (g : G) :
    liftOperator T f g = T (f g) := rfl

theorem liftOperator_single [DecidableEq G] (T : E →L[ℂ] E) (g : G) (x : E) :
    liftOperator T (lp.single 2 g x) = lp.single 2 g (T x) := by
  ext h
  by_cases hh : h = g
  · subst h
    simp
  · simp [lp.single_apply, hh]

/-- Coordinate permutations are actual Hilbert-space isometries. -/
def reindexFunction (e : G ≃ G) (f : VectorHilbert G E) : VectorHilbert G E :=
  ⟨fun g => f (e g), by
    apply memℓp_gen
    exact (e.summable_iff
      (f := fun g : G => ‖f g‖ ^ (2 : ℝ≥0∞).toReal)).mpr
      (f.property.summable (by norm_num))⟩

def reindexIsometry (e : G ≃ G) : VectorHilbert G E ≃ₗᵢ[ℂ] VectorHilbert G E where
  toFun := reindexFunction e
  invFun := reindexFunction e.symm
  left_inv := by intro f; ext g; simp [reindexFunction]
  right_inv := by intro f; ext g; simp [reindexFunction]
  map_add' := by intro f h; ext g; rfl
  map_smul' := by intro c f; ext g; rfl
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.tsum_eq (fun g => ‖f g‖ ^ (2 : ℝ≥0∞).toReal))

end Lift

section Polynomial

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

abbrev CoefficientSpace (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι
abbrev Hilbert (G ι : Type*) [Fintype ι] := VectorHilbert G (CoefficientSpace ι)

def coefficientOperator (A : Matrix ι ι ℂ) : CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A

def leftRegular (g : G) : Hilbert G ι →L[ℂ] Hilbert G ι :=
  (reindexIsometry (E := CoefficientSpace ι) (Equiv.mulLeft g⁻¹)).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq G] [DecidableEq ι] in
@[simp] theorem leftRegular_apply (g : G) (f : Hilbert G ι) (h : G) :
    leftRegular g f h = f (g⁻¹ * h) := rfl

omit [DecidableEq ι] in
theorem leftRegular_single (g h : G) (x : CoefficientSpace ι) :
    leftRegular g (lp.single 2 h x) = lp.single 2 (g * h) x := by
  ext z
  simp only [leftRegular_apply, lp.single_apply, Pi.single_apply]
  have heq : g⁻¹ * z = h ↔ z = g * h := by
    constructor
    · intro hz
      have hm := congrArg (fun t => g * t) hz
      simpa [mul_assoc] using hm
    · intro hz
      rw [hz]
      simp
  simp only [heq]

/-- The literal finite polynomial `∑ c_w ⊗ λ(w)`, realized on vector-valued ℓ². -/
def regularPolynomial (S : Finset G) (c : G → Matrix ι ι ℂ) : Hilbert G ι →L[ℂ] Hilbert G ι :=
  ∑ w ∈ S, (liftOperator (coefficientOperator (c w))).comp (leftRegular w)

/-- At the identity basis vector, different words occupy distinct coordinates. -/
theorem regularPolynomial_single_one (S : Finset G) (c : G → Matrix ι ι ℂ)
    (x : CoefficientSpace ι) :
    regularPolynomial S c (lp.single 2 (1 : G) x) =
      ∑ w ∈ S, lp.single 2 w (coefficientOperator (c w) x) := by
  simp only [regularPolynomial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    leftRegular_single, mul_one, liftOperator_single]

/-- The coefficient energy is bounded by the actual polynomial operator norm,
proved by identity-basis evaluation rather than supplied as a premise. -/
theorem coefficient_energy_le (S : Finset G) (c : G → Matrix ι ι ℂ)
    (x : CoefficientSpace ι) :
    ∑ w ∈ S, ‖coefficientOperator (c w) x‖ ^ 2 ≤
      ‖regularPolynomial S c‖ ^ 2 * ‖x‖ ^ 2 := by
  have h := (regularPolynomial S c).le_opNorm (lp.single 2 (1 : G) x)
  rw [regularPolynomial_single_one, lp.norm_single (by norm_num)] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hnorm := lp.norm_sum_single (p := 2) (by norm_num)
    (fun w => coefficientOperator (c w) x) S
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
  simpa only [hnorm, mul_pow] using hsq

/-- Matrix Gram energy in the actual positive-semidefinite matrix order. -/
theorem coefficient_gram_le (S : Finset G) (c : G → Matrix ι ι ℂ) :
    ∑ w ∈ S, (c w).conjTranspose * c w ≤
      ((‖regularPolynomial S c‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  apply Matrix.le_iff.mpr
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  change (coefficientOperator
    (((‖regularPolynomial S c‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
      ∑ w ∈ S, (c w).conjTranspose * c w)).toLinearMap.IsPositive
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hsingle (A : Matrix ι ι ℂ) :
      inner ℂ ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A.conjTranspose * A)) x) x =
        ((‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Matrix.star_eq_conjTranspose, map_mul, map_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hinner :
      inner ℂ (coefficientOperator
        (((‖regularPolynomial S c‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
          ∑ w ∈ S, (c w).conjTranspose * c w) x) x =
        (((‖regularPolynomial S c‖ ^ 2 * ‖x‖ ^ 2 -
          ∑ w ∈ S, ‖coefficientOperator (c w) x‖ ^ 2 : ℝ)) : ℂ) := by
    change inner ℂ
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (((‖regularPolynomial S c‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) -
          ∑ w ∈ S, (c w).conjTranspose * c w)) x) x = _
    simp only [coefficientOperator, map_sub, map_smul, map_one, map_sum,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      inner_sub_left, inner_smul_left, sum_inner]
    simp only [hsingle, inner_self_eq_norm_sq_to_K,
      Complex.conj_ofReal, ← Complex.ofReal_sum]
    norm_cast
    simp only [Complex.ofReal_sub, Complex.ofReal_mul]
    rfl
  rw [hinner]
  change
    (((‖regularPolynomial S c‖ ^ 2 * ‖x‖ ^ 2 -
      ∑ w ∈ S, ‖coefficientOperator (c w) x‖ ^ 2 : ℝ) : ℂ).re : ℂ) = _ ∧
      0 ≤ ((‖regularPolynomial S c‖ ^ 2 * ‖x‖ ^ 2 -
        ∑ w ∈ S, ‖coefficientOperator (c w) x‖ ^ 2 : ℝ) : ℂ).re
  simp only [Complex.ofReal_re]
  exact ⟨trivial, sub_nonneg.mpr (coefficient_energy_le S c x)⟩

/-- The modulus correction bound now has no supplied coefficient-energy premise. -/
theorem modulus_sum_norm_le_regular (S : Finset G) (c : G → Matrix ι ι ℂ) :
    ‖∑ w ∈ S, CFC.abs (c w)‖ ≤
      Real.sqrt (S.card : ℝ) * ‖regularPolynomial S c‖ := by
  apply Linearization.modulus_sum_norm_le_sqrt_card S c
    ‖regularPolynomial S c‖ (norm_nonneg _)
  intro x
  exact coefficient_energy_le S c x

/-- On a difference support `S⁻¹S`, the Appendix A correction is at most
`|S|` times the genuine regular-polynomial norm. -/
theorem differenceSupport_modulus_sum_norm_le (S : Finset G)
    (c : G → Matrix ι ι ℂ) :
    ‖∑ w ∈ Linearization.differenceSupport S, CFC.abs (c w)‖ ≤
      (S.card : ℝ) * ‖regularPolynomial (Linearization.differenceSupport S) c‖ := by
  apply (modulus_sum_norm_le_regular (Linearization.differenceSupport S) c).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨Nat.cast_nonneg _, ?_⟩
  exact_mod_cast Linearization.card_differenceSupport_le S

end Polynomial

end Nonadditivity.RegularCoefficientEnergy
