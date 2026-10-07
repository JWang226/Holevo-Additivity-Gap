/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularDilation
import Nonadditivity.MatrixNormReindex
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Fintype.Prod

/-!
# Positive Gram assembly over a finite difference support

Every nonidentity word contributes half a positive modulus block.  Summing
over all such words avoids a choice of inverse-orbit representatives,
including the involution case.  The resulting coefficient matrix is
independent of the unitary representation at which it is evaluated.
The literal dilation coefficients and zero-column padding give the exact
factorization norm identity for every nonempty finite matrix representation.
Its scalar correction is bounded by `|S|` times the original polynomial's
actual infinite left regular norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.FiniteSetFactorization

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

section MatrixBlocks

variable {ζ ι ν : Type*} [Fintype ζ] [DecidableEq ζ]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

/-- Select one coefficient block. -/
def selector (g : ζ) : Matrix ι (ζ × ι) ℂ := fun i p => if p = (g, i) then 1 else 0

theorem selector_mul_adjoint (g h : ζ) :
    selector (ι := ι) g * (selector h).conjTranspose =
      if g = h then (1 : Matrix ι ι ℂ) else 0 := by
  ext i j
  by_cases hgh : g = h <;> by_cases hij : i = j <;>
    simp [Matrix.mul_apply, selector, Matrix.conjTranspose_apply,
      Prod.mk.injEq, Matrix.one_apply, hgh, hij, eq_comm]

/-- Place a matrix in a specified coefficient block. -/
def place (g h : ζ) (A : Matrix ι ι ℂ) : Matrix (ζ × ι) (ζ × ι) ℂ :=
  (selector g).conjTranspose * A * selector h

theorem place_posSemidef (g : ζ) (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (place g g A).PosSemidef := hA.conjTranspose_mul_mul_same _

/-- Insert the full positive polar block at two coefficient rows. -/
def polarInsertion (g h : ζ) (c : Matrix ι ι ℂ) : Matrix (ζ × ι) (ζ × ι) ℂ :=
  let J := Matrix.fromRows (selector g) (selector h)
  J.conjTranspose *
    Matrix.fromBlocks (CFC.abs c.conjTranspose) c c.conjTranspose (CFC.abs c) * J

theorem polarInsertion_posSemidef (g h : ζ) (c : Matrix ι ι ℂ) :
    (polarInsertion g h c).PosSemidef :=
  (Linearization.modulus_block_posSemidef c).conjTranspose_mul_mul_same _

omit [Fintype ζ] in
theorem polarInsertion_eq (g h : ζ) (c : Matrix ι ι ℂ) :
    polarInsertion g h c =
      place g g (CFC.abs c.conjTranspose) + place g h c +
      place h g c.conjTranspose + place h h (CFC.abs c) := by
  simp only [polarInsertion, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
    Matrix.add_mul, place]
  abel

/-- The unitary block column used to evaluate the coefficient matrix. -/
def unitaryColumn (U : ζ → unitary (Matrix ν ν ℂ)) :
    Matrix ((ζ × ι) × ν) (ι × ν) ℂ :=
  ∑ g, (selector (ι := ι) g).conjTranspose ⊗ₖ (U g : Matrix ν ν ℂ)

theorem select_unitaryColumn (U : ζ → unitary (Matrix ν ν ℂ)) (g : ζ) :
    (selector (ι := ι) g ⊗ₖ (1 : Matrix ν ν ℂ)) * unitaryColumn U =
      (1 : Matrix ι ι ℂ) ⊗ₖ (U g : Matrix ν ν ℂ) := by
  rw [unitaryColumn, Matrix.mul_sum]
  simp only [← Matrix.mul_kronecker_mul, selector_mul_adjoint, Matrix.one_mul]
  rw [Finset.sum_eq_single g]
  · simp
  · intro h hh hne
    simp [Ne.symm hne]
  · simp

/-- Literal evaluation of a block coefficient matrix. -/
def evaluate (U : ζ → unitary (Matrix ν ν ℂ))
    (G : Matrix (ζ × ι) (ζ × ι) ℂ) : Matrix (ι × ν) (ι × ν) ℂ :=
  (unitaryColumn U).conjTranspose * (G ⊗ₖ (1 : Matrix ν ν ℂ)) * unitaryColumn U

theorem evaluate_add (U : ζ → unitary (Matrix ν ν ℂ))
    (A B : Matrix (ζ × ι) (ζ × ι) ℂ) :
    evaluate U (A + B) = evaluate U A + evaluate U B := by
  simp [evaluate, Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

theorem evaluate_smul (U : ζ → unitary (Matrix ν ν ℂ)) (r : ℝ)
    (A : Matrix (ζ × ι) (ζ × ι) ℂ) :
    evaluate U (r • A) = r • evaluate U A := by
  simp [evaluate, Matrix.smul_kronecker]

theorem evaluate_sum {κ : Type*} (U : ζ → unitary (Matrix ν ν ℂ)) (s : Finset κ)
    (A : κ → Matrix (ζ × ι) (ζ × ι) ℂ) :
    evaluate U (∑ k ∈ s, A k) = ∑ k ∈ s, evaluate U (A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evaluate]
  | insert k s hk ih => simp [hk, evaluate_add, ih]

theorem evaluate_place (U : ζ → unitary (Matrix ν ν ℂ))
    (g h : ζ) (A : Matrix ι ι ℂ) :
    evaluate U (place g h A) =
      A ⊗ₖ ((U g : Matrix ν ν ℂ).conjTranspose * (U h : Matrix ν ν ℂ)) := by
  have hk : place g h A ⊗ₖ (1 : Matrix ν ν ℂ) =
      (selector (ι := ι) g ⊗ₖ (1 : Matrix ν ν ℂ)).conjTranspose *
      (A ⊗ₖ (1 : Matrix ν ν ℂ)) *
      (selector (ι := ι) h ⊗ₖ (1 : Matrix ν ν ℂ)) := by
    simp only [place, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have heq : evaluate U (place g h A) =
      ((selector (ι := ι) g ⊗ₖ (1 : Matrix ν ν ℂ)) * unitaryColumn U).conjTranspose *
      (A ⊗ₖ (1 : Matrix ν ν ℂ)) *
      ((selector (ι := ι) h ⊗ₖ (1 : Matrix ν ν ℂ)) * unitaryColumn U) := by
    rw [evaluate, hk]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq, select_unitaryColumn, select_unitaryColumn]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem evaluate_polarInsertion (U : ζ → unitary (Matrix ν ν ℂ))
    (g h : ζ) (c : Matrix ι ι ℂ) :
    evaluate U (polarInsertion g h c) =
      CFC.abs c.conjTranspose ⊗ₖ (1 : Matrix ν ν ℂ) +
      c ⊗ₖ ((U g : Matrix ν ν ℂ).conjTranspose * (U h : Matrix ν ν ℂ)) +
      c.conjTranspose ⊗ₖ ((U h : Matrix ν ν ℂ).conjTranspose * (U g : Matrix ν ν ℂ)) +
      CFC.abs c ⊗ₖ (1 : Matrix ν ν ℂ) := by
  rw [polarInsertion_eq]
  simp only [evaluate_add, evaluate_place]
  simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self]

end MatrixBlocks

section FiniteSupport

variable {G ι ν : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

abbrev Support (S : Finset G) := {g : G // g ∈ S}
abbrev NonidentityWords (S : Finset G) :=
  {w : G // w ∈ (Linearization.differenceSupport S).erase 1}

private theorem exists_pair (S : Finset G) (w : NonidentityWords S) :
    ∃ p : Support S × Support S, p.1.val⁻¹ * p.2.val = w.val := by
  obtain ⟨g, hg, h, hh, heq⟩ :=
    Linearization.mem_differenceSupport.mp (Finset.mem_erase.mp w.property).2
  exact ⟨(⟨g, hg⟩, ⟨h, hh⟩), heq⟩

/-- A genuine representing pair `g,h ∈ S` for each difference word. -/
def representative (S : Finset G) (w : NonidentityWords S) : Support S × Support S :=
  Classical.choose (exists_pair S w)

theorem representative_spec (S : Finset G) (w : NonidentityWords S) :
    (representative S w).1.val⁻¹ * (representative S w).2.val = w.val :=
  Classical.choose_spec (exists_pair S w)

def inverseWords (S : Finset G) : NonidentityWords S ≃ NonidentityWords S where
  toFun w := ⟨w.val⁻¹, Finset.mem_erase.mpr ⟨by
      have hw := (Finset.mem_erase.mp w.property).1
      simpa using hw,
    Linearization.inv_mem_differenceSupport (Finset.mem_erase.mp w.property).2⟩⟩
  invFun w := ⟨w.val⁻¹, Finset.mem_erase.mpr ⟨by
      have hw := (Finset.mem_erase.mp w.property).1
      simpa using hw,
    Linearization.inv_mem_differenceSupport (Finset.mem_erase.mp w.property).2⟩⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

/-- All nonidentity words contribute half of the positive polar block. -/
def nonconstantGram (S : Finset G) (c : G → Matrix ι ι ℂ) :
    Matrix (Support S × ι) (Support S × ι) ℂ :=
  ∑ w : NonidentityWords S, (1 / 2 : ℝ) •
    polarInsertion (representative S w).1 (representative S w).2 (c w.val)

theorem nonconstantGram_posSemidef (S : Finset G) (c : G → Matrix ι ι ℂ) :
    (nonconstantGram S c).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro w hw
  exact (polarInsertion_posSemidef _ _ _).smul (by norm_num : 0 ≤ (1 / 2 : ℝ))

/-- The exact constant contribution from the nonidentity moduli. -/
def diagonalCorrection (S : Finset G) (c : G → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ w : NonidentityWords S, CFC.abs (c w.val)

theorem diagonalCorrection_posSemidef (S : Finset G) (c : G → Matrix ι ι ℂ) :
    (diagonalCorrection S c).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro w hw
  exact Matrix.LE.le.posSemidef (CFC.abs_nonneg _)

/-- A finite-dimensional unitary representation restricted to the support. -/
def restrictedRepresentation (S : Finset G) (π : G →* unitary (Matrix ν ν ℂ)) :
    Support S → unitary (Matrix ν ν ℂ) := fun g => π g.val

omit [DecidableEq G] in
theorem representation_difference (π : G →* unitary (Matrix ν ν ℂ)) (g h : G) :
    (π g : Matrix ν ν ℂ).conjTranspose * (π h : Matrix ν ν ℂ) =
      (π (g⁻¹ * h) : Matrix ν ν ℂ) := by
  rw [map_mul, map_inv]
  rfl

theorem evaluate_representative_polar (S : Finset G) (c : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) (w : NonidentityWords S) :
    evaluate (restrictedRepresentation S π)
        (polarInsertion (representative S w).1 (representative S w).2 (c w.val)) =
      CFC.abs (c w.val).conjTranspose ⊗ₖ (1 : Matrix ν ν ℂ) +
      c w.val ⊗ₖ (π w.val : Matrix ν ν ℂ) +
      (c w.val).conjTranspose ⊗ₖ (π w.val⁻¹ : Matrix ν ν ℂ) +
      CFC.abs (c w.val) ⊗ₖ (1 : Matrix ν ν ℂ) := by
  rw [evaluate_polarInsertion]
  unfold restrictedRepresentation
  rw [representation_difference, representation_difference, representative_spec]
  have hinv : (representative S w).2.val⁻¹ * (representative S w).1.val = w.val⁻¹ := by
    rw [← representative_spec S w]
    simp
  rw [hinv]

private theorem inverse_modulus_sum (S : Finset G) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    (∑ w : NonidentityWords S, CFC.abs (c w.val).conjTranspose) = diagonalCorrection S c := by
  unfold diagonalCorrection
  apply Fintype.sum_equiv (inverseWords S)
  intro w
  rw [← hstar w.val (Finset.mem_erase.mp w.property).2]
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem inverse_polynomial_sum (S : Finset G) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    (∑ w : NonidentityWords S,
      (c w.val).conjTranspose ⊗ₖ (π w.val⁻¹ : Matrix ν ν ℂ)) =
      ∑ w : NonidentityWords S, c w.val ⊗ₖ (π w.val : Matrix ν ν ℂ) := by
  apply Fintype.sum_equiv (inverseWords S)
  intro w
  rw [← hstar w.val (Finset.mem_erase.mp w.property).2]
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype ν] in
private theorem sum_kronecker_one {κ : Type*} [Fintype κ]
    (A : κ → Matrix ι ι ℂ) :
    (∑ k, A k ⊗ₖ (1 : Matrix ν ν ℂ)) = (∑ k, A k) ⊗ₖ (1 : Matrix ν ν ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- Evaluation of the sum of half-blocks is exactly the nonconstant
polynomial plus its sum of coefficient moduli. -/
theorem evaluate_nonconstantGram (S : Finset G) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    evaluate (restrictedRepresentation S π) (nonconstantGram S c) =
      (∑ w : NonidentityWords S, c w.val ⊗ₖ (π w.val : Matrix ν ν ℂ)) +
      diagonalCorrection S c ⊗ₖ (1 : Matrix ν ν ℂ) := by
  unfold nonconstantGram
  rw [evaluate_sum]
  simp only [evaluate_smul, evaluate_representative_polar]
  rw [← Finset.smul_sum]
  simp only [Finset.sum_add_distrib]
  rw [sum_kronecker_one, inverse_modulus_sum S c hstar,
    inverse_polynomial_sum S c hstar π, sum_kronecker_one]
  change (1 / 2 : ℝ) •
    (diagonalCorrection S c ⊗ₖ (1 : Matrix ν ν ℂ) +
      (∑ w : NonidentityWords S, c w.val ⊗ₖ (π w.val : Matrix ν ν ℂ)) +
      (∑ w : NonidentityWords S, c w.val ⊗ₖ (π w.val : Matrix ν ν ℂ)) +
      diagonalCorrection S c ⊗ₖ (1 : Matrix ν ν ℂ)) = _
  module

private theorem one_mem_differenceSupport (S : Finset G) (hS : (1 : G) ∈ S) :
    (1 : G) ∈ Linearization.differenceSupport S :=
  Linearization.mem_differenceSupport.mpr ⟨1, hS, 1, hS, by simp⟩

private theorem sum_words_eq {A : Type*} [AddCommMonoid A] (S : Finset G) (f : G → A) :
    (∑ w : NonidentityWords S, f w.val) =
      ∑ w ∈ (Linearization.differenceSupport S).erase 1, f w :=
  (Finset.sum_subtype (p := fun w => w ∈ (Linearization.differenceSupport S).erase 1)
    ((Linearization.differenceSupport S).erase 1) (fun _ => Iff.rfl) f).symm

/-- The literal matrix polynomial on `S⁻¹S`. -/
def polynomial (S : Finset G) (c : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) : Matrix (ι × ν) (ι × ν) ℂ :=
  ∑ w ∈ Linearization.differenceSupport S, c w ⊗ₖ (π w : Matrix ν ν ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem polynomial_decompose (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ) (π : G →* unitary (Matrix ν ν ℂ)) :
    polynomial S c π =
      (∑ w : NonidentityWords S, c w.val ⊗ₖ (π w.val : Matrix ν ν ℂ)) +
      c 1 ⊗ₖ (1 : Matrix ν ν ℂ) := by
  have h := Finset.sum_erase_add (Linearization.differenceSupport S)
    (fun w => c w ⊗ₖ (π w : Matrix ν ν ℂ)) (one_mem_differenceSupport S hS)
  rw [sum_words_eq S (fun w => c w ⊗ₖ (π w : Matrix ν ν ℂ))]
  simpa only [polynomial,
    map_one, Submonoid.coe_one] using h.symm

/-- The additive scalar is chosen from the actual coefficient moduli. -/
def theta (S : Finset G) (c : G → Matrix ι ι ℂ) : ℝ :=
  ‖diagonalCorrection S c + CFC.abs (c 1)‖

theorem theta_nonneg (S : Finset G) (c : G → Matrix ι ι ℂ) : 0 ≤ theta S c := norm_nonneg _

def constantCorrection (S : Finset G) (c : G → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  algebraMap ℝ (Matrix ι ι ℂ) (theta S c) + c 1 - diagonalCorrection S c

theorem constantCorrection_posSemidef (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    (constantCorrection S c).PosSemidef := by
  apply Linearization.constant_correction_posSemidef
    (diagonalCorrection S c) (c 1) (diagonalCorrection_posSemidef S c)
  simpa only [inv_one] using (hstar 1 (one_mem_differenceSupport S hS)).symm

/-- The positive coefficient matrix with the exact constant correction. -/
def gramMatrix (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Matrix (Support S × ι) (Support S × ι) ℂ :=
  nonconstantGram S c + place (⟨1, hS⟩ : Support S) ⟨1, hS⟩ (constantCorrection S c)

theorem gramMatrix_posSemidef (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    (gramMatrix S hS c).PosSemidef :=
  (nonconstantGram_posSemidef S c).add
    (place_posSemidef _ _ (constantCorrection_posSemidef S hS c hstar))

private theorem algebraMap_kronecker_one (r : ℝ) :
    algebraMap ℝ (Matrix ι ι ℂ) r ⊗ₖ (1 : Matrix ν ν ℂ) =
      algebraMap ℝ (Matrix (ι × ν) (ι × ν) ℂ) r := by
  simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker]

/-- The full Gram evaluation identity, proved from the assembled coefficients. -/
theorem evaluate_gramMatrix (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    evaluate (restrictedRepresentation S π) (gramMatrix S hS c) =
      polynomial S c π + algebraMap ℝ (Matrix (ι × ν) (ι × ν) ℂ) (theta S c) := by
  rw [gramMatrix, evaluate_add, evaluate_nonconstantGram S c hstar π, evaluate_place]
  have hunit :
      ((restrictedRepresentation S π) (⟨1, hS⟩ : Support S) : Matrix ν ν ℂ).conjTranspose *
      ((restrictedRepresentation S π) (⟨1, hS⟩ : Support S) : Matrix ν ν ℂ) = 1 := by
    simp [restrictedRepresentation]
  rw [hunit, add_assoc, ← Matrix.add_kronecker]
  have hcor : diagonalCorrection S c + constantCorrection S c =
      c 1 + algebraMap ℝ (Matrix ι ι ℂ) (theta S c) := by
    unfold constantCorrection
    abel
  rw [hcor, Matrix.add_kronecker, algebraMap_kronecker_one,
    polynomial_decompose S hS c π]
  abel

theorem theta_eq_modulus_sum_norm (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ) :
    theta S c = ‖∑ w ∈ Linearization.differenceSupport S, CFC.abs (c w)‖ := by
  unfold theta diagonalCorrection
  congr 1
  rw [sum_words_eq S (fun w => CFC.abs (c w))]
  exact Finset.sum_erase_add _ _ (one_mem_differenceSupport S hS)

/-- The scalar bound uses the actual infinite left regular polynomial. -/
theorem theta_le_card_mul_regularNorm (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ) :
    theta S c ≤ (S.card : ℝ) *
      ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) c‖ := by
  rw [theta_eq_modulus_sum_norm S hS]
  exact RegularCoefficientEnergy.differenceSupport_modulus_sum_norm_le S c

/-- Genuine square-root coefficients, independent of the representation. -/
def factorCoefficient (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : Support S) : Matrix (Support S × ι) ι ℂ :=
  CFC.sqrt (gramMatrix S hS c) * (selector g).conjTranspose

/-- The actual evaluated factor polynomial. -/
def factorPolynomial (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    Matrix ((Support S × ι) × ν) (ι × ν) ℂ :=
  ∑ g : Support S, factorCoefficient S hS c g ⊗ₖ (π g.val : Matrix ν ν ℂ)

theorem factorPolynomial_eq (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ) (π : G →* unitary (Matrix ν ν ℂ)) :
    factorPolynomial S hS c π =
      (CFC.sqrt (gramMatrix S hS c) ⊗ₖ (1 : Matrix ν ν ℂ)) *
        unitaryColumn (restrictedRepresentation S π) := by
  unfold factorPolynomial factorCoefficient unitaryColumn restrictedRepresentation
  rw [Matrix.mul_sum]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Universal finite-dimensional Gram factorization of the literal polynomial.
The Gram identity is a conclusion, rather than a supplied assumption. -/
theorem factorPolynomial_gram (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    (factorPolynomial S hS c π).conjTranspose * factorPolynomial S hS c π =
      polynomial S c π + algebraMap ℝ (Matrix (ι × ν) (ι × ν) ℂ) (theta S c) := by
  have hG := gramMatrix_posSemidef S hS c hstar
  have hR := Linearization.positive_sqrt_gram (gramMatrix S hS c) hG
  rw [factorPolynomial_eq, Linearization.gram_factorization]
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, hR]
  exact evaluate_gramMatrix S hS c hstar π

/-- The unconditional squared norm resulting from this Gram construction. -/
theorem factorPolynomial_norm_sq (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    ‖factorPolynomial S hS c π‖ ^ 2 =
      ‖polynomial S c π + algebraMap ℝ (Matrix (ι × ν) (ι × ν) ℂ) (theta S c)‖ := by
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    factorPolynomial_gram S hS c hstar π]

/-- The square coefficient matrices in the manuscript; the identity support
block supplies the zero-column padding of the rectangular factor. -/
def paddedCoefficient (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : Support S) : Matrix (Support S × ι) (Support S × ι) ℂ :=
  factorCoefficient S hS c g * selector (⟨1, hS⟩ : Support S)

def paddedPolynomial (S : Finset G) (hS : (1 : G) ∈ S) (c : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    Matrix ((Support S × ι) × ν) ((Support S × ι) × ν) ℂ :=
  ∑ g : Support S, paddedCoefficient S hS c g ⊗ₖ (π g.val : Matrix ν ν ℂ)

theorem paddedPolynomial_eq (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ) (π : G →* unitary (Matrix ν ν ℂ)) :
    paddedPolynomial S hS c π = factorPolynomial S hS c π *
      (selector (⟨1, hS⟩ : Support S) ⊗ₖ (1 : Matrix ν ν ℂ)) := by
  unfold paddedPolynomial paddedCoefficient factorPolynomial
  rw [Matrix.sum_mul]
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem paddedPolynomial_norm (S : Finset G) (hS : (1 : G) ∈ S)
    (c : G → Matrix ι ι ℂ) (π : G →* unitary (Matrix ν ν ℂ)) :
    ‖paddedPolynomial S hS c π‖ = ‖factorPolynomial S hS c π‖ := by
  rw [paddedPolynomial_eq]
  apply Linearization.right_isometry_mul_norm
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, selector_mul_adjoint, ite_true, Matrix.one_mul,
    Matrix.one_kronecker_one]

end FiniteSupport

section Dilation

variable {G ι ν : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

omit [Group G] [DecidableEq G] [DecidableEq ι] in
/-- The square coefficients have the exact manuscript dimension `2*m*B`. -/
theorem coefficient_dimension (S : Finset G) :
    Fintype.card (Support S × (ι ⊕ ι)) = 2 * Fintype.card ι * S.card := by
  have hcard : Fintype.card (Support S) = S.card :=
    Fintype.card_of_subtype S (fun _ => Iff.rfl)
  rw [Fintype.card_prod, Fintype.card_sum, hcard]
  ring

/-- Actual Hermitian dilation coefficients of an arbitrary polynomial. -/
def dilationCoefficient (a : G → Matrix ι ι ℂ) (w : G) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 (a w) (a w⁻¹).conjTranspose 0

omit [DecidableEq G] [Fintype ι] [DecidableEq ι] in
theorem dilationCoefficient_inverse (a : G → Matrix ι ι ℂ) (w : G) :
    dilationCoefficient a w⁻¹ = (dilationCoefficient a w).conjTranspose := by
  simp [dilationCoefficient, Matrix.fromBlocks_conjTranspose]

private theorem inverse_support_sum {A : Type*} [AddCommMonoid A]
    (S : Finset G) (f : G → A) :
    (∑ w ∈ Linearization.differenceSupport S, f w⁻¹) =
      ∑ w ∈ Linearization.differenceSupport S, f w := by
  apply Finset.sum_bij (fun w _ => w⁻¹)
  · intro w hw
    exact Linearization.inv_mem_differenceSupport hw
  · intro w hw v hv heq
    exact inv_injective heq
  · intro w hw
    exact ⟨w⁻¹, Linearization.inv_mem_differenceSupport hw, by simp⟩
  · intro w hw
    rfl

omit [Fintype ι] [DecidableEq ι] in
theorem polynomial_adjoint (S : Finset G) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    (polynomial S a π).conjTranspose =
      ∑ w ∈ Linearization.differenceSupport S,
        (a w⁻¹).conjTranspose ⊗ₖ (π w : Matrix ν ν ℂ) := by
  have hstar (w : G) : (π w : Matrix ν ν ℂ).conjTranspose =
      (π w⁻¹ : Matrix ν ν ℂ) := by
    rw [map_inv]
    rfl
  unfold polynomial
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_kronecker, hstar]
  have h := inverse_support_sum S
    (fun w => (a w⁻¹).conjTranspose ⊗ₖ (π w : Matrix ν ν ℂ))
  simpa only [inv_inv] using h

omit [Fintype ι] [DecidableEq ι] in
/-- The coefficient assembly evaluates to the actual Hermitian dilation,
up to the explicit permutation that distributes a product over a sum. -/
theorem polynomial_dilation (S : Finset G) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    Matrix.reindex (Equiv.sumProdDistrib ι ι ν) (Equiv.sumProdDistrib ι ι ν)
        (polynomial S (dilationCoefficient a) π) =
      Linearization.hermitianDilation (polynomial S a π) := by
  rw [Linearization.hermitianDilation, polynomial_adjoint]
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [polynomial, dilationCoefficient, Matrix.reindex_apply,
          Matrix.sum_apply, Matrix.kroneckerMap_apply]
      | inr j => simp [polynomial, dilationCoefficient, Matrix.reindex_apply,
          Matrix.sum_apply, Matrix.kroneckerMap_apply]
  | inr i =>
      cases j with
      | inl j => simp [polynomial, dilationCoefficient, Matrix.reindex_apply,
          Matrix.sum_apply, Matrix.kroneckerMap_apply]
      | inr j => simp [polynomial, dilationCoefficient, Matrix.reindex_apply,
          Matrix.sum_apply, Matrix.kroneckerMap_apply]

private theorem reindex_shift {κ μ : Type*} [Fintype κ] [Fintype μ]
    [DecidableEq κ] [DecidableEq μ]
    (e : κ ≃ μ) (A : Matrix κ κ ℂ) (θ : ℝ) :
    Matrix.reindex e e (A + algebraMap ℝ (Matrix κ κ ℂ) θ) =
      Matrix.reindex e e A + algebraMap ℝ (Matrix μ μ ℂ) θ := by
  ext i j
  simp [Matrix.reindex_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
    Matrix.one_apply, e.symm.injective.eq_iff]

/-- The actual dilation, rather than general Hermiticity, supplies the exact
additive norm identity.  In particular no such identity is claimed for an
arbitrary self-adjoint coefficient polynomial. -/
theorem shifted_dilation_polynomial_norm [Nonempty ι] [Nonempty ν]
    (S : Finset G) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) (θ : ℝ) (hθ : 0 ≤ θ) :
    ‖polynomial S (dilationCoefficient a) π +
      algebraMap ℝ (Matrix ((ι ⊕ ι) × ν) ((ι ⊕ ι) × ν) ℂ) θ‖ =
        ‖polynomial S a π‖ + θ := by
  have h := MatrixNormReindex.reindex_norm (Equiv.sumProdDistrib ι ι ν)
    (polynomial S (dilationCoefficient a) π +
      algebraMap ℝ (Matrix ((ι ⊕ ι) × ν) ((ι ⊕ ι) × ν) ℂ) θ)
  rw [reindex_shift, polynomial_dilation,
    Linearization.shifted_dilation_norm _ θ hθ] at h
  exact h.symm

/-- The square factor polynomial in the appendix has exactly the original
polynomial norm plus its explicit constant as squared norm. -/
theorem paddedPolynomial_dilation_norm_sq [Nonempty ι] [Nonempty ν]
    (S : Finset G) (hS : (1 : G) ∈ S) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    ‖paddedPolynomial S hS (dilationCoefficient a) π‖ ^ 2 =
      ‖polynomial S a π‖ + theta S (dilationCoefficient a) := by
  rw [paddedPolynomial_norm, factorPolynomial_norm_sq S hS (dilationCoefficient a)
    (fun w _ => dilationCoefficient_inverse a w) π]
  exact shifted_dilation_polynomial_norm S a π _ (theta_nonneg S _)

/-- The exact finite representation identity of Appendix A, with actual
representation-independent square coefficient matrices. -/
theorem paddedPolynomial_dilation_norm_identity [Nonempty ι] [Nonempty ν]
    (S : Finset G) (hS : (1 : G) ∈ S) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    ‖polynomial S a π‖ = ‖paddedPolynomial S hS (dilationCoefficient a) π‖ ^ 2 -
      theta S (dilationCoefficient a) := by
  linarith [paddedPolynomial_dilation_norm_sq S hS a π]

/-- The exact Appendix A correction bound for the original polynomial,
with the regular dilation norm equality proved on the actual infinite
square-summable Hilbert spaces. -/
theorem theta_dilation_le_card_mul_regularNorm (S : Finset G) (hS : (1 : G) ∈ S)
    (a : G → Matrix ι ι ℂ) :
    theta S (dilationCoefficient a) ≤ (S.card : ℝ) *
      ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) a‖ := by
  have h := theta_le_card_mul_regularNorm S hS (dilationCoefficient a)
  have hnorm :
      ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S)
        (dilationCoefficient a)‖ =
      ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) a‖ := by
    simpa only [dilationCoefficient, RegularDilation.dilationCoefficient] using
      RegularDilation.dilation_polynomial_norm (Linearization.differenceSupport S)
        (fun _ hw => Linearization.inv_mem_differenceSupport hw) a
  rwa [hnorm] at h

/-- The finite representation form of the complete finite-set factorization
lemma.  The witnessing scalar and coefficient matrices are the explicit
constructions above and therefore do not depend on the representation. -/
theorem exists_finite_factorization [Nonempty ι] [Nonempty ν]
    (S : Finset G) (hS : (1 : G) ∈ S) (a : G → Matrix ι ι ℂ) :
    ∃ (θ : ℝ)
      (b : Support S → Matrix (Support S × (ι ⊕ ι)) (Support S × (ι ⊕ ι)) ℂ),
      0 ≤ θ ∧ θ ≤ (S.card : ℝ) *
        ‖RegularCoefficientEnergy.regularPolynomial (Linearization.differenceSupport S) a‖ ∧
      ∀ π : G →* unitary (Matrix ν ν ℂ),
        ‖polynomial S a π‖ =
          ‖∑ g : Support S, b g ⊗ₖ (π g.val : Matrix ν ν ℂ)‖ ^ 2 - θ := by
  refine ⟨theta S (dilationCoefficient a), paddedCoefficient S hS (dilationCoefficient a),
    theta_nonneg S _, theta_dilation_le_card_mul_regularNorm S hS a, ?_⟩
  intro π
  exact paddedPolynomial_dilation_norm_identity S hS a π

end Dilation

end Nonadditivity.FiniteSetFactorization
