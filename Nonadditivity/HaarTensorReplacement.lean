/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductMomentBridge

/-! # Literal partial evaluation of a tensor-group polynomial

Replacing one group coordinate by matrices is a ring homomorphism into
matrix-valued polynomials on the remaining group. Consequently powers and
vacuum moments are those of the original polynomial, with just that coordinate
evaluated. No tensor independence or trace comparison is built into the map.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarTensorReplacement
open HaarWordExpansion
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker

variable {G H ι ν : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

def partialCoefficientHom : Matrix ι ι ℂ →+* MatrixPolynomial H (ι × ν) :=
  MonoidAlgebra.singleOneRingHom.comp (coefficientHom (ν := ν))

def partialWordHom (ρ : G →* Matrix ν ν ℂ) :
    G × H →* MatrixPolynomial H (ι × ν) where
  toFun w := MonoidAlgebra.single w.2 ((1 : Matrix ι ι ℂ) ⊗ₖ ρ w.1)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' a b := by
    simp only [MonoidAlgebra.single_mul_single, Prod.fst_mul, Prod.snd_mul, map_mul]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem partial_commute (ρ : G →* Matrix ν ν ℂ) (A : Matrix ι ι ℂ) (w : G × H) :
    Commute (partialCoefficientHom (H := H) (ν := ν) A) (partialWordHom ρ w) := by
  change MonoidAlgebra.single 1 (A ⊗ₖ (1 : Matrix ν ν ℂ)) *
      MonoidAlgebra.single w.2 ((1 : Matrix ι ι ℂ) ⊗ₖ ρ w.1) =
    MonoidAlgebra.single w.2 ((1 : Matrix ι ι ℂ) ⊗ₖ ρ w.1) *
      MonoidAlgebra.single 1 (A ⊗ₖ (1 : Matrix ν ν ℂ))
  simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

def partialEval (ρ : G →* Matrix ν ν ℂ) :
    MatrixPolynomial (G × H) ι →+* MatrixPolynomial H (ι × ν) :=
  MonoidAlgebra.liftNCRingHom partialCoefficientHom (partialWordHom ρ)
    (partial_commute ρ)

@[simp] theorem partialEval_single (ρ : G →* Matrix ν ν ℂ)
    (w : G × H) (A : Matrix ι ι ℂ) :
    partialEval ρ (MonoidAlgebra.single w A) = MonoidAlgebra.single w.2 (A ⊗ₖ ρ w.1) := by
  simp only [partialEval, MonoidAlgebra.liftNCRingHom_single]
  change MonoidAlgebra.single 1 (A ⊗ₖ (1 : Matrix ν ν ℂ)) *
    MonoidAlgebra.single w.2 ((1 : Matrix ι ι ℂ) ⊗ₖ ρ w.1) = _
  simp only [MonoidAlgebra.single_mul_single, one_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem partialEval_eq_sum (ρ : G →* Matrix ν ν ℂ) (f : MatrixPolynomial (G × H) ι) :
    partialEval ρ f = ∑ w ∈ f.support, MonoidAlgebra.single w.2 (f w ⊗ₖ ρ w.1) := by
  conv_lhs => rw [← MonoidAlgebra.sum_single f]
  change partialEval ρ (∑ w ∈ f.support, MonoidAlgebra.single w (f w)) = _
  simp only [map_sum, partialEval_single]

theorem partialEval_apply (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial (G × H) ι) (h : H) :
    partialEval ρ f h = ∑ w ∈ f.support, if w.2 = h then f w ⊗ₖ ρ w.1 else 0 := by
  rw [partialEval_eq_sum]
  change (∑ w ∈ f.support, (Finsupp.single w.2 (f w ⊗ₖ ρ w.1) : H →₀ Matrix (ι × ν) (ι × ν) ℂ)) h = _
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem normalizedTrace_kronecker (A : Matrix ι ι ℂ) (B : Matrix ν ν ℂ) :
    normalizedTrace (A ⊗ₖ B) = normalizedTrace A * normalizedTrace B := by
  simp only [normalizedTrace, Matrix.trace_kronecker, Fintype.card_prod, Nat.cast_mul]
  ring

theorem vacuumTrace_partialEval (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial (G × H) ι) :
    vacuumTrace (partialEval ρ f) = ∑ w ∈ f.support,
      if w.2 = 1 then normalizedTrace (f w) * normalizedTrace (ρ w.1) else 0 := by
  rw [vacuumTrace, partialEval_apply]
  simp only [normalizedTrace, Matrix.trace_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs with h
  · exact normalizedTrace_kronecker _ _
  · simp

/-- The moment after a replacement is the literal evaluated moment. -/
theorem vacuumTrace_partialEval_pow (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial (G × H) ι) (p : ℕ) :
    vacuumTrace ((partialEval ρ f)^p) = ∑ w ∈ (f^p).support,
      if w.2 = 1 then normalizedTrace ((f^p) w) * normalizedTrace (ρ w.1) else 0 := by
  rw [← map_pow, vacuumTrace_partialEval]

theorem partialEval_support (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial (G × H) ι) :
    (partialEval ρ f).support ⊆ f.support.image Prod.snd := by
  intro h hh
  by_contra hnot
  have hz : partialEval ρ f h = 0 := by
    rw [partialEval_apply]
    apply Finset.sum_eq_zero
    intro w hw
    have hn : w.2 ≠ h := fun he => hnot (Finset.mem_image.mpr ⟨w, hw, he⟩)
    simp only [hn, ↓reduceIte]
  exact (Finsupp.mem_support_iff.mp hh) hz

/-! The involution is written explicitly, since the group algebra currently has
no built-in convolution-star instance. -/

def adjointPolynomial (f : MatrixPolynomial G ι) : MatrixPolynomial G ι :=
  Finsupp.mapDomain Inv.inv
    (Finsupp.mapRange Matrix.conjTranspose Matrix.conjTranspose_zero f)

@[simp] theorem adjointPolynomial_apply (f : MatrixPolynomial G ι) (g : G) :
    adjointPolynomial f g = (f g⁻¹).conjTranspose := by
  unfold adjointPolynomial
  simpa only [inv_inv, Finsupp.mapRange_apply] using
    Finsupp.mapDomain_apply (f := Inv.inv) inv_injective
      (Finsupp.mapRange Matrix.conjTranspose Matrix.conjTranspose_zero f) (g⁻¹)

@[simp] theorem adjointPolynomial_zero : adjointPolynomial (0 : MatrixPolynomial G ι) = 0 := by
  ext g i j
  simp

@[simp] theorem adjointPolynomial_add (f k : MatrixPolynomial G ι) :
    adjointPolynomial (f+k) = adjointPolynomial f + adjointPolynomial k := by
  ext g i j
  simp

@[simp] theorem adjointPolynomial_single (g : G) (A : Matrix ι ι ℂ) :
    adjointPolynomial (MonoidAlgebra.single g A) =
      MonoidAlgebra.single g⁻¹ A.conjTranspose := by
  simp only [adjointPolynomial, Finsupp.mapRange_single, Finsupp.mapDomain_single]

theorem regularEval_adjointPolynomial (f : MatrixPolynomial G ι) :
    regularEval (adjointPolynomial f) = (regularEval f).adjoint := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk =>
    change regularEval (adjointPolynomial ((f : MatrixPolynomial G ι) + k)) = _
    rw [adjointPolynomial_add, map_add, hf, hk, map_add, map_add]
  | single g A => simp only [adjointPolynomial_single, regularEval_single,
      RegularFactorization.term_adjoint]

theorem regularEval_single_column (f : MatrixPolynomial G ι)
    (x : RegularCoefficientEnergy.CoefficientSpace ι) (g : G) :
    regularEval f (lp.single 2 (1:G) x) g =
      RegularCoefficientEnergy.coefficientOperator (f g) x := by
  rw [regularEval_eq_regularPolynomial,
    RegularCoefficientEnergy.regularPolynomial_single_one]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  by_cases h : g ∈ f.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h,
      RegularCoefficientEnergy.coefficientOperator]

theorem regularEval_injective : Function.Injective (regularEval (G := G) (ι := ι)) := by
  intro f k he
  ext g i j
  have hh := congrArg (fun T : RegularCoefficientEnergy.Hilbert G ι →L[ℂ]
      RegularCoefficientEnergy.Hilbert G ι =>
      T (lp.single 2 (1:G) (EuclideanSpace.single j 1)) g i) he
  simp only [regularEval_single_column] at hh
  change ((f g) *ᵥ Pi.single j (1 : ℂ)) i = ((k g) *ᵥ Pi.single j (1 : ℂ)) i at hh
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh

theorem regularEval_selfAdjoint_iff (f : MatrixPolynomial G ι) :
    IsSelfAdjoint (regularEval f) ↔ adjointPolynomial f = f := by
  change (regularEval f).adjoint = regularEval f ↔ _
  rw [← regularEval_adjointPolynomial]
  exact ⟨fun h => regularEval_injective h, fun h => congrArg regularEval h⟩

theorem partialEval_adjointPolynomial
    (ρ : G →* unitary (Matrix ν ν ℂ)) (f : MatrixPolynomial (G × H) ι) :
    partialEval (representationMatrix ρ) (adjointPolynomial f) =
      adjointPolynomial (partialEval (representationMatrix ρ) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk =>
    change partialEval (representationMatrix ρ)
      (adjointPolynomial ((f : MatrixPolynomial (G × H) ι) + k)) = _
    rw [adjointPolynomial_add, map_add, hf, hk, map_add, adjointPolynomial_add]
  | single g A =>
    simp only [adjointPolynomial_single, partialEval_single, Prod.fst_inv, Prod.snd_inv,
      Matrix.conjTranspose_kronecker]
    congr 1
    change A.conjTranspose ⊗ₖ (ρ g.1⁻¹ : Matrix ν ν ℂ) =
      A.conjTranspose ⊗ₖ (ρ g.1 : Matrix ν ν ℂ).conjTranspose
    rw [map_inv]
    rfl

/-- Self-adjointness survives the actual matrix substitution. -/
theorem partialEval_selfAdjoint
    (ρ : G →* unitary (Matrix ν ν ℂ)) (f : MatrixPolynomial (G × H) ι)
    (hf : IsSelfAdjoint (regularEval f)) :
    IsSelfAdjoint (regularEval (partialEval (representationMatrix ρ) f)) := by
  rw [regularEval_selfAdjoint_iff] at hf ⊢
  rw [← partialEval_adjointPolynomial, hf]

end Nonadditivity.HaarTensorReplacement
