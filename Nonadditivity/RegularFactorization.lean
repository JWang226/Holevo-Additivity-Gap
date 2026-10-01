/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FiniteSetFactorization
import Nonadditivity.RegularShiftedDilation

/-! # Finite-set factorization at the actual infinite regular representation

Rectangular coefficient matrices act pointwise on vector-valued square-summable
functions. Their lifted adjoints and products agree with the literal matrix
operations. This permits evaluation of the same positive Gram matrix used for
finite-dimensional representations at the infinite left regular representation.

The constructed square factor has exactly squared norm `‖P(λ)‖ + θ`, with the
same coefficients and scalar as its finite-representation evaluation. The scalar
bound `θ ≤ |S| ‖P(λ)‖` and both norm identities therefore yield the concrete
backward relative-error bound `e(P) ≤ 6 |S| e(Q)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.RegularFactorization
open RegularCoefficientEnergy
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

section Lift
variable {G E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def liftFunction (T : E →L[ℂ] F) (f : VectorHilbert G E) : VectorHilbert G F :=
  ⟨fun g => T (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (f := fun g => ‖T‖ ^ 2 * ‖f g‖ ^ 2)
      (fun _ => sq_nonneg _) (fun g => ?_) ?_
    · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (f g)) 2
    · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)⟩

theorem liftFunction_norm_le (T : E →L[ℂ] F) (f : VectorHilbert G E) :
    ‖liftFunction T f‖ ≤ ‖T‖ * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    (∑' g, ‖T (f g)‖ ^ 2) ≤ ∑' g, ‖T‖ ^ 2 * ‖f g‖ ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro g
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (f g)) 2
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (liftFunction T f).property.summable (by norm_num)
      · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (f.property.summable (by norm_num)).mul_left (‖T‖ ^ 2)
    _ = (‖T‖ * ‖f‖) ^ 2 := by
      rw [tsum_mul_left, mul_pow]
      congr 1
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum (by norm_num) f).symm

def lift (T : E →L[ℂ] F) : VectorHilbert G E →L[ℂ] VectorHilbert G F :=
  LinearMap.mkContinuous
    { toFun := liftFunction T
      map_add' := by intro f h; ext g; exact T.map_add _ _
      map_smul' := by intro c f; ext g; exact T.map_smul _ _ }
    ‖T‖ (liftFunction_norm_le T)

@[simp] theorem lift_apply (T : E →L[ℂ] F) (f : VectorHilbert G E) (g : G) :
    lift T f g = T (f g) := rfl

end Lift

section Matrix
variable {G ι κ μ : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

def rectLift (A : Matrix ι κ ℂ) : Hilbert G κ →L[ℂ] Hilbert G ι :=
  lift (Matrix.toEuclideanLin A).toContinuousLinearMap

@[simp] theorem rectLift_apply (A : Matrix ι κ ℂ) (f : Hilbert G κ) (g : G) :
    rectLift A f g = Matrix.toEuclideanLin A (f g) := rfl

@[simp] theorem rectLift_zero : rectLift (G := G) (0 : Matrix ι κ ℂ) = 0 := by
  ext f g i
  simp [rectLift_apply]

@[simp] theorem rectLift_add (A B : Matrix ι κ ℂ) :
    rectLift (G := G) (A+B) = rectLift A + rectLift B := by
  ext f g i
  simp [rectLift_apply]

@[simp] theorem rectLift_smul (r : ℝ) (A : Matrix ι κ ℂ) :
    rectLift (G := G) (r • A) = r • rectLift A := by
  ext f g i
  simp [rectLift_apply, Matrix.smul_mulVec]

@[simp] theorem rectLift_one : rectLift (G := G) (1 : Matrix ι ι ℂ) = 1 := by
  ext f g i
  change ((1 : Matrix ι ι ℂ) *ᵥ (f g).ofLp) i = f g i
  simp

@[simp] theorem rectLift_mul (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) :
    rectLift (G := G) (A*B) = (rectLift A).comp (rectLift B) := by
  ext f g i
  change ((A*B) *ᵥ (f g).ofLp) i = (A *ᵥ (B *ᵥ (f g).ofLp)) i
  rw [Matrix.mulVec_mulVec]

@[simp] theorem rectLift_adjoint (A : Matrix ι κ ℂ) :
    rectLift (G := G) A.conjTranspose = (rectLift A).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro g
  simp only [rectLift_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

@[simp] theorem rectLift_sum {α : Type*} (s : Finset α) (A : α → Matrix ι κ ℂ) :
    rectLift (G := G) (∑ a ∈ s, A a) = ∑ a ∈ s, rectLift (A a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

theorem rectLift_square (A : Matrix ι ι ℂ) :
    rectLift (G := G) A = liftOperator (coefficientOperator A) := by
  ext f g i
  rfl

theorem rectLift_shift (A : Matrix ι κ ℂ) (g : G) :
    (rectLift A).comp (leftRegular g) = (leftRegular g).comp (rectLift (G := G) A) := by
  ext f h i
  rfl

@[simp] theorem shift_mul (g h : G) :
    (leftRegular (ι := ι) g).comp (leftRegular h) = leftRegular (g*h) := by
  ext f w i
  simp [mul_assoc]

@[simp] theorem shift_one : leftRegular (G := G) (ι := ι) 1 = 1 := by
  ext f w i
  simp

@[simp] theorem shift_adjoint (g : G) : (leftRegular (ι := ι) g).adjoint = leftRegular g⁻¹ := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro h
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro f
  change inner ℂ ((leftRegular g).adjoint (lp.single 2 h x)) f =
    inner ℂ (leftRegular g⁻¹ (lp.single 2 h x)) f
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left, leftRegular_single,
    lp.inner_single_left]
  rfl

/-- A single rectangular coefficient times a genuine regular translation. -/
def term (A : Matrix ι κ ℂ) (g : G) : Hilbert G κ →L[ℂ] Hilbert G ι :=
  (rectLift A).comp (leftRegular g)

@[simp] theorem term_add (A B : Matrix ι κ ℂ) (g : G) :
    term (A+B) g = term A g + term B g := by simp [term, ContinuousLinearMap.add_comp]

@[simp] theorem term_smul (r : ℝ) (A : Matrix ι κ ℂ) (g : G) :
    term (r • A) g = r • term A g := by simp [term, ContinuousLinearMap.smul_comp]

@[simp] theorem term_zero (g : G) : term (0 : Matrix ι κ ℂ) g = 0 := by simp [term]

@[simp] theorem term_one (g : G) : term (1 : Matrix ι ι ℂ) g = leftRegular g := by
  ext f h i
  simp [term]

@[simp] theorem term_identity (A : Matrix ι κ ℂ) : term (G := G) A 1 = rectLift A := by
  ext f h i
  simp [term]

theorem term_mul (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) (g h : G) :
    (term A g).comp (term B h) = term (A*B) (g*h) := by
  simp only [term, rectLift_mul, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (leftRegular g), ← rectLift_shift,
    ContinuousLinearMap.comp_assoc, shift_mul]

theorem term_adjoint (A : Matrix ι κ ℂ) (g : G) :
    (term A g).adjoint = term A.conjTranspose g⁻¹ := by
  simp only [term, ContinuousLinearMap.adjoint_comp, shift_adjoint, ← rectLift_adjoint]
  exact (rectLift_shift _ _).symm

end Matrix

section Assembly
open FiniteSetFactorization
variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

/-- The actual column of regular translations on the given finite support. -/
def column (S : Finset G) : Hilbert G ι →L[ℂ] Hilbert G (Support S × ι) :=
  ∑ g : Support S, term (selector g).conjTranspose g.val

def evaluate (S : Finset G) (A : Matrix (Support S × ι) (Support S × ι) ℂ) :
    Hilbert G ι →L[ℂ] Hilbert G ι :=
  (column S).adjoint.comp ((rectLift A).comp (column S))

theorem select_column (S : Finset G) (g : Support S) :
    (rectLift (selector (ι := ι) g)).comp (column S) = leftRegular g.val := by
  rw [column, ContinuousLinearMap.comp_finset_sum]
  conv_lhs => arg 2; ext h; rw [← term_identity (G := G), term_mul, one_mul,
    selector_mul_adjoint]
  rw [Finset.sum_eq_single g]
  · simp
  · intro h hh hne
    simp [Ne.symm hne]
  · simp

@[simp] theorem evaluate_add (S : Finset G)
    (A B : Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate S (A+B) = evaluate S A + evaluate S B := by
  simp [evaluate, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

@[simp] theorem evaluate_smul (S : Finset G) (r : ℝ)
    (A : Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate S (r • A) = r • evaluate S A := by
  simp [evaluate, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem evaluate_sum {α : Type*} (S : Finset G) (s : Finset α)
    (A : α → Matrix (Support S × ι) (Support S × ι) ℂ) :
    evaluate S (∑ a ∈ s, A a) = ∑ a ∈ s, evaluate S (A a) := by
  simp [evaluate, ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum]

theorem evaluate_place (S : Finset G) (g h : Support S) (A : Matrix ι ι ℂ) :
    evaluate S (place g h A) = term A (g.val⁻¹*h.val) := by
  have heq : evaluate S (place g h A) =
      ((rectLift (selector g)).comp (column S)).adjoint.comp
        ((rectLift A).comp ((rectLift (selector h)).comp (column S))) := by
    simp only [evaluate, place, rectLift_mul, rectLift_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
  rw [heq, select_column, select_column, shift_adjoint, ← ContinuousLinearMap.comp_assoc, ← rectLift_shift,
    ContinuousLinearMap.comp_assoc, shift_mul]
  rfl

theorem evaluate_polarInsertion (S : Finset G) (g h : Support S) (c : Matrix ι ι ℂ) :
    evaluate S (polarInsertion g h c) =
      rectLift (CFC.abs c.conjTranspose) + term c (g.val⁻¹*h.val) +
      term c.conjTranspose (h.val⁻¹*g.val) + rectLift (CFC.abs c) := by
  rw [polarInsertion_eq]
  simp only [evaluate_add, evaluate_place, inv_mul_cancel, term_identity]

theorem evaluate_representative (S : Finset G) (c : G → Matrix ι ι ℂ)
    (w : NonidentityWords S) :
    evaluate S (polarInsertion (representative S w).1 (representative S w).2 (c w.val)) =
      rectLift (CFC.abs (c w.val).conjTranspose) + term (c w.val) w.val +
      term (c w.val).conjTranspose w.val⁻¹ + rectLift (CFC.abs (c w.val)) := by
  rw [evaluate_polarInsertion, representative_spec]
  have hinv : (representative S w).2.val⁻¹ * (representative S w).1.val = w.val⁻¹ := by
    rw [← representative_spec S w]
    simp
  rw [hinv]

theorem evaluate_nonconstantGram (S : Finset G) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    evaluate S (nonconstantGram S c) =
      (∑ w : NonidentityWords S, term (c w.val) w.val) + rectLift (diagonalCorrection S c) := by
  have hmod : (∑ w : NonidentityWords S, CFC.abs (c w.val).conjTranspose) =
      diagonalCorrection S c := by
    unfold diagonalCorrection
    apply Fintype.sum_equiv (inverseWords S)
    intro w
    rw [← hstar w.val (Finset.mem_erase.mp w.property).2]
    rfl
  have hinv : (∑ w : NonidentityWords S, term (c w.val).conjTranspose w.val⁻¹) =
      ∑ w : NonidentityWords S, term (c w.val) w.val := by
    apply Fintype.sum_equiv (inverseWords S)
    intro w
    rw [← hstar w.val (Finset.mem_erase.mp w.property).2]
    rfl
  unfold nonconstantGram
  rw [evaluate_sum]
  simp only [evaluate_smul, evaluate_representative]
  rw [← Finset.smul_sum]
  simp only [Finset.sum_add_distrib]
  rw [← rectLift_sum, hmod, hinv, ← rectLift_sum]
  change (1 / 2 : ℝ) •
    (rectLift (diagonalCorrection S c) +
      (∑ w : NonidentityWords S, term (c w.val) w.val) +
      (∑ w : NonidentityWords S, term (c w.val) w.val) +
      rectLift (diagonalCorrection S c)) = _
  module

theorem polynomial_eq (S : Finset G) (c : G → Matrix ι ι ℂ) :
    regularPolynomial S c = ∑ w ∈ S, term (c w) w := by
  simp only [regularPolynomial, term, rectLift_square]

theorem polynomial_decompose (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    regularPolynomial (Linearization.differenceSupport S) c =
      (∑ w : NonidentityWords S, term (c w.val) w.val) + rectLift (c 1) := by
  have h1 : (1:G) ∈ Linearization.differenceSupport S :=
    Linearization.mem_differenceSupport.mpr ⟨1,hS,1,hS,by simp⟩
  rw [polynomial_eq]
  have hs : (∑ w : NonidentityWords S, term (c w.val) w.val) =
      ∑ w ∈ (Linearization.differenceSupport S).erase 1, term (c w) w :=
    (Finset.sum_subtype (p := fun w => w ∈ (Linearization.differenceSupport S).erase 1)
      ((Linearization.differenceSupport S).erase 1) (fun _ => Iff.rfl) (fun w => term (c w) w)).symm
  rw [hs, ← term_identity (G := G) (c 1)]
  exact (Finset.sum_erase_add _ _ h1).symm

@[simp] theorem rectLift_algebraMap (r : ℝ) :
    rectLift (G := G) (algebraMap ℝ (Matrix ι ι ℂ) r) =
      algebraMap ℝ (Hilbert G ι →L[ℂ] Hilbert G ι) r := by
  simp only [Algebra.algebraMap_eq_smul_one, rectLift_smul, rectLift_one]

/-- Infinite regular evaluation of the actual finite positive Gram matrix. -/
theorem evaluate_gramMatrix (S : Finset G) (hS : (1:G) ∈ S)
    (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    evaluate S (gramMatrix S hS c) =
      regularPolynomial (Linearization.differenceSupport S) c +
        algebraMap ℝ (Hilbert G ι →L[ℂ] Hilbert G ι) (theta S c) := by
  rw [gramMatrix, evaluate_add, evaluate_nonconstantGram S c hstar, evaluate_place]
  simp only [inv_one, one_mul, term_identity]
  rw [add_assoc, ← rectLift_add]
  have hc : diagonalCorrection S c + constantCorrection S c =
      c 1 + algebraMap ℝ (Matrix ι ι ℂ) (theta S c) := by
    unfold constantCorrection
    abel
  rw [hc, rectLift_add, rectLift_algebraMap, polynomial_decompose S hS c]
  abel

/-- Rectangular square-root factor evaluated at the actual regular representation. -/
def factor (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Hilbert G ι →L[ℂ] Hilbert G (Support S × ι) :=
  ∑ g : Support S, term (factorCoefficient S hS c g) g.val

theorem factor_eq (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    factor S hS c = (rectLift (CFC.sqrt (gramMatrix S hS c))).comp (column S) := by
  unfold factor factorCoefficient column term
  rw [ContinuousLinearMap.comp_finset_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [rectLift_mul, ContinuousLinearMap.comp_assoc]

/-- The Gram identity holds on the true infinite regular Hilbert space. -/
theorem factor_gram (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    (factor S hS c).adjoint.comp (factor S hS c) =
      regularPolynomial (Linearization.differenceSupport S) c +
        algebraMap ℝ (Hilbert G ι →L[ℂ] Hilbert G ι) (theta S c) := by
  have hG := gramMatrix_posSemidef S hS c hstar
  have hR := Linearization.positive_sqrt_gram (gramMatrix S hS c) hG
  rw [factor_eq, ContinuousLinearMap.adjoint_comp, ← rectLift_adjoint]
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (rectLift _),
    ← rectLift_mul, hR]
  exact evaluate_gramMatrix S hS c hstar

/-- Padding into the identity coefficient block preserves any rectangular
operator norm, also in infinite dimension. -/
theorem norm_comp_coisometry {E F H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : E →L[ℂ] F) (V : H →L[ℂ] E)
    (hV : V.comp V.adjoint = 1) : ‖Q.comp V‖ = ‖Q‖ := by
  have hgram : (Q.comp V).comp (Q.comp V).adjoint = Q.comp Q.adjoint := by
    rw [ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc V, hV]
    rfl
  have hnorm (A : H →L[ℂ] F) : ‖A.comp A.adjoint‖ = ‖A‖ * ‖A‖ := by
    simpa using ContinuousLinearMap.norm_adjoint_comp_self A.adjoint
  have hQ : ‖Q.comp Q.adjoint‖ = ‖Q‖ * ‖Q‖ := by
    simpa using ContinuousLinearMap.norm_adjoint_comp_self Q.adjoint
  have hQV := hnorm (Q.comp V)
  rw [hgram, hQ] at hQV
  nlinarith [norm_nonneg Q, norm_nonneg (Q.comp V)]

/-- The very same padded coefficients as in the finite representation theorem,
evaluated on actual infinite vector-valued square-summable functions. -/
def padded (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    Hilbert G (Support S × ι) →L[ℂ] Hilbert G (Support S × ι) :=
  ∑ g : Support S, term (paddedCoefficient S hS c g) g.val

/-- Extend the constructed supported coefficients by zero to the whole group. -/
def paddedCoefficients (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (g : G) : Matrix (Support S × ι) (Support S × ι) ℂ :=
  if hg : g ∈ S then paddedCoefficient S hS c ⟨g,hg⟩ else 0

/-- The regular factor is exactly the established literal regular-polynomial API. -/
theorem padded_eq_regularPolynomial (S : Finset G) (hS : (1:G) ∈ S)
    (c : G → Matrix ι ι ℂ) :
    padded S hS c = regularPolynomial S (paddedCoefficients S hS c) := by
  rw [polynomial_eq]
  unfold padded
  rw [← Finset.sum_coe_sort S (fun g => term (paddedCoefficients S hS c g) g)]
  apply Finset.sum_congr rfl
  intro g hg
  simp [paddedCoefficients, g.property]

theorem padded_eq (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    padded S hS c = (factor S hS c).comp (rectLift (selector (⟨1,hS⟩ : Support S))) := by
  unfold padded factor paddedCoefficient
  rw [ContinuousLinearMap.finset_sum_comp]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← term_identity (G := G) (selector (⟨1,hS⟩ : Support S)), term_mul, mul_one]

theorem padded_norm (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ) :
    ‖padded S hS c‖ = ‖factor S hS c‖ := by
  rw [padded_eq]
  apply norm_comp_coisometry
  rw [← rectLift_adjoint, ← rectLift_mul, selector_mul_adjoint]
  simp

/-- Squared norm of the factor from its proved, literal infinite Gram identity. -/
theorem padded_norm_sq (S : Finset G) (hS : (1:G) ∈ S) (c : G → Matrix ι ι ℂ)
    (hstar : ∀ w ∈ Linearization.differenceSupport S, c w⁻¹ = (c w).conjTranspose) :
    ‖padded S hS c‖ ^ 2 =
      ‖regularPolynomial (Linearization.differenceSupport S) c +
        algebraMap ℝ (Hilbert G ι →L[ℂ] Hilbert G ι) (theta S c)‖ := by
  rw [padded_norm, pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self,
    factor_gram S hS c hstar]

/-- Exact norm of the square factor for the infinite left regular representation. -/
theorem padded_dilation_norm_sq [Nonempty ι] (S : Finset G) (hS : (1:G) ∈ S)
    (a : G → Matrix ι ι ℂ) :
    ‖padded S hS (dilationCoefficient a)‖ ^ 2 =
      ‖regularPolynomial (Linearization.differenceSupport S) a‖ +
        theta S (dilationCoefficient a) := by
  rw [padded_norm_sq S hS (dilationCoefficient a)
    (fun w _ => dilationCoefficient_inverse a w)]
  exact RegularShiftedDilation.shifted_dilation_polynomial_norm
    (Linearization.differenceSupport S)
    (fun _ hw => Linearization.inv_mem_differenceSupport hw) a _ (theta_nonneg S _)

/-- The exact Appendix A identity now holds at the genuine infinite regular representation. -/
theorem padded_dilation_norm_identity [Nonempty ι] (S : Finset G) (hS : (1:G) ∈ S)
    (a : G → Matrix ι ι ℂ) :
    ‖regularPolynomial (Linearization.differenceSupport S) a‖ =
      ‖padded S hS (dilationCoefficient a)‖ ^ 2 - theta S (dilationCoefficient a) := by
  linarith [padded_dilation_norm_sq S hS a]

/-- The shared actual coefficients satisfy both the finite representation and
infinite regular norm identities, together with the original regular norm bound. -/
theorem exists_factorization [Nonempty ι] {ν : Type*}
    [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (S : Finset G) (hS : (1:G) ∈ S) (a : G → Matrix ι ι ℂ) :
    ∃ (θ : ℝ)
      (b : Support S → Matrix (Support S × (ι ⊕ ι)) (Support S × (ι ⊕ ι)) ℂ),
      0 ≤ θ ∧ θ ≤ (S.card : ℝ) *
        ‖regularPolynomial (Linearization.differenceSupport S) a‖ ∧
      ‖regularPolynomial (Linearization.differenceSupport S) a‖ =
        ‖∑ g : Support S, term (b g) g.val‖ ^ 2 - θ ∧
      ∀ π : G →* unitary (Matrix ν ν ℂ),
        ‖polynomial S a π‖ =
          ‖∑ g : Support S, b g ⊗ₖ (π g.val : Matrix ν ν ℂ)‖ ^ 2 - θ := by
  refine ⟨theta S (dilationCoefficient a), paddedCoefficient S hS (dilationCoefficient a),
    theta_nonneg S _, theta_dilation_le_card_mul_regularNorm S hS a,
    padded_dilation_norm_identity S hS a, ?_⟩
  intro π
  exact paddedPolynomial_dilation_norm_identity S hS a π

/-- Quantitative finite-to-regular transfer for the actual constructed factors.
Every Gram identity and the scalar correction bound is discharged internally. -/
theorem finite_regular_error_transfer [Nonempty ι] {ν : Type*}
    [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (S : Finset G) (hS : (1:G) ∈ S) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ)) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hQ : ‖paddedPolynomial S hS (dilationCoefficient a) π‖ ≤
      (1+ε) * ‖padded S hS (dilationCoefficient a)‖) :
    ‖polynomial S a π‖ ≤ (1 + 6 * (S.card : ℝ) * ε) *
      ‖regularPolynomial (Linearization.differenceSupport S) a‖ := by
  have hB : (1:ℝ) ≤ S.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hS⟩
  exact Linearization.backward_error_transfer _ _ _ _
    (theta S (dilationCoefficient a)) (S.card : ℝ) ε
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (theta_nonneg S _) hB hε hε1
    (paddedPolynomial_dilation_norm_sq S hS a π)
    (padded_dilation_norm_sq S hS a)
    (theta_dilation_le_card_mul_regularNorm S hS a) hQ

/-- The literal relative-error inequality from Appendix A, now for concrete
finite and infinite regular evaluations of the same constructed polynomial. -/
theorem relative_error_transfer [Nonempty ι] {ν : Type*}
    [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (S : Finset G) (hS : (1:G) ∈ S) (a : G → Matrix ι ι ℂ)
    (π : G →* unitary (Matrix ν ν ℂ))
    (hP : 0 < ‖regularPolynomial (Linearization.differenceSupport S) a‖)
    (hQ : Linearization.relativeNormError
      ‖paddedPolynomial S hS (dilationCoefficient a) π‖
      ‖padded S hS (dilationCoefficient a)‖ ≤ 1) :
    Linearization.relativeNormError ‖polynomial S a π‖
      ‖regularPolynomial (Linearization.differenceSupport S) a‖ ≤
      6 * (S.card : ℝ) * Linearization.relativeNormError
        ‖paddedPolynomial S hS (dilationCoefficient a) π‖
        ‖padded S hS (dilationCoefficient a)‖ := by
  have hB : (1:ℝ) ≤ S.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hS⟩
  exact Linearization.relative_backward_error_transfer _ _ _ _
    (theta S (dilationCoefficient a)) (S.card : ℝ)
    (norm_nonneg _) (norm_nonneg _) hP
    (theta_nonneg S _) hB
    (paddedPolynomial_dilation_norm_sq S hS a π)
    (padded_dilation_norm_sq S hS a)
    (theta_dilation_le_card_mul_regularNorm S hS a) hQ

/-- One representation-independent factor, including its uniform error transfer
from every finite representation to the infinite regular representation. -/
theorem exists_factorization_with_error_transfer [Nonempty ι] {ν : Type*}
    [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (S : Finset G) (hS : (1:G) ∈ S) (a : G → Matrix ι ι ℂ) :
    ∃ (θ : ℝ)
      (b : Support S → Matrix (Support S × (ι ⊕ ι)) (Support S × (ι ⊕ ι)) ℂ),
      0 ≤ θ ∧ θ ≤ (S.card : ℝ) *
        ‖regularPolynomial (Linearization.differenceSupport S) a‖ ∧
      ‖regularPolynomial (Linearization.differenceSupport S) a‖ =
        ‖∑ g : Support S, term (b g) g.val‖ ^ 2 - θ ∧
      ∀ π : G →* unitary (Matrix ν ν ℂ),
        ‖polynomial S a π‖ =
          ‖∑ g : Support S, b g ⊗ₖ (π g.val : Matrix ν ν ℂ)‖ ^ 2 - θ ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          ‖∑ g : Support S, b g ⊗ₖ (π g.val : Matrix ν ν ℂ)‖ ≤
            (1+ε) * ‖∑ g : Support S, term (b g) g.val‖ →
          ‖polynomial S a π‖ ≤ (1 + 6 * (S.card : ℝ) * ε) *
            ‖regularPolynomial (Linearization.differenceSupport S) a‖ := by
  refine ⟨theta S (dilationCoefficient a), paddedCoefficient S hS (dilationCoefficient a),
    theta_nonneg S _, theta_dilation_le_card_mul_regularNorm S hS a,
    padded_dilation_norm_identity S hS a, ?_⟩
  intro π
  refine ⟨paddedPolynomial_dilation_norm_identity S hS a π, ?_⟩
  intro ε hε hε1 hQ
  exact finite_regular_error_transfer S hS a π ε hε hε1 hQ

end Assembly
end Nonadditivity.RegularFactorization
