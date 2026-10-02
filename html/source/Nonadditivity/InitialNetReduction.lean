/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NetPolynomialSupport
import Nonadditivity.HaarMomentTail
import Nonadditivity.FreeEmbedding

/-! # The undoubled initial Gram construction for a symmetric test net

The square coefficients have exactly `|B| * |J|` rows, and use only individual
branch words. The same coefficients are evaluated in finite representations
and on the actual infinite left regular Hilbert space.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Nonadditivity.InitialNetReduction
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker
open FiniteSetFactorization (selector)
open RegularFactorization (term rectLift)

section Construction
variable {G B J : Type} [Group G] [DecidableEq G]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype J] [DecidableEq J]

/-- The fixed, representation-independent positive coefficient matrix. -/
def gramMatrix (A : J → Matrix B B ℂ) : Matrix (B × J) (B × J) ℂ :=
  ((Fintype.card B : ℝ)⁻¹) • (1 + Matrix.blockDiagonal A)

/-- A single fixed column is sufficient; no Hermitian doubling occurs. -/
def coefficient (A : J → Matrix B B ℂ) (b₀ b : B) : Matrix (B × J) (B × J) ℂ :=
  CFC.sqrt (gramMatrix A) * (selector (ι := J) b).conjTranspose * selector b₀

def regularColumn (w : B → G) :
    RegularCoefficientEnergy.Hilbert G J →L[ℂ] RegularCoefficientEnergy.Hilbert G (B × J) :=
  ∑ b, term (selector (ι := J) b).conjTranspose (w b)

def regularFactor (w : B → G) (A : J → Matrix B B ℂ) :
    RegularCoefficientEnergy.Hilbert G J →L[ℂ] RegularCoefficientEnergy.Hilbert G (B × J) :=
  (rectLift (CFC.sqrt (gramMatrix A))).comp (regularColumn w)

def regularEval (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :=
  ∑ b, term (coefficient A b₀ b) (w b)

def pairedCoefficient (A : J → Matrix B B ℂ) (p : B × B) (j : J) : ℂ :=
  (Fintype.card B : ℂ)⁻¹ * A j p.1 p.2

def pairedWord (w : B → G) (p : B × B) : G := (w p.1)⁻¹ * w p.2

def regularPaired (w : B → G) (A : J → Matrix B B ℂ) :=
  NetPolynomial.regularPolynomial (pairedWord w) (pairedCoefficient A)

/-- Injective word substitution preserves the actual paired regular norm,
including the short free-group embedding used before tensor-factor reduction. -/
theorem regularPaired_injective_norm_eq {H : Type} [Group H] [DecidableEq H]
    (φ : G →* H) (hφ : Function.Injective φ) (w : B → G) (A : J → Matrix B B ℂ) :
    ‖regularPaired (fun b => φ (w b)) A‖ = ‖regularPaired w A‖ := by
  simpa only [regularPaired, NetPolynomial.regularPolynomial, pairedWord, map_mul, map_inv]
    using MatrixRegularRestriction.coefficientPolynomial_injective_norm_eq φ hφ
      (pairedWord w) (fun p => RegularCoefficientEnergy.coefficientOperator
        (NetPolynomial.diagonalCoefficient (pairedCoefficient A) p))

theorem norm_le_hsLength (A : Matrix B B ℂ) (hA : A.IsHermitian) :
    ‖A‖ ≤ AdjointPurity.hsLength A := by
  have h := HaarMomentTail.norm_pow_le_trace_even A hA 1
  simp only [show 2 * 1 = 2 by omega, pow_two] at h
  have hs := AdjointPurity.hsLength_sq_of_isHermitian A hA
  nlinarith [norm_nonneg A, AdjointPurity.hsLength_nonneg A]

theorem gramMatrix_posSemidef (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1) :
    (gramMatrix A).PosSemidef := by
  letI : CStarAlgebra (Matrix (B × J) (B × J) ℂ) := { }
  have hself : IsSelfAdjoint (Matrix.blockDiagonal A) :=
    (NetPolynomial.blockDiagonal_isHermitian A hA).isSelfAdjoint
  have hn : ‖Matrix.blockDiagonal A‖ ≤ 1 := by
    rw [NetPolynomial.blockDiagonal_norm]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr hnorm
  have hle := hself.neg_algebraMap_norm_le_self
  have hn' : -(1 : Matrix (B × J) (B × J) ℂ) ≤ Matrix.blockDiagonal A := by
    calc
      _ ≤ -algebraMap ℝ (Matrix (B × J) (B × J) ℂ) ‖Matrix.blockDiagonal A‖ := by
        apply neg_le_neg
        simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using (smul_le_smul_of_nonneg_right hn (show (0 : Matrix (B × J) (B × J) ℂ) ≤ 1 from zero_le_one))
      _ ≤ _ := hle
  have hp : (1 + Matrix.blockDiagonal A).PosSemidef :=
    Matrix.LE.le.posSemidef (by simpa only [add_neg_cancel, add_comm] using add_le_add_left hn' 1)
  exact hp.smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem regularEval_eq (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    regularEval w A b₀ = (regularFactor w A).comp (rectLift (selector b₀)) := by
  unfold regularEval coefficient regularFactor regularColumn
  simp only [ContinuousLinearMap.comp_finset_sum, ContinuousLinearMap.finset_sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rw [← RegularFactorization.term_identity (G := G), RegularFactorization.term_mul,
    one_mul, ← RegularFactorization.term_identity (G := G),
    RegularFactorization.term_mul, mul_one]

theorem regularEval_norm (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    ‖regularEval w A b₀‖ = ‖regularFactor w A‖ := by
  rw [regularEval_eq]
  apply RegularFactorization.norm_comp_coisometry
  rw [← RegularFactorization.rectLift_adjoint, ← RegularFactorization.rectLift_mul,
    FiniteSetFactorization.selector_mul_adjoint]
  simp

theorem select_blockDiagonal (A : J → Matrix B B ℂ) (a b : B) :
    selector a * Matrix.blockDiagonal A * (selector b).conjTranspose =
      Matrix.diagonal (fun j => A j a b) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [Matrix.mul_apply, selector, Matrix.conjTranspose_apply, Matrix.blockDiagonal_apply,
      Fintype.sum_prod_type, eq_comm]
  · simp [Matrix.mul_apply, selector, Matrix.conjTranspose_apply, Matrix.blockDiagonal_apply,
      Fintype.sum_prod_type, eq_comm, hjk]

theorem select_gramMatrix (A : J → Matrix B B ℂ) (a b : B) :
    selector a * gramMatrix A * (selector b).conjTranspose =
      ((Fintype.card B : ℝ)⁻¹) •
        ((if a = b then (1 : Matrix J J ℂ) else 0) + Matrix.diagonal (fun j => A j a b)) := by
  simp only [gramMatrix, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, FiniteSetFactorization.selector_mul_adjoint, select_blockDiagonal]

/-- Evaluation of an arbitrary coefficient Gram matrix on the actual regular column. -/
theorem regularColumn_gram (w : B → G) (M : Matrix (B × J) (B × J) ℂ) :
    (regularColumn w).adjoint.comp ((rectLift M).comp (regularColumn w)) =
      ∑ a, ∑ b, term (selector a * M * (selector b).conjTranspose) ((w a)⁻¹ * w b) := by
  simp only [regularColumn, map_sum, ContinuousLinearMap.comp_finset_sum,
    ContinuousLinearMap.finset_sum_comp, RegularFactorization.term_adjoint,
    Matrix.conjTranspose_conjTranspose]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← RegularFactorization.term_identity (G := G), RegularFactorization.term_mul,
    one_mul, RegularFactorization.term_mul]
  rw [Matrix.mul_assoc]

theorem regularFactor_gram (w : B → G) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1) :
    (regularFactor w A).adjoint.comp (regularFactor w A) = regularPaired w A + 1 := by
  have hs := Linearization.positive_sqrt_gram (gramMatrix A) (gramMatrix_posSemidef A hA hnorm)
  rw [regularFactor, ContinuousLinearMap.adjoint_comp, ← RegularFactorization.rectLift_adjoint]
  rw [ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (rectLift _),
    ← RegularFactorization.rectLift_mul, hs, regularColumn_gram]
  simp_rw [select_gramMatrix, RegularFactorization.term_smul, RegularFactorization.term_add]
  simp only [← Finset.smul_sum, Finset.sum_add_distrib]
  have hid : (∑ a : B, ∑ b : B, term (if a = b then (1 : Matrix J J ℂ) else 0)
      ((w a)⁻¹ * w b)) = (Fintype.card B : ℝ) • (1 :
        RegularCoefficientEnergy.Hilbert G J →L[ℂ] RegularCoefficientEnergy.Hilbert G J) := by
    have ht (a b : B) : term (if a = b then (1 : Matrix J J ℂ) else 0) ((w a)⁻¹ * w b) =
        if a = b then (1 : RegularCoefficientEnergy.Hilbert G J →L[ℂ] _) else 0 := by
      split_ifs with hab
      · subst b; simp
      · simp
    simp_rw [ht]
    simp [Nat.cast_smul_eq_nsmul]
  rw [hid, smul_add, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  rw [add_comm]
  congr 1
  rw [regularPaired, NetPolynomial.regularPolynomial_eq_terms, Fintype.sum_prod_type]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← RegularFactorization.term_smul]
  congr 1
  ext j k
  simp [NetPolynomial.diagonalCoefficient, pairedCoefficient, Matrix.diagonal_apply,
    Matrix.smul_apply]


theorem regularPaired_selfAdjoint (w : B → G) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1) :
    IsSelfAdjoint (regularPaired w A) := by
  have h : IsSelfAdjoint (regularPaired w A + 1) := by
    change (regularPaired w A + 1).adjoint = regularPaired w A + 1
    rw [← regularFactor_gram w A hA hnorm]
    simp
  simpa only [add_sub_cancel_right] using h.sub (IsSelfAdjoint.one _)

theorem regularPaired_shifted_norm [Nonempty J] (w : B → G) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j) :
    ‖regularPaired w A + 1‖ = ‖regularPaired w A‖ + 1 := by
  have hsym : spectrum ℝ (-regularPaired w A) = spectrum ℝ (regularPaired w A) := by
    apply NetPolynomial.regularPolynomial_spectrum_neg _ _ e
    intro p j
    simp [pairedCoefficient, he]
  have hm : ‖regularPaired w A‖ ∈ spectrum ℝ (regularPaired w A) := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (regularPaired_selfAdjoint w A hA hnorm) with h | h
    · exact h
    · have hh : ‖regularPaired w A‖ ∈ spectrum ℝ (-regularPaired w A) := by
        rw [← spectrum.neg_eq]
        exact h
      rwa [hsym] at hh
  simpa using NetPolynomial.shifted_norm_of_norm_mem_spectrum (regularPaired w A) hm 1 zero_le_one

/-- Exact initial Gram identity at the genuine regular representation, with no doubling. -/
theorem regularEval_norm_sq [Nonempty J] (w : B → G) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j) (b₀ : B) :
    ‖regularEval w A b₀‖ ^ 2 = ‖regularPaired w A‖ + 1 := by
  rw [regularEval_norm, pow_two, ← ContinuousLinearMap.norm_adjoint_comp_self,
    regularFactor_gram w A hA hnorm, regularPaired_shifted_norm w A hA hnorm e he]

section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]

def finiteFactor (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ) :
    Matrix ((B × J) × V) (J × V) ℂ :=
  (CFC.sqrt (gramMatrix A) ⊗ₖ (1 : Matrix V V ℂ)) * FiniteSetFactorization.unitaryColumn U

def finiteEval (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ) (b₀ : B) :
    Matrix ((B × J) × V) ((B × J) × V) ℂ :=
  ∑ b, coefficient A b₀ b ⊗ₖ (U b : Matrix V V ℂ)

def finitePaired (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ) :
    Matrix (J × V) (J × V) ℂ :=
  ∑ a, ∑ b, Matrix.diagonal (fun j => (Fintype.card B : ℂ)⁻¹ * A j a b) ⊗ₖ
    ((U a : Matrix V V ℂ).conjTranspose * (U b : Matrix V V ℂ))

theorem finiteEval_eq (U : B → unitary (Matrix V V ℂ))
    (A : J → Matrix B B ℂ) (b₀ : B) :
    finiteEval U A b₀ = finiteFactor U A * (selector b₀ ⊗ₖ (1 : Matrix V V ℂ)) := by
  unfold finiteEval finiteFactor coefficient FiniteSetFactorization.unitaryColumn
  simp only [Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]

theorem finiteEval_norm (U : B → unitary (Matrix V V ℂ))
    (A : J → Matrix B B ℂ) (b₀ : B) :
    ‖finiteEval U A b₀‖ = ‖finiteFactor U A‖ := by
  rw [finiteEval_eq]
  apply Linearization.right_isometry_mul_norm
  simp [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    FiniteSetFactorization.selector_mul_adjoint]

theorem finiteColumn_gram (U : B → unitary (Matrix V V ℂ))
    (M : Matrix (B × J) (B × J) ℂ) :
    FiniteSetFactorization.evaluate U M =
      ∑ a, ∑ b, (selector a * M * (selector b).conjTranspose) ⊗ₖ
        ((U a : Matrix V V ℂ).conjTranspose * (U b : Matrix V V ℂ)) := by
  simp only [FiniteSetFactorization.evaluate, FiniteSetFactorization.unitaryColumn,
    Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  exact Finset.sum_comm

theorem finiteFactor_gram (U : B → unitary (Matrix V V ℂ))
    (A : J → Matrix B B ℂ) (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1) :
    (finiteFactor U A).conjTranspose * finiteFactor U A = finitePaired U A + 1 := by
  have hs := Linearization.positive_sqrt_gram (gramMatrix A) (gramMatrix_posSemidef A hA hnorm)
  rw [finiteFactor, Linearization.gram_factorization]
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, hs]
  rw [← FiniteSetFactorization.evaluate, finiteColumn_gram]
  simp_rw [select_gramMatrix, Matrix.smul_kronecker, Matrix.add_kronecker]
  simp only [← Finset.smul_sum, Finset.sum_add_distrib]
  have hid : (∑ a : B, ∑ b : B, (if a = b then (1 : Matrix J J ℂ) else 0) ⊗ₖ
      ((U a : Matrix V V ℂ).conjTranspose * (U b : Matrix V V ℂ))) =
        (Fintype.card B : ℝ) • (1 : Matrix (J × V) (J × V) ℂ) := by
    have ht (a b : B) : (if a = b then (1 : Matrix J J ℂ) else 0) ⊗ₖ
        ((U a : Matrix V V ℂ).conjTranspose * (U b : Matrix V V ℂ)) =
          if a = b then (1 : Matrix (J × V) (J × V) ℂ) else 0 := by
      split_ifs with hab
      · subst b; simp [← Matrix.star_eq_conjTranspose]
      · simp
    simp_rw [ht]
    simp [Nat.cast_smul_eq_nsmul]
  rw [hid, smul_add, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  rw [add_comm]
  congr 1
  unfold finitePaired
  simp only [Finset.smul_sum, ← Matrix.smul_kronecker]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ext j k
  simp [Matrix.diagonal_apply, Matrix.smul_apply]

theorem finiteEval_norm_sq (U : B → unitary (Matrix V V ℂ))
    (A : J → Matrix B B ℂ) (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (b₀ : B) : ‖finiteEval U A b₀‖ ^ 2 = ‖finitePaired U A + 1‖ := by
  rw [finiteEval_norm, pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    finiteFactor_gram U A hA hnorm]

theorem finitePaired_selfAdjoint (U : B → unitary (Matrix V V ℂ))
    (A : J → Matrix B B ℂ) (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1) :
    IsSelfAdjoint (finitePaired U A) := by
  have h : IsSelfAdjoint (finitePaired U A + 1) := by
    change (finitePaired U A + 1).conjTranspose = finitePaired U A + 1
    rw [← finiteFactor_gram U A hA hnorm]
    simp
  simpa only [add_sub_cancel_right] using h.sub (IsSelfAdjoint.one _)

theorem finitePaired_negation_reindex (U : B → unitary (Matrix V V ℂ))
    (A : J → Matrix B B ℂ) (e : J ≃ J) (he : ∀ j, A (e j) = -A j) :
    (finitePaired U A).submatrix (Equiv.prodCongr e (Equiv.refl V))
      (Equiv.prodCongr e (Equiv.refl V)) = -finitePaired U A := by
  ext ⟨j,x⟩ ⟨k,y⟩
  simp only [finitePaired, Matrix.submatrix_apply, Equiv.prodCongr_apply,
    Matrix.sum_apply, Matrix.kronecker_apply, Matrix.diagonal_apply, Matrix.neg_apply]
  by_cases h : j = k
  · subst k
    simp [he]
  · simp [h]

theorem finitePaired_shifted_norm [Nonempty J] [Nonempty V]
    (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j) :
    ‖finitePaired U A + 1‖ = ‖finitePaired U A‖ + 1 := by
  letI : CStarAlgebra (Matrix (J × V) (J × V) ℂ) := { }
  have hsym : spectrum ℝ (-finitePaired U A) = spectrum ℝ (finitePaired U A) := by
    let q := MatrixNormReindex.reindexStarAlgEquiv (Equiv.prodCongr e (Equiv.refl V)).symm
    have hq : q (finitePaired U A) = -finitePaired U A := finitePaired_negation_reindex U A e he
    rw [← hq]
    exact AlgEquiv.spectrum_eq (q.toAlgEquiv.restrictScalars ℝ) _
  have hm : ‖finitePaired U A‖ ∈ spectrum ℝ (finitePaired U A) := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (finitePaired_selfAdjoint U A hA hnorm) with h | h
    · exact h
    · have hh : ‖finitePaired U A‖ ∈ spectrum ℝ (-finitePaired U A) := by
        rw [← spectrum.neg_eq]
        exact h
      rwa [hsym] at hh
  apply le_antisymm
  · simpa using norm_add_le (finitePaired U A) 1
  · have hh : ‖finitePaired U A‖ + 1 ∈ spectrum ℝ (finitePaired U A + 1) := by
      rw [← map_one (algebraMap ℝ (Matrix (J × V) (J × V) ℂ)), ← spectrum.add_singleton_eq]
      exact Set.add_mem_add hm (Set.mem_singleton 1)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖finitePaired U A‖ + 1)]
      using spectrum.norm_le_norm_of_mem hh

/-- Exact initial Gram identity at every finite unitary representation. -/
theorem finiteEval_norm_sq_symmetric [Nonempty J] [Nonempty V]
    (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j) (b₀ : B) :
    ‖finiteEval U A b₀‖ ^ 2 = ‖finitePaired U A‖ + 1 := by
  rw [finiteEval_norm_sq U A hA hnorm, finitePaired_shifted_norm U A hA hnorm e he]

/-- Swapping the two tensor coordinates identifies the paired matrix with
exactly the finite direct sum of the scalar observable tests. -/
theorem finitePaired_swap (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ) :
    (finitePaired U A).submatrix (Equiv.prodComm V J) (Equiv.prodComm V J) =
      NetPolynomial.finitePolynomial
        (fun p : B × B => (U p.1 : Matrix V V ℂ).conjTranspose * (U p.2 : Matrix V V ℂ))
        (pairedCoefficient A) := by
  ext ⟨x,j⟩ ⟨y,k⟩
  simp only [finitePaired, NetPolynomial.finitePolynomial, Fintype.sum_prod_type,
    Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.sum_apply,
    Matrix.kronecker_apply, NetPolynomial.diagonalCoefficient, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

/-- The finite paired polynomial has exactly the maximum test norm. -/
theorem finitePaired_norm (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ) :
    ‖finitePaired U A‖ =
      ‖fun j => ∑ a, ∑ b, ((Fintype.card B : ℂ)⁻¹ * A j a b) •
        ((U a : Matrix V V ℂ).conjTranspose * (U b : Matrix V V ℂ))‖ := by
  rw [← MatrixNormReindex.submatrix_equiv_norm (Equiv.prodComm V J) (finitePaired U A),
    finitePaired_swap, NetPolynomial.finitePolynomial_norm]
  simp only [Fintype.sum_prod_type, pairedCoefficient]

end Finite

section Collection
variable [Nonempty J]

def collectedCoefficient (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) (g : G) :
    Matrix (B × J) (B × J) ℂ := ∑ b, if w b = g then coefficient A b₀ b else 0

/-- The actual polynomial record to which subsequent support reductions apply. -/
def polynomial (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    PolynomialReduction.Polynomial G where
  Index := B × J
  fintype := inferInstance
  decEq := inferInstance
  nonempty := inferInstance
  support := Finset.univ.image w
  coefficient := collectedCoefficient w A b₀

@[simp] theorem polynomial_dimension (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    Fintype.card (polynomial w A b₀).Index = Fintype.card B * Fintype.card J :=
  Fintype.card_prod _ _

@[simp] theorem polynomial_support (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    (polynomial w A b₀).support = Finset.univ.image w := rfl

private theorem collection_sum {E : Type*} [AddCommMonoid E]
    (w : B → G) (f : B → G → E) :
    ∑ g ∈ Finset.univ.image w, ∑ b, (if w b = g then f b g else 0) = ∑ b, f b (w b) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_ite_eq]
  simp

@[simp] theorem polynomial_regularEval (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    (polynomial w A b₀).regularEval = regularEval w A b₀ := by
  change RegularCoefficientEnergy.regularPolynomial _ _ = _
  rw [RegularFactorization.polynomial_eq]
  simp only [polynomial, collectedCoefficient]
  have ht (g : G) : term (∑ b, if w b = g then coefficient A b₀ b else 0) g =
      ∑ b, if w b = g then term (coefficient A b₀ b) g else 0 := by
    simp only [term, RegularFactorization.rectLift_sum, ContinuousLinearMap.finset_sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  simp_rw [ht]
  exact collection_sum w (fun b g => term (coefficient A b₀ b) g)

@[simp] theorem polynomial_finiteEval {V : Type*} [Fintype V] [DecidableEq V]
    (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B)
    (π : G →* unitary (Matrix V V ℂ)) :
    (polynomial w A b₀).finiteEval π = finiteEval (fun b => π (w b)) A b₀ := by
  ext x y
  change (∑ g ∈ Finset.univ.image w, collectedCoefficient w A b₀ g ⊗ₖ
    (π g : Matrix V V ℂ)) x y = (finiteEval (fun b => π (w b)) A b₀) x y
  rcases x with ⟨x,x'⟩
  rcases y with ⟨y,y'⟩
  simp only [finiteEval, Matrix.sum_apply, Matrix.kronecker_apply, collectedCoefficient,
    Finset.sum_mul, Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul]
  exact collection_sum w (fun b g => coefficient A b₀ b x y * (π g : Matrix V V ℂ) x' y')

/-- Initial backward transfer with its exact additive constant one. All norm
identities refer to the coefficients constructed above and are proved internally. -/
theorem initial_backward_transfer {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (w : B → G) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j) (b₀ : B)
    (π : G →* unitary (Matrix V V ℂ)) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hQ : ‖(polynomial w A b₀).finiteEval π‖ ≤ (1+ε) * ‖(polynomial w A b₀).regularEval‖) :
    ‖finitePaired (fun b => π (w b)) A‖ - ‖regularPaired w A‖ ≤
      3 * ε * (1 + ‖regularPaired w A‖) := by
  rw [polynomial_finiteEval, polynomial_regularEval] at hQ
  exact Linearization.initial_backward_error
    ‖finitePaired (fun b => π (w b)) A‖ ‖regularPaired w A‖
    ‖finiteEval (fun b => π (w b)) A b₀‖ ‖regularEval w A b₀‖ ε
    (norm_nonneg _) (norm_nonneg _) hε hε1
    (finiteEval_norm_sq_symmetric _ A hA hnorm e he b₀)
    (regularEval_norm_sq w A hA hnorm e he b₀) hQ

/-- The manuscript's initial relative-error factor `3(1+1/rho)` for the
actual, undoubled polynomial. -/
theorem initial_relative_transfer {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (w : B → G) (A : J → Matrix B B ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hnorm : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j) (b₀ : B)
    (π : G →* unitary (Matrix V V ℂ)) (ε ρ : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hr : ρ ≤ ‖regularPaired w A‖)
    (hQ : ‖(polynomial w A b₀).finiteEval π‖ ≤ (1+ε) * ‖(polynomial w A b₀).regularEval‖) :
    ‖finitePaired (fun b => π (w b)) A‖ ≤
      (1 + 3 * (1 + 1/ρ) * ε) * ‖regularPaired w A‖ := by
  have hb := initial_backward_transfer w A hA hnorm e he b₀ π ε hε hε1 hQ
  have hs : 1 ≤ ‖regularPaired w A‖ / ρ := (le_div_iff₀ hρ).mpr (by simpa using hr)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3*ε by positivity)
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith
end Collection

end Construction

section Nets
open FreeModel FiniteRealization
variable {K n : ℕ}
local instance (tests : Finset (ObservableSpace (Branch K n))) : DecidableEq tests := Classical.decEq _

/-- The generic paired polynomial is exactly the manuscript's test polynomial. -/
theorem net_regularPaired_eq (tests : Finset (ObservableSpace (Branch K n))) :
    regularPaired (branchWord (K := K) (n := n)) (fun j : tests => observableMatrix j.val) =
      NetPolynomial.netRegularPolynomial tests := by
  classical
  unfold regularPaired NetPolynomial.netRegularPolynomial NetPolynomial.regularTestPolynomial
  congr 1
  funext p j
  simp [pairedCoefficient, NetPolynomial.testCoefficient, Branch, one_div]

set_option maxHeartbeats 1000000 in
/-- Construction of the initial polynomial with the exact undoubled coefficient
size and individual-word support, specialized to an actual symmetric observable net. -/
theorem exists_initial_net_polynomial (hK : 0 < K)
    (tests : Finset (ObservableSpace (Branch K n))) (hne : tests.Nonempty)
    (hnorm : ∀ x ∈ tests, ‖x‖ = 1) (hsymm : ∀ x ∈ tests, -x ∈ tests) :
    ∃ Q : PolynomialReduction.Polynomial (ProductFreeGroup K n),
      Fintype.card Q.Index = tests.card * K^n ∧
      Q.support = Finset.univ.image (branchWord (K := K) (n := n)) ∧
      ‖Q.regularEval‖ ^ 2 = ‖NetPolynomial.netRegularPolynomial tests‖ + 1 ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
        (π : ProductFreeGroup K n →* unitary (Matrix V V ℂ)),
        ‖Q.finiteEval π‖ ^ 2 =
          ‖finitePaired (fun b => π (branchWord b)) (fun j : tests => observableMatrix j.val)‖ + 1 := by
  classical
  letI : Nonempty tests := hne.to_subtype
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  let A : tests → Matrix (Branch K n) (Branch K n) ℂ := fun j => observableMatrix j.val
  let b₀ : Branch K n := fun _ => ⟨0,hK⟩
  have hA : ∀ j, (A j).IsHermitian := fun j => observableMatrix_isHermitian j.val
  have hAn : ∀ j, ‖A j‖ ≤ 1 := by
    intro j
    have hhs : AdjointPurity.hsLength (A j) = 1 := by
      rw [← observable_norm_eq_hsLength]
      exact hnorm j.val j.property
    exact (norm_le_hsLength (A j) (hA j)).trans hhs.le
  let e := NetPolynomial.netNegationEquiv tests hsymm
  have he : ∀ j, A (e j) = -A j := fun _ => rfl
  refine ⟨polynomial branchWord A b₀, ?_, rfl, ?_, ?_⟩
  · simp only [polynomial_dimension, Fintype.card_coe, Branch, Fintype.card_fun,
      Fintype.card_fin, Nat.mul_comm]
  · rw [polynomial_regularEval, regularEval_norm_sq branchWord A hA hAn e he b₀]
    rw [show regularPaired branchWord A = NetPolynomial.netRegularPolynomial tests from
      net_regularPaired_eq tests]
  · intro V _ _ _ π
    rw [polynomial_finiteEval, finiteEval_norm_sq_symmetric _ A hA hAn e he b₀]

end Nets


section ShortWords

/-- Relabeling generators never increases reduced word length. -/
theorem norm_freeGroup_map_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (w : FreeGroup α) : FreeGroup.norm (FreeGroup.map f w) ≤ FreeGroup.norm w := by
  calc
    FreeGroup.norm (FreeGroup.map f w) =
        FreeGroup.norm (FreeGroup.mk (w.toWord.map fun x => (f x.1,x.2))) := by
      rw [← FreeGroup.map.mk, FreeGroup.mk_toWord]
    _ ≤ _ := FreeGroup.norm_mk_le.trans (by simp [FreeGroup.norm])

/-- The actual logarithmic-length embedding with the target generators named
`Fin 2`, as required by the one-factor support and linear-polynomial APIs. -/
def shortEmbedding (K : ℕ) (hK : 2 ≤ K) : FreeGroup (Fin K) →* FreeGroup (Fin 2) :=
  (FreeGroup.freeGroupCongr finTwoEquiv.symm).toMonoidHom.comp (FreeEmbedding.logarithmicEmbedding K hK)

theorem shortEmbedding_injective (K : ℕ) (hK : 2 ≤ K) :
    Function.Injective (shortEmbedding K hK) :=
  (FreeGroup.freeGroupCongr finTwoEquiv.symm).injective.comp (FreeEmbedding.logarithmicEmbedding_injective K hK)

def shortWord (K : ℕ) (hK : 2 ≤ K) (a : Fin K) : FreeGroup (Fin 2) :=
  shortEmbedding K hK (FreeGroup.of a)

theorem shortWord_norm_le (K : ℕ) (hK : 2 ≤ K) (a : Fin K) :
    FreeGroup.norm (shortWord K hK a) ≤ 2 * Nat.log 2 (K-1) + 1 := by
  exact (norm_freeGroup_map_le finTwoEquiv.symm
    (FreeEmbedding.logarithmicEmbedding K hK (FreeGroup.of a))).trans
      (FreeEmbedding.norm_logarithmicEmbedding_of_le K hK a)

def shortProductEmbedding (K n : ℕ) (hK : 2 ≤ K) :
    FreeModel.ProductFreeGroup K n →* (Fin n → FreeGroup (Fin 2)) where
  toFun g i := shortEmbedding K hK (g i)
  map_one' := by ext i; exact map_one _
  map_mul' g h := by ext i; exact map_mul _ _ _

theorem shortProductEmbedding_injective (K n : ℕ) (hK : 2 ≤ K) :
    Function.Injective (shortProductEmbedding K n hK) := by
  intro g h hgh
  funext i
  exact shortEmbedding_injective K hK (congrFun hgh i)

@[simp] theorem shortProductEmbedding_branchWord (K n : ℕ) (hK : 2 ≤ K)
    (a : FreeModel.Branch K n) :
    shortProductEmbedding K n hK (FreeModel.branchWord a) = fun i => shortWord K hK (a i) := rfl

end ShortWords

end Nonadditivity.InitialNetReduction
