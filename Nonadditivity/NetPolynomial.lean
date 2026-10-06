/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.CollinsYounProduct
import Nonadditivity.ObservableDimension
import Nonadditivity.PrescribedTest
import Nonadditivity.RegularFactorization

/-! # A finite family of observable tests as one actual polynomial

Diagonal coefficient matrices give a direct sum on the genuine vector-valued
regular Hilbert space. Its norm is the maximum of the scalar test norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Nonadditivity.NetPolynomial

open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator
open RegularCoefficientEnergy (CoefficientSpace)

section Slices
variable {G J : Type*} [Fintype J] [DecidableEq J]

/-- One scalar coordinate of a vector-valued square-summable function. -/
def slice (j : J) (f : RegularCoefficientEnergy.Hilbert G J) : FreeModel.Hilbert G :=
  ⟨fun g => f g j, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => ?_)
      (by simpa using f.property.summable (by norm_num))
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖f g i‖) (Finset.mem_univ j)⟩

omit [DecidableEq J] in
@[simp] theorem slice_apply (j : J) (f : RegularCoefficientEnergy.Hilbert G J) (g : G) :
    slice j f g = f g j := rfl

omit [DecidableEq J] in
theorem slice_energy (f : RegularCoefficientEnergy.Hilbert G J) :
    ‖f‖ ^ 2 = ∑ j, ‖slice j f‖ ^ 2 := by
  rw [MatrixRegularRestriction.norm_sq]
  simp_rw [EuclideanSpace.norm_sq_eq, MatrixRegularRestriction.norm_sq]
  exact Summable.tsum_finsetSum (fun j _ => by
    simpa using (slice j f).property.summable (by norm_num))

/-- Include one scalar block isometrically in the coefficient direct sum. -/
def embed (j : J) (f : FreeModel.Hilbert G) : RegularCoefficientEnergy.Hilbert G J :=
  ⟨fun g => EuclideanSpace.single j (f g), by
    apply memℓp_gen
    simpa using f.property.summable (by norm_num)⟩

@[simp] theorem slice_embed (j k : J) (f : FreeModel.Hilbert G) :
    slice j (embed k f) = if j = k then f else 0 := by
  ext g
  by_cases h : j = k <;> simp [slice, embed, EuclideanSpace.single_apply, h]

theorem embed_norm (j : J) (f : FreeModel.Hilbert G) : ‖embed j f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [MatrixRegularRestriction.norm_sq, MatrixRegularRestriction.norm_sq]
  simp [embed]

omit [DecidableEq J] in
theorem slice_norm_le (j : J) (f : RegularCoefficientEnergy.Hilbert G J) :
    ‖slice j f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [slice_energy]
  exact Finset.single_le_sum (fun i _ => sq_nonneg ‖slice i f‖) (Finset.mem_univ j)
end Slices

section Polynomial
variable {G J I : Type*} [Group G] [Fintype J] [DecidableEq J] [Fintype I]

/-- The diagonal coefficient `diag_j a_{ij}`. -/
def diagonalCoefficient (a : I → J → ℂ) (i : I) : Matrix J J ℂ :=
  Matrix.diagonal (a i)

/-- The literal matrix-coefficient regular polynomial on `ℓ²(G;ℂ^J)`. -/
def regularPolynomial (w : I → G) (a : I → J → ℂ) :
    RegularCoefficientEnergy.Hilbert G J →L[ℂ] RegularCoefficientEnergy.Hilbert G J :=
  MatrixRegularRestriction.coefficientPolynomial w
    (fun i => RegularCoefficientEnergy.coefficientOperator (diagonalCoefficient a i))

def scalarPolynomial (w : I → G) (a : I → J → ℂ) (j : J) :
    FreeModel.Hilbert G →L[ℂ] FreeModel.Hilbert G :=
  ∑ i, a i j • FreeModel.leftRegular (w i)

omit [Fintype I] in
@[simp] theorem diagonalCoefficient_apply (a : I → J → ℂ) (i : I)
    (x : CoefficientSpace J) (j : J) :
    RegularCoefficientEnergy.coefficientOperator (diagonalCoefficient a i) x j =
      a i j * x j := by
  change ((Matrix.diagonal (a i)) *ᵥ x.ofLp) j = _
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- Coordinate compression is exactly the requested scalar test. -/
theorem slice_regularPolynomial (w : I → G) (a : I → J → ℂ)
    (j : J) (f : RegularCoefficientEnergy.Hilbert G J) :
    slice j (regularPolynomial w a f) = scalarPolynomial w a j (slice j f) := by
  ext g
  simp only [slice_apply, regularPolynomial, MatrixRegularRestriction.coefficientPolynomial_apply,
    WithLp.ofLp_sum, Finset.sum_apply, diagonalCoefficient_apply, scalarPolynomial, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, FreeModel.leftRegular_apply, smul_eq_mul]

theorem regularPolynomial_norm_le (w : I → G) (a : I → J → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ j, ‖scalarPolynomial w a j‖ ≤ C) :
    ‖regularPolynomial w a‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [slice_energy, mul_pow, slice_energy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [slice_regularPolynomial, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((scalarPolynomial w a j).le_opNorm (slice j f)).trans
    (mul_le_mul_of_nonneg_right (h j) (norm_nonneg _))

/-- No test norm exceeds the norm of the combined polynomial. -/
theorem scalarPolynomial_norm_le (w : I → G) (a : I → J → ℂ) (j : J) :
    ‖scalarPolynomial w a j‖ ≤ ‖regularPolynomial w a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have h := (slice_norm_le j (regularPolynomial w a (embed j f))).trans
    ((regularPolynomial w a).le_opNorm (embed j f))
  simpa [slice_regularPolynomial, slice_embed, embed_norm] using h

/-- The combined operator norm is exactly the finite maximum of test norms,
written as the canonical supremum norm on the finite family. -/
theorem regularPolynomial_norm (w : I → G) (a : I → J → ℂ) :
    ‖regularPolynomial w a‖ = ‖fun j => scalarPolynomial w a j‖ := by
  apply le_antisymm
  · exact regularPolynomial_norm_le w a (norm_nonneg _) (norm_le_pi_norm _)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (scalarPolynomial_norm_le w a)
end Polynomial

section Tests
open FreeModel FiniteRealization
variable {K n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The coefficients in the manuscript, with the branch pair as term index. -/
def testCoefficient (A : J → Matrix (Branch K n) (Branch K n) ℂ)
    (p : Branch K n × Branch K n) (j : J) : ℂ := (1 / (K : ℂ)^n) * A j p.1 p.2

def testWord (p : Branch K n × Branch K n) : ProductFreeGroup K n :=
  (branchWord p.1)⁻¹ * branchWord p.2

def regularTestPolynomial (A : J → Matrix (Branch K n) (Branch K n) ℂ) :=
  regularPolynomial testWord (testCoefficient A)

omit [Fintype J] [DecidableEq J] in
@[simp] theorem scalar_testPolynomial
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (j : J) :
    scalarPolynomial testWord (testCoefficient A) j = gamma (A j) := by
  simp only [scalarPolynomial, testCoefficient, testWord, gamma, Fintype.sum_prod_type,
    Finset.smul_sum, mul_smul]

theorem regularTestPolynomial_norm (A : J → Matrix (Branch K n) (Branch K n) ℂ) :
    ‖regularTestPolynomial A‖ = ‖fun j => gamma (A j)‖ := by
  rw [regularTestPolynomial, regularPolynomial_norm]
  simp only [scalar_testPolynomial]

theorem test_norm_le (A : J → Matrix (Branch K n) (Branch K n) ℂ) (j : J) :
    freeNorm (A j) ≤ ‖regularTestPolynomial A‖ := by
  simpa only [scalar_testPolynomial, freeNorm] using
    scalarPolynomial_norm_le testWord (testCoefficient A) j

/-- The actual combined regular polynomial satisfies the proved Collins--Youn
bound for every finite family of traceless unit Hilbert--Schmidt tests. -/
theorem regularTestPolynomial_norm_le (hK : 2 ≤ K) (hn : 1 ≤ n)
    (A : J → Matrix (Branch K n) (Branch K n) ℂ)
    (htrace : ∀ j, (A j).trace = 0) (hhs : ∀ j, AdjointPurity.hsLength (A j) = 1) :
    ‖regularTestPolynomial A‖ ≤ c K n := by
  apply regularPolynomial_norm_le _ _ (c_pos hK hn).le
  intro j
  rw [scalar_testPolynomial]
  exact freeNorm_le_of_collinsYoun (CollinsYounProduct.collinsYounBound hK hn)
    (A j) (htrace j) (hhs j)
end Tests

section FiniteMatrices
variable {J V I : Type*} [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype I]

/-- Finite direct sums form an injective star-algebra homomorphism. -/
def blockDiagonalHom :
    (J → Matrix V V ℂ) →⋆ₐ[ℂ] Matrix (V × J) (V × J) ℂ where
  toFun := Matrix.blockDiagonal
  map_zero' := Matrix.blockDiagonal_zero
  map_one' := Matrix.blockDiagonal_one
  map_add' := Matrix.blockDiagonal_add
  map_mul' := Matrix.blockDiagonal_mul
  commutes' z := by
    ext ⟨x,j⟩ ⟨y,k⟩
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal_smul,
      Matrix.blockDiagonal_one]
  map_star' A := by
    exact (Matrix.blockDiagonal_conjTranspose A).symm

/-- The actual Euclidean operator norm of a finite block diagonal matrix. -/
theorem blockDiagonal_norm (A : J → Matrix V V ℂ) :
    ‖Matrix.blockDiagonal A‖ = ‖A‖ := by
  letI : CStarAlgebra (Matrix V V ℂ) := { }
  letI : CStarAlgebra (Matrix (V × J) (V × J) ℂ) := { }
  exact NonUnitalStarAlgHom.norm_map (blockDiagonalHom (J := J) (V := V))
    Matrix.blockDiagonal_injective A

/-- Finite-dimensional evaluation of exactly the same diagonal coefficients. -/
def finitePolynomial (U : I → Matrix V V ℂ) (a : I → J → ℂ) :
    Matrix (V × J) (V × J) ℂ :=
  ∑ i, Matrix.kronecker (U i) (diagonalCoefficient a i)

omit [Fintype J] [Fintype V] [DecidableEq V] in
/-- The coefficient polynomial is literally the direct sum of scalar tests;
the tensor factors are written with the representation coordinate first. -/
theorem finitePolynomial_eq_blockDiagonal (U : I → Matrix V V ℂ) (a : I → J → ℂ) :
    finitePolynomial U a = Matrix.blockDiagonal (fun j => ∑ i, a i j • U i) := by
  ext ⟨x,j⟩ ⟨y,k⟩
  simp only [finitePolynomial, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply,
    diagonalCoefficient, Matrix.diagonal_apply, Matrix.blockDiagonal_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : j = k
  · subst k
    simp only [ite_true]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  · simp [h]

theorem finitePolynomial_norm (U : I → Matrix V V ℂ) (a : I → J → ℂ) :
    ‖finitePolynomial U a‖ = ‖fun j => ∑ i, a i j • U i‖ := by
  rw [finitePolynomial_eq_blockDiagonal, blockDiagonal_norm]

omit [Fintype J] [Fintype V] [DecidableEq V] in
/-- Self-adjoint test blocks give an actual self-adjoint combined matrix. -/
theorem blockDiagonal_isHermitian (A : J → Matrix V V ℂ)
    (hA : ∀ j, (A j).IsHermitian) : (Matrix.blockDiagonal A).IsHermitian := by
  change (Matrix.blockDiagonal A).conjTranspose = _
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext j
  exact (hA j).eq

omit [Fintype J] [Fintype V] [DecidableEq V] in
/-- Negation-paired tests make the combined matrix similar to its negative
by a literal permutation of coefficient coordinates. -/
theorem blockDiagonal_negation_reindex (A : J → Matrix V V ℂ)
    (e : J ≃ J) (he : ∀ j, A (e j) = - A j) :
    (Matrix.blockDiagonal A).submatrix (Equiv.prodCongr (Equiv.refl V) e)
      (Equiv.prodCongr (Equiv.refl V) e) = - Matrix.blockDiagonal A := by
  ext ⟨x,j⟩ ⟨y,k⟩
  simp only [Matrix.submatrix_apply, Equiv.prodCongr_apply,
    Matrix.blockDiagonal_apply, Matrix.neg_apply]
  by_cases h : j = k
  · subst k
    simp [he]
  · simp [h]

/-- Exact spectral symmetry for the finite negation-paired polynomial. -/
theorem blockDiagonal_spectrum_neg (A : J → Matrix V V ℂ)
    (e : J ≃ J) (he : ∀ j, A (e j) = - A j) :
    spectrum ℂ (-Matrix.blockDiagonal A) = spectrum ℂ (Matrix.blockDiagonal A) := by
  let q := MatrixNormReindex.reindexStarAlgEquiv
    (Equiv.prodCongr (Equiv.refl V) e).symm
  have hq : q (Matrix.blockDiagonal A) = - Matrix.blockDiagonal A :=
    blockDiagonal_negation_reindex A e he
  rw [← hq]
  exact AlgEquiv.spectrum_eq q.toAlgEquiv _
end FiniteMatrices

section RegularSymmetry
variable {G J I : Type*} [Group G] [Fintype J] [DecidableEq J] [Fintype I]

/-- Reindex the finite coefficient coordinate inside the actual regular Hilbert space. -/
def permutationFunction (e : J ≃ J) (f : RegularCoefficientEnergy.Hilbert G J) :
    RegularCoefficientEnergy.Hilbert G J :=
  ⟨fun g => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm (f g), by
    apply memℓp_gen
    simpa only [LinearIsometryEquiv.norm_map] using f.property.summable (by norm_num)⟩

omit [Group G] [DecidableEq J] in
@[simp] theorem permutationFunction_apply (e : J ≃ J)
    (f : RegularCoefficientEnergy.Hilbert G J) (g : G) (j : J) :
    permutationFunction e f g j = f g (e j) := rfl

def permutationIsometry (e : J ≃ J) :
    RegularCoefficientEnergy.Hilbert G J ≃ₗᵢ[ℂ] RegularCoefficientEnergy.Hilbert G J where
  toFun := permutationFunction e
  invFun := permutationFunction e.symm
  left_inv := by intro f; ext g j; simp
  right_inv := by intro f; ext g j; simp
  map_add' := by intro f h; ext g j; rfl
  map_smul' := by intro z f; ext g j; rfl
  norm_map' := by
    intro f
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [MatrixRegularRestriction.norm_sq, MatrixRegularRestriction.norm_sq]
    exact tsum_congr (fun g => congrArg (fun x : ℝ => x^2)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map (f g)))

omit [Group G] [DecidableEq J] in
@[simp] theorem permutationIsometry_apply (e : J ≃ J)
    (f : RegularCoefficientEnergy.Hilbert G J) (g : G) (j : J) :
    permutationIsometry e f g j = f g (e j) := rfl

omit [Group G] [DecidableEq J] in
@[simp] theorem permutationIsometry_symm_apply (e : J ≃ J)
    (f : RegularCoefficientEnergy.Hilbert G J) (g : G) (j : J) :
    (permutationIsometry e).symm f g j = f g (e.symm j) := rfl

/-- Negation pairing acts by genuine unitary conjugation on the regular polynomial. -/
theorem regularPolynomial_negation_conjugate (w : I → G) (a : I → J → ℂ)
    (e : J ≃ J) (he : ∀ i j, a i (e j) = -a i j) :
    (permutationIsometry (G := G) e).conjStarAlgEquiv (regularPolynomial w a) =
      -regularPolynomial w a := by
  ext f g j
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, permutationIsometry_apply,
    regularPolynomial, MatrixRegularRestriction.coefficientPolynomial_apply,
    WithLp.ofLp_sum, Finset.sum_apply, diagonalCoefficient_apply,
    permutationIsometry_symm_apply, Equiv.symm_apply_apply, he,
    ContinuousLinearMap.neg_apply, lp.coeFn_neg, Pi.neg_apply, WithLp.ofLp_neg]
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- Exact spectral symmetry holds in the actual infinite regular representation. -/
theorem regularPolynomial_spectrum_neg (w : I → G) (a : I → J → ℂ)
    (e : J ≃ J) (he : ∀ i j, a i (e j) = -a i j) :
    spectrum ℝ (-regularPolynomial w a) = spectrum ℝ (regularPolynomial w a) := by
  rw [← regularPolynomial_negation_conjugate w a e he]
  exact AlgEquiv.spectrum_eq
    ((permutationIsometry (G := G) e).conjStarAlgEquiv.toAlgEquiv.restrictScalars ℝ) _
end RegularSymmetry

section RegularSelfAdjoint
variable {G J I : Type*} [Group G] [DecidableEq G] [Fintype J] [DecidableEq J] [Fintype I]

omit [DecidableEq G] in
theorem regularPolynomial_eq_terms (w : I → G) (a : I → J → ℂ) :
    regularPolynomial w a = ∑ i, RegularFactorization.term (diagonalCoefficient a i) (w i) := by
  apply Finset.sum_congr rfl
  intro i _
  ext f g j
  rfl

/-- Adjoint of the literal matrix-coefficient regular polynomial. -/
theorem regularPolynomial_adjoint (w : I → G) (a : I → J → ℂ) :
    (regularPolynomial w a).adjoint =
      ∑ i, RegularFactorization.term (diagonalCoefficient a i).conjTranspose (w i)⁻¹ := by
  rw [regularPolynomial_eq_terms]
  simp only [map_sum, RegularFactorization.term_adjoint]
end RegularSelfAdjoint

section SelfAdjointTests
open FreeModel
variable {K n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- Every Hermitian test produces a self-adjoint block; the combined regular
operator is therefore self-adjoint on the actual infinite Hilbert space. -/
theorem regularTestPolynomial_selfAdjoint
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (hA : ∀ j, (A j).IsHermitian) :
    IsSelfAdjoint (regularTestPolynomial A) := by
  classical
  change (regularTestPolynomial A).adjoint = _
  rw [regularTestPolynomial, regularPolynomial_adjoint, regularPolynomial_eq_terms]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hc : (diagonalCoefficient (testCoefficient A) (b,a)).conjTranspose =
      diagonalCoefficient (testCoefficient A) (a,b) := by
    ext j k
    simp only [Matrix.conjTranspose_apply, diagonalCoefficient, Matrix.diagonal_apply]
    by_cases h : j = k
    · subst k
      simp only [ite_true, testCoefficient, star_mul, star_div₀, star_one, star_pow,
        star_natCast]
      have hh := congrArg (fun M : Matrix (Branch K n) (Branch K n) ℂ => M a b) (hA j).eq
      simpa only [Matrix.conjTranspose_apply, mul_comm] using congrArg
        (fun z : ℂ => (1 / (K : ℂ)^n) * z) hh
    · simp [h, Ne.symm h]
  rw [hc]
  congr 1

/-- Negation-paired observable tests give exact spectral symmetry without
introducing a doubled coefficient space. -/
theorem regularTestPolynomial_spectrum_neg
    (A : J → Matrix (Branch K n) (Branch K n) ℂ)
    (e : J ≃ J) (he : ∀ j, A (e j) = - A j) :
    spectrum ℝ (-regularTestPolynomial A) = spectrum ℝ (regularTestPolynomial A) := by
  apply regularPolynomial_spectrum_neg _ _ e
  intro p j
  simp only [testCoefficient, he, Matrix.neg_apply, mul_neg]
end SelfAdjointTests

section ObservableNets
open FreeModel FiniteRealization
variable {K n : ℕ}

/-- The literal combined regular polynomial of a finite observable net. -/
def netRegularPolynomial (tests : Finset (ObservableSpace (Branch K n))) :
    RegularCoefficientEnergy.Hilbert (ProductFreeGroup K n) tests →L[ℂ]
      RegularCoefficientEnergy.Hilbert (ProductFreeGroup K n) tests := by
  classical
  exact regularTestPolynomial (fun j : tests => observableMatrix j.val)

/-- Negation symmetry of the net gives an actual permutation of its test indices. -/
def netNegationEquiv (tests : Finset (ObservableSpace (Branch K n)))
    (hsymm : ∀ x ∈ tests, -x ∈ tests) : tests ≃ tests where
  toFun x := ⟨-x.val, hsymm x.val x.property⟩
  invFun x := ⟨-x.val, hsymm x.val x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem netRegularPolynomial_norm_le (hK : 2 ≤ K) (hn : 1 ≤ n)
    (tests : Finset (ObservableSpace (Branch K n)))
    (hnorm : ∀ x ∈ tests, ‖x‖ = 1) : ‖netRegularPolynomial tests‖ ≤ c K n := by
  classical
  apply regularTestPolynomial_norm_le hK hn
  · intro j
    exact observableMatrix_trace_zero j.val
  · intro j
    rw [← observable_norm_eq_hsLength]
    exact hnorm j.val j.property

theorem netRegularPolynomial_test_le (tests : Finset (ObservableSpace (Branch K n)))
    (x : ObservableSpace (Branch K n)) (hx : x ∈ tests) :
    freeNorm (observableMatrix x) ≤ ‖netRegularPolynomial tests‖ := by
  classical
  exact test_norm_le (fun j : tests => observableMatrix j.val) ⟨x,hx⟩

theorem netRegularPolynomial_selfAdjoint (tests : Finset (ObservableSpace (Branch K n))) :
    IsSelfAdjoint (netRegularPolynomial tests) := by
  classical
  exact regularTestPolynomial_selfAdjoint _ (fun j => observableMatrix_isHermitian j.val)

theorem netRegularPolynomial_spectrum_neg (tests : Finset (ObservableSpace (Branch K n)))
    (hsymm : ∀ x ∈ tests, -x ∈ tests) :
    spectrum ℝ (-netRegularPolynomial tests) = spectrum ℝ (netRegularPolynomial tests) := by
  classical
  apply regularTestPolynomial_spectrum_neg _ (netNegationEquiv tests hsymm)
  intro j
  rfl

/-- The symmetric test net has its positive norm endpoint in its real spectrum. -/
theorem netRegularPolynomial_norm_mem_spectrum (tests : Finset (ObservableSpace (Branch K n)))
    (hne : tests.Nonempty) (hsymm : ∀ x ∈ tests, -x ∈ tests) :
    ‖netRegularPolynomial tests‖ ∈ spectrum ℝ (netRegularPolynomial tests) := by
  classical
  letI : Nonempty tests := hne.to_subtype
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum
    (A := RegularCoefficientEnergy.Hilbert (ProductFreeGroup K n) tests →L[ℂ]
      RegularCoefficientEnergy.Hilbert (ProductFreeGroup K n) tests)
    (a := netRegularPolynomial tests)
    (netRegularPolynomial_selfAdjoint tests) with h | h
  · exact h
  · have hneg : ‖netRegularPolynomial tests‖ ∈ spectrum ℝ (-netRegularPolynomial tests) := by
      rw [← spectrum.neg_eq]
      exact h
    rwa [netRegularPolynomial_spectrum_neg tests hsymm] at hneg

/-- A real positive spectral endpoint gives the exact positive shift norm. -/
theorem shifted_norm_of_norm_mem_spectrum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (T : H →L[ℂ] H) (hT : ‖T‖ ∈ spectrum ℝ T) (θ : ℝ) (hθ : 0 ≤ θ) :
    ‖T + algebraMap ℝ (H →L[ℂ] H) θ‖ = ‖T‖ + θ := by
  apply le_antisymm
  · calc
      _ ≤ ‖T‖ + ‖algebraMap ℝ (H →L[ℂ] H) θ‖ := norm_add_le _ _
      _ = ‖T‖ + θ := by rw [norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg hθ]
  · have hm : ‖T‖ + θ ∈ spectrum ℝ (T + algebraMap ℝ (H →L[ℂ] H) θ) := by
      rw [← spectrum.add_singleton_eq]
      exact Set.add_mem_add hT (Set.mem_singleton θ)
    have h := spectrum.norm_le_norm_of_mem hm
    simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg T) hθ)] using h

/-- Exact shift identity for Step 3's first, undoubled shortening. -/
theorem netRegularPolynomial_shifted_norm (tests : Finset (ObservableSpace (Branch K n)))
    (hne : tests.Nonempty) (hsymm : ∀ x ∈ tests, -x ∈ tests) (θ : ℝ) (hθ : 0 ≤ θ) :
    ‖netRegularPolynomial tests + algebraMap ℝ
      (RegularCoefficientEnergy.Hilbert (ProductFreeGroup K n) tests →L[ℂ]
        RegularCoefficientEnergy.Hilbert (ProductFreeGroup K n) tests) θ‖ =
      ‖netRegularPolynomial tests‖ + θ := by
  classical
  letI : Nonempty tests := hne.to_subtype
  exact shifted_norm_of_norm_mem_spectrum (netRegularPolynomial tests)
    (netRegularPolynomial_norm_mem_spectrum tests hne hsymm) θ hθ

/-- Step 1 assembled on actual matrices and actual regular operators: a sharp,
negation-symmetric net, prescribed positive lower bound, Collins--Youn upper
bound, with no analytic inputs. Self-adjointness and spectral symmetry are
provided by `netRegularPolynomial_selfAdjoint` and `netRegularPolynomial_spectrum_neg`. -/
theorem exists_net_polynomial (hK : 2 ≤ K) (hn : 1 ≤ n) :
    ∃ tests : Finset (ObservableSpace (Branch K n)), tests.Nonempty ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      UnitSphereNet tests (1 / (n : ℝ)) ∧
      (tests.card : ℝ) ≤ (1 + 2 * (n : ℝ)) ^ (K ^ (2*n) - 1) ∧
      Real.sqrt 2 * (K : ℝ)^(-((n : ℝ)+1)/2) ≤ ‖netRegularPolynomial tests‖ ∧
      ‖netRegularPolynomial tests‖ ≤ c K n := by
  classical
  letI : NeZero K := ⟨by omega⟩
  obtain ⟨A, hA, ht, hh, hfree⟩ := PrescribedTest.exists_prescribed_test (K := K) (n := n) hK hn
  obtain ⟨tests, ha, _, hnorm, hsymm, _, hnet, hcard⟩ :=
    ObservableDimension.exists_symmetric_observable_net_for_matrix A hA ht hh n hn
  refine ⟨tests, ⟨_,ha⟩, hnorm, hsymm, hnet, ?_, ?_,
    netRegularPolynomial_norm_le hK hn tests hnorm⟩
  · simpa only [Branch, Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm n 2]
      using hcard
  · rw [← hfree]
    exact netRegularPolynomial_test_le tests (matrixObservable A hA ht) ha
end ObservableNets

end Nonadditivity.NetPolynomial
