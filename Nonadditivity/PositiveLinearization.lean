/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Linearization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Unconditional positive blocks for finite-set linearization

The positive block used in Appendix A is constructed directly by functional
calculus, so no polar-decomposition identities are supplied as hypotheses.
-/

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.Linearization

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal block matrix with positive blocks is positive. -/
theorem diagonal_blocks_posSemidef (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  let R := Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B)
  have hR := Matrix.posSemidef_conjTranspose_mul_self R
  simpa [R, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    positive_sqrt_gram A hA, positive_sqrt_gram B hB] using hR

/-- The modulus of a Hermitian dilation is the diagonal pair of moduli. -/
theorem abs_hermitianDilation (c : Matrix ι ι ℂ) :
    CFC.abs (hermitianDilation c) =
      Matrix.fromBlocks (CFC.abs c.conjTranspose) 0 0 (CFC.abs c) := by
  have hD := diagonal_blocks_posSemidef (CFC.abs c.conjTranspose) (CFC.abs c)
    (Matrix.LE.le.posSemidef (CFC.abs_nonneg c.conjTranspose))
    (Matrix.LE.le.posSemidef (CFC.abs_nonneg c))
  apply (CFC.sq_eq_sq_iff _ _ (CFC.abs_nonneg _) hD.nonneg).mp
  rw [CFC.abs_sq, Matrix.star_eq_conjTranspose,
    (hermitianDilation_isHermitian c), hermitianDilation_sq]
  simp [pow_two, Matrix.fromBlocks_multiply, CFC.abs_mul_abs,
    Matrix.star_eq_conjTranspose]

/-- The exact positive polar block, valid for every complex square matrix. -/
theorem modulus_block_posSemidef (c : Matrix ι ι ℂ) :
    (Matrix.fromBlocks (CFC.abs c.conjTranspose) c c.conjTranspose
      (CFC.abs c)).PosSemidef := by
  have hH : IsSelfAdjoint (hermitianDilation c) := hermitianDilation_isHermitian c
  have h : 0 ≤ CFC.abs (hermitianDilation c) + hermitianDilation c := by
    rw [CFC.abs_add_self _ hH]
    exact nsmul_nonneg (CFC.posPart_nonneg _) 2
  have hp := Matrix.LE.le.posSemidef h
  rw [abs_hermitianDilation] at hp
  simpa [hermitianDilation, Matrix.fromBlocks_add] using hp

/-- The constant-block correction in the appendix is positive, with its
scalar chosen explicitly. -/
theorem constant_correction_posSemidef (D c : Matrix ι ι ℂ)
    (hD : D.PosSemidef) (hc : c.IsHermitian) :
    (algebraMap ℝ (Matrix ι ι ℂ) ‖D + CFC.abs c‖ + c - D).PosSemidef := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  have hsum : 0 ≤ D + CFC.abs c := add_nonneg hD.nonneg (CFC.abs_nonneg c)
  have hupper := (IsSelfAdjoint.of_nonneg hsum).le_algebraMap_norm_self
  have hpos : 0 ≤ CFC.abs c + c := by
    rw [CFC.abs_add_self c hc.isSelfAdjoint]
    exact nsmul_nonneg (CFC.posPart_nonneg c) 2
  have h := add_nonneg (sub_nonneg.mpr hupper) hpos
  have heq : algebraMap ℝ (Matrix ι ι ℂ) ‖D + CFC.abs c‖ -
      (D + CFC.abs c) + (CFC.abs c + c) =
      algebraMap ℝ (Matrix ι ι ℂ) ‖D + CFC.abs c‖ + c - D := by abel
  rw [heq] at h
  exact Matrix.LE.le.posSemidef h

/-- Taking the matrix modulus preserves every vector's output norm. -/
theorem modulus_apply_norm (c : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (CFC.abs c) x‖ = ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) c x‖ := by
  have hgram : star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (CFC.abs c)) *
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (CFC.abs c) =
      star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) c) * Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) c := by
    rw [← map_star, ← map_mul, ← map_star, ← map_mul]
    congr 1
    rw [(IsSelfAdjoint.of_nonneg (CFC.abs_nonneg c)).star_eq, CFC.abs_mul_abs]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  exact congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι =>
    (inner ℂ (T x) x).re) hgram

/-- The precise additive-constant bound from coefficient energy. The moduli
and the matrix operator norm here are the actual functional-calculus ones. -/
theorem modulus_sum_norm_le_sqrt_card {κ : Type*} (s : Finset κ)
    (c : κ → Matrix ι ι ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (henergy : ∀ x : EuclideanSpace ℂ ι,
      ∑ w ∈ s, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (c w) x‖ ^ 2 ≤ ρ ^ 2 * ‖x‖ ^ 2) :
    ‖∑ w ∈ s, CFC.abs (c w)‖ ≤ Real.sqrt (s.card : ℝ) * ρ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, map_sum]
  apply operator_sum_norm_le_sqrt_card s (fun w => Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (CFC.abs (c w)))
    ρ hρ
  intro x
  simpa only [modulus_apply_norm] using henergy x

/-- Diagonal blocks give an injective star-algebra homomorphism. -/
def diagonalBlocksHom :
    (Matrix ι ι ℂ × Matrix ι ι ℂ) →⋆ₐ[ℂ] Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_zero' := Matrix.fromBlocks_zero
  map_one' := Matrix.fromBlocks_one
  map_add' p q := by simp [Matrix.fromBlocks_add]
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  commutes' z := by ext i j; cases i <;> cases j <;>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
  map_star' p := by simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

theorem diagonalBlocksHom_injective :
    Function.Injective (diagonalBlocksHom (ι := ι)) := by
  intro p q h
  apply Prod.ext
  · ext i j
    exact congrArg (fun A => A (Sum.inl i) (Sum.inl j)) h
  · ext i j
    exact congrArg (fun A => A (Sum.inr i) (Sum.inr j)) h

/-- The Euclidean operator norm of diagonal blocks is the larger block norm. -/
theorem diagonal_blocks_norm (A B : Matrix ι ι ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  letI : CStarAlgebra (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := { }
  exact NonUnitalStarAlgHom.norm_map (diagonalBlocksHom (ι := ι))
    diagonalBlocksHom_injective (A, B)

/-- Hermitian dilation preserves the actual matrix operator norm. -/
theorem hermitianDilation_norm (c : Matrix ι ι ℂ) :
    ‖hermitianDilation c‖ = ‖c‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (hermitianDilation c)
  rw [(hermitianDilation_isHermitian c), hermitianDilation_sq,
    diagonal_blocks_norm] at h
  have hc : ‖c * c.conjTranspose‖ = ‖c‖ * ‖c‖ := by
    simpa [Matrix.l2_opNorm_conjTranspose] using
      Matrix.l2_opNorm_conjTranspose_mul_self c.conjTranspose
  rw [hc, Matrix.l2_opNorm_conjTranspose_mul_self, max_self] at h
  nlinarith [norm_nonneg c, norm_nonneg (hermitianDilation c)]

/-- The grading unitary exchanges the two spectral signs of a dilation. -/
def dilationSign : unitary (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :=
  ⟨Matrix.fromBlocks 1 0 0 (-1), by
    rw [Unitary.mem_iff]
    constructor <;>
      simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩

theorem dilationSign_conjugate (c : Matrix ι ι ℂ) :
    (dilationSign (ι := ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * hermitianDilation c *
      (star (dilationSign (ι := ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) = -hermitianDilation c := by
  simp [dilationSign, hermitianDilation, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/-- The positive spectral endpoint is the original matrix's norm. -/
theorem norm_mem_dilation_spectrum [Nonempty ι] (c : Matrix ι ι ℂ) :
    ‖c‖ ∈ spectrum ℝ (hermitianDilation c) := by
  letI : CStarAlgebra (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := { }
  have hsym : spectrum ℝ (-hermitianDilation c) = spectrum ℝ (hermitianDilation c) := by
    rw [← dilationSign_conjugate c]
    exact Unitary.spectrum_star_right_conjugate
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum
    (hermitianDilation_isHermitian c).isSelfAdjoint with h | h
  · simpa only [hermitianDilation_norm] using h
  · rw [hermitianDilation_norm] at h
    have hneg : ‖c‖ ∈ spectrum ℝ (-hermitianDilation c) := by
      rw [← spectrum.neg_eq]
      exact h
    rwa [hsym] at hneg

/-- The exact norm identity needed after the positive Gram construction. -/
theorem shifted_dilation_norm [Nonempty ι] (c : Matrix ι ι ℂ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ‖hermitianDilation c + algebraMap ℝ (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) θ‖ =
      ‖c‖ + θ := by
  letI : CStarAlgebra (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := { }
  apply le_antisymm
  · calc
      _ ≤ ‖hermitianDilation c‖ +
          ‖algebraMap ℝ (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) θ‖ := norm_add_le _ _
      _ = ‖c‖ + θ := by
        rw [hermitianDilation_norm, norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg hθ]
  · have hmem : ‖c‖ + θ ∈ spectrum ℝ
        (hermitianDilation c + algebraMap ℝ (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) θ) := by
      rw [← spectrum.add_singleton_eq]
      exact Set.add_mem_add (norm_mem_dilation_spectrum c) (Set.mem_singleton θ)
    have h := spectrum.norm_le_norm_of_mem hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg c) hθ)] at h

/-- The matrix Gram identity alone supplies the exact squared norm;
no factor norm equality is assumed. -/
theorem factor_norm_sq_of_shifted_gram [Nonempty ι]
    {κ : Type*} [Fintype κ] (c : Matrix ι ι ℂ)
    (Q : Matrix κ (ι ⊕ ι) ℂ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hgram : Q.conjTranspose * Q = hermitianDilation c +
      algebraMap ℝ (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) θ) :
    ‖Q‖ ^ 2 = ‖c‖ + θ := by
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, hgram]
  exact shifted_dilation_norm c θ hθ

/-- Padding a rectangular polynomial into a fixed block column preserves
its Euclidean operator norm. -/
theorem right_isometry_mul_norm {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (Q : Matrix κ ι ℂ) (V : Matrix ι ν ℂ)
    (hV : V * V.conjTranspose = 1) : ‖Q * V‖ = ‖Q‖ := by
  classical
  have hgram : (Q * V) * (Q * V).conjTranspose = Q * Q.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV, Matrix.one_mul]
  have hQ : ‖Q * Q.conjTranspose‖ = ‖Q‖ * ‖Q‖ := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] using
      Matrix.l2_opNorm_conjTranspose_mul_self Q.conjTranspose
  have hQV : ‖(Q * V) * (Q * V).conjTranspose‖ = ‖Q * V‖ * ‖Q * V‖ := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] using
      Matrix.l2_opNorm_conjTranspose_mul_self (Q * V).conjTranspose
  rw [hgram, hQ] at hQV
  nlinarith [norm_nonneg Q, norm_nonneg (Q * V)]

end Nonadditivity.Linearization
