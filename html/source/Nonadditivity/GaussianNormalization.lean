/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMomentTail

/-! Deterministic polar normalization of a rectangular matrix close to an isometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.GaussianNormalization
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker ComplexConjugate
open Channels
variable {D B E : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- The positive inverse square root, constructed by the matrix spectral theorem. -/
def normalizer (A : Matrix D D ℂ) (hA : A.IsHermitian) : Matrix D D ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal fun i => ((Real.sqrt (hA.eigenvalues i))⁻¹ : ℂ))

theorem eigenvalue_lower (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hclose : ‖A-1‖≤1/2) (i : D) : 1/2 ≤ hA.eigenvalues i := by
  letI : CStarAlgebra (Matrix D D ℂ) := {}
  let f : D → ℂ := fun i => (hA.eigenvalues i : ℂ)-1
  have hnorm : ‖A-1‖ = ‖f‖ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_one (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary), ←map_sub,
      StarAlgEquiv.norm_map]
    have hd : Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) - 1 = Matrix.diagonal f := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    change ‖Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) - 1‖ = ‖f‖
    rw [hd,Matrix.l2_opNorm_diagonal]
  have hi : |hA.eigenvalues i-1| ≤ 1/2 := by
    have h := (norm_le_pi_norm f i).trans (hnorm ▸ hclose)
    simpa only [f, ←Complex.ofReal_one, ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  linarith [(abs_le.mp hi).1]

theorem normalizer_hermitian (A : Matrix D D ℂ) (hA : A.IsHermitian) :
    (normalizer A hA).IsHermitian := by
  change star (normalizer A hA) = normalizer A hA
  unfold normalizer
  rw [← map_star]
  congr 1
  ext i j
  by_cases h:i=j
  · subst j; simp [Matrix.star_apply]
  · simp [Matrix.star_apply,h,Ne.symm h]

theorem inv_sqrt_identity (x : ℝ) (hx : 0<x) :
    ((Real.sqrt x)⁻¹:ℂ) * (x:ℂ) * ((Real.sqrt x)⁻¹:ℂ) = 1 := by
  have h : (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = (1:ℝ) := by
    have hsq := Real.sq_sqrt hx.le
    have hn := (Real.sqrt_pos.mpr hx).ne'
    field_simp
    nlinarith
  exact_mod_cast h

theorem normalizer_identity (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hclose : ‖A-1‖≤1/2) : normalizer A hA * A * normalizer A hA = 1 := by
  let U := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  have ha : A = U (Matrix.diagonal fun i => (hA.eigenvalues i:ℂ)) := hA.spectral_theorem
  unfold normalizer
  change U _ * A * U _ = 1
  conv_lhs => arg 1; arg 2; rw [ha]
  rw [←map_mul,←map_mul,←map_one U]
  congr 1
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h:i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    exact inv_sqrt_identity _ (by have := eigenvalue_lower A hA hclose i; linarith)
  · simp [h]

theorem normalizer_norm_sq (A : Matrix D D ℂ) (hA : A.IsHermitian)
    (hclose : ‖A-1‖≤1/2) : ‖normalizer A hA‖^2≤2 := by
  letI : CStarAlgebra (Matrix D D ℂ) := {}
  have hnorm : ‖normalizer A hA‖ ≤ Real.sqrt 2 := by
    unfold normalizer
    rw [StarAlgEquiv.norm_map,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hl := eigenvalue_lower A hA hclose i
    have hx : 0 < hA.eigenvalues i := by linarith
    have hinv : ((Real.sqrt (hA.eigenvalues i))⁻¹)^2≤2 := by
      rw [inv_pow,Real.sq_sqrt hx.le]
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hx).mpr (by linarith)
    have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
    have hi : (Real.sqrt (hA.eigenvalues i))⁻¹ ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
    simpa only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using hi
  nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),norm_nonneg (normalizer A hA)]

def gram (G : Matrix (B×E) D ℂ) : Matrix D D ℂ := G.conjTranspose * G

theorem gram_hermitian (G : Matrix (B×E) D ℂ) : (gram G).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self G

def normalized (G : Matrix (B×E) D ℂ) : Matrix (B×E) D ℂ :=
  G * normalizer (gram G) (gram_hermitian G)

theorem normalized_isometry (G : Matrix (B×E) D ℂ) (hclose : ‖gram G-1‖≤1/2) :
    (normalized G).conjTranspose * normalized G = 1 := by
  unfold normalized
  rw [Matrix.conjTranspose_mul,(normalizer_hermitian (gram G) (gram_hermitian G)).eq]
  simpa only [Matrix.mul_assoc,gram] using normalizer_identity (gram G) (gram_hermitian G) hclose

/-- Slicing an actual isometry into environment-indexed Kraus matrices. -/
def channelOfIsometry (V : Matrix (B×E) D ℂ) (hV : V.conjTranspose*V=1) : KrausChannel D B E where
  kraus e b d := V (b,e) d
  complete := by
    ext i j
    have h := congrArg (fun M : Matrix D D ℂ => M i j) hV
    simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type] at h ⊢
    rw [Finset.sum_comm] at h
    exact h

/-- An actual finite channel obtained by polar normalization of `G`. -/
def channel (G : Matrix (B×E) D ℂ) (hclose : ‖gram G-1‖≤1/2) : KrausChannel D B E :=
  channelOfIsometry (normalized G) (normalized_isometry G hclose)

def slice (G : Matrix (B×E) D ℂ) (e : E) : Matrix B D ℂ := fun b d => G (b,e) d

/-- The unnormalized adjoint compression whose Gaussian concentration is needed. -/
def rawAdjoint (G : Matrix (B×E) D ℂ) (A : Matrix B B ℂ) : Matrix D D ℂ :=
  G.conjTranspose * (A ⊗ₖ (1 : Matrix E E ℂ)) * G

theorem rawAdjoint_eq_sum (G : Matrix (B×E) D ℂ) (A : Matrix B B ℂ) :
    rawAdjoint G A = ∑ e, (slice G e).conjTranspose * A * slice G e := by
  ext i j
  simp only [rawAdjoint,Matrix.mul_assoc,Matrix.mul_apply,Matrix.kronecker_apply,
    Matrix.one_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,Fintype.sum_prod_type,slice]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  exact Finset.sum_comm

theorem channelOfIsometry_adjoint (V : Matrix (B×E) D ℂ) (hV : V.conjTranspose*V=1)
    (A : Matrix B B ℂ) : (channelOfIsometry V hV).adjointMap A = rawAdjoint V A := by
  rw [rawAdjoint_eq_sum]
  rfl

theorem rawAdjoint_normalized (G : Matrix (B×E) D ℂ) (A : Matrix B B ℂ) :
    rawAdjoint (normalized G) A = normalizer (gram G) (gram_hermitian G) *
      rawAdjoint G A * normalizer (gram G) (gram_hermitian G) := by
  simp only [rawAdjoint,normalized,Matrix.conjTranspose_mul,
    (normalizer_hermitian (gram G) (gram_hermitian G)).eq,Matrix.mul_assoc]

theorem channel_adjoint (G : Matrix (B×E) D ℂ) (hclose : ‖gram G-1‖≤1/2)
    (A : Matrix B B ℂ) : (channel G hclose).adjointMap A =
      normalizer (gram G) (gram_hermitian G) * rawAdjoint G A *
        normalizer (gram G) (gram_hermitian G) := by
  exact (channelOfIsometry_adjoint _ _ A).trans (rawAdjoint_normalized G A)

/-- Polar normalization costs at most a factor two in every adjoint observable bound. -/
theorem channel_adjoint_norm_le (G : Matrix (B×E) D ℂ) (hclose : ‖gram G-1‖≤1/2)
    (A : Matrix B B ℂ) : ‖(channel G hclose).adjointMap A‖ ≤ 2*‖rawAdjoint G A‖ := by
  rw [channel_adjoint]
  let S := normalizer (gram G) (gram_hermitian G)
  calc
    ‖S * rawAdjoint G A * S‖ ≤ (‖S‖*‖rawAdjoint G A‖)*‖S‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖S‖^2*‖rawAdjoint G A‖ := by ring
    _ ≤ 2*‖rawAdjoint G A‖ := mul_le_mul_of_nonneg_right
      (normalizer_norm_sq (gram G) (gram_hermitian G) hclose) (norm_nonneg _)

theorem transfer_observable_bound (G : Matrix (B×E) D ℂ) (hclose : ‖gram G-1‖≤1/2)
    (A : Matrix B B ℂ) (t h : ℝ) (hraw : ‖rawAdjoint G A‖ ≤ t*h) :
    ‖(channel G hclose).adjointMap A‖ ≤ (2*t)*h :=
  (channel_adjoint_norm_le G hclose A).trans (by nlinarith)

end Nonadditivity.GaussianNormalization
