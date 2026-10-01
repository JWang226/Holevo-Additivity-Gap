/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Algebraic and numerical steps in polynomial linearization

This file proves the finite support bound, Gram factorization identities,
Hermitian dilation identities, the scalar backward-error calculation, and the
geometric word-count calculation used in Sections 3 and Appendix A of
`nonadditivity.tex`.

The analytic existence of the positive block matrix with the stated operator
norm bound is not assumed globally or declared as an axiom here. The Gram
identities below apply to any supplied square-root factor; the error theorem
states its norm-identity hypotheses explicitly.
-/

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.Linearization

open scoped BigOperators

section Support

variable {G : Type*} [Group G] [DecidableEq G]

/-- The finite set `S⁻¹ S`, represented without a pointwise-set convention. -/
def differenceSupport (S : Finset G) : Finset G :=
  (S ×ˢ S).image (fun gh => gh.1⁻¹ * gh.2)

@[simp] theorem mem_differenceSupport {S : Finset G} {w : G} :
    w ∈ differenceSupport S ↔ ∃ g ∈ S, ∃ h ∈ S, g⁻¹ * h = w := by
  simp only [differenceSupport, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨g,h⟩, ⟨hg,hh⟩, hw⟩
    exact ⟨g,hg,h,hh,hw⟩
  · rintro ⟨g,hg,h,hh,hw⟩
    exact ⟨(g,h), ⟨hg,hh⟩, hw⟩

/-- There are at most `B²` differences in a set of `B` elements. -/
theorem card_differenceSupport_le (S : Finset G) :
    (differenceSupport S).card ≤ S.card ^ 2 := by
  calc
    (differenceSupport S).card ≤ (S ×ˢ S).card := Finset.card_image_le
    _ = S.card ^ 2 := by simp [pow_two]

/-- The adjoint support is covered by the same finite set. -/
theorem inv_mem_differenceSupport {S : Finset G} {w : G}
    (hw : w ∈ differenceSupport S) : w⁻¹ ∈ differenceSupport S := by
  obtain ⟨g,hg,h,hh,rfl⟩ := mem_differenceSupport.mp hw
  apply mem_differenceSupport.mpr
  exact ⟨h,hh,g,hg, by simp⟩

omit [DecidableEq G] in
/-- Including the identity makes the support size at least one. -/
theorem one_le_card {S : Finset G} (hS : (1 : G) ∈ S) : 1 ≤ S.card :=
  Finset.one_le_card.mpr ⟨1,hS⟩

/-- A split word `a * b` factors as `(a⁻¹)⁻¹ * b`. -/
theorem split_mem_differenceSupport {S : Finset G} {a b : G}
    (ha : a⁻¹ ∈ S) (hb : b ∈ S) : a * b ∈ differenceSupport S :=
  mem_differenceSupport.mpr ⟨a⁻¹, ha, b, hb, by simp⟩

end Support

section Gram

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

omit [Fintype ν] in
/-- Exact Gram identity for the evaluated square-root construction. -/
theorem gram_factorization (R : Matrix ι κ A) (V : Matrix κ ν A) :
    (R * V).conjTranspose * (R * V) =
      V.conjTranspose * (R.conjTranspose * R) * V := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype ν] in
/-- A square-root factor may be supplied as ordinary data. -/
theorem gram_factorization_of_sqrt (R : Matrix ι κ A) (G : Matrix κ κ A)
    (V : Matrix κ ν A) (hR : R.conjTranspose * R = G) :
    (R * V).conjTranspose * (R * V) = V.conjTranspose * G * V := by
  rw [gram_factorization, hR]

/-- The finite block evaluation in the manuscript, with noncommuting entries. -/
theorem column_gram_entry (G : Matrix κ κ A) (v : κ → A) :
    let V : Matrix κ Unit A := fun g _ => v g
    (V.conjTranspose * G * V) () () =
      ∑ g, ∑ h, star (v g) * G g h * v h := by
  dsimp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_mul]

end Gram

section PositiveMatrices

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν]

/-- Finite-dimensional positivity provides the Gram square root. -/
theorem positive_sqrt_gram (G : Matrix ι ι ℂ) (hG : G.PosSemidef) :
    (CFC.sqrt G).conjTranspose * CFC.sqrt G = G := by
  rw [← Matrix.star_eq_conjTranspose,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg G)).star_eq]
  exact CFC.sqrt_mul_sqrt_self G hG.nonneg

omit [Fintype ν] in
/-- Construct the evaluated factor using the positive matrix's actual square root. -/
theorem positive_gram_factorization (G : Matrix ι ι ℂ) (hG : G.PosSemidef)
    (V : Matrix ι ν ℂ) :
    ∃ Q : Matrix ι ν ℂ, Q.conjTranspose * Q = V.conjTranspose * G * V := by
  exact ⟨CFC.sqrt G * V,
    gram_factorization_of_sqrt _ G V (positive_sqrt_gram G hG)⟩

/-- The positive polar block is a compression of `P` by the column `(U*, I)`. -/
theorem polar_block_posSemidef (P U : Matrix ι ι ℂ) (hP : P.PosSemidef) :
    (Matrix.fromBlocks (U * P * U.conjTranspose) (U * P)
      (P * U.conjTranspose) P).PosSemidef := by
  have h := hP.conjTranspose_mul_mul_same (Matrix.fromCols U.conjTranspose (1 : Matrix ι ι ℂ))
  simpa [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, Matrix.mul_assoc] using h

/-- The appendix polar positivity step with the exact polar identities explicit. -/
theorem polar_block_posSemidef_of_identities (c p d u : Matrix ι ι ℂ)
    (hp : p.PosSemidef) (hc : c = u * p) (hd : d = u * p * u.conjTranspose) :
    (Matrix.fromBlocks d c c.conjTranspose p).PosSemidef := by
  rw [hc, hd, Matrix.conjTranspose_mul, hp.1]
  exact polar_block_posSemidef p u hp

end PositiveMatrices

section Dilation

variable {ι : Type*} [Fintype ι]
variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- The standard Hermitian dilation, at the matrix-algebra level. -/
def hermitianDilation (P : Matrix ι ι A) : Matrix (Sum ι ι) (Sum ι ι) A :=
  Matrix.fromBlocks 0 P P.conjTranspose 0

omit [Fintype ι] in
theorem hermitianDilation_isHermitian (P : Matrix ι ι A) :
    (hermitianDilation P).IsHermitian := by
  unfold hermitianDilation Matrix.IsHermitian
  simp [Matrix.fromBlocks_conjTranspose]

theorem hermitianDilation_sq (P : Matrix ι ι A) :
    hermitianDilation P * hermitianDilation P =
      Matrix.fromBlocks (P * P.conjTranspose) 0 0 (P.conjTranspose * P) := by
  unfold hermitianDilation
  simp [Matrix.fromBlocks_multiply]

end Dilation

section ErrorTransfer

/-- The scalar calculation behind `e_old ≤ 6 B e_new`.

`rN, rR` are the original two operator norms; `qN, qR` are the
factorized operator norms. All analytic input appears in `hN`, `hR`,
and `hTheta`, rather than as hidden axioms.
-/
theorem backward_error_transfer
    (rN rR qN qR theta B e : ℝ)
    (hqN : 0 ≤ qN) (_hqR : 0 ≤ qR) (hrR : 0 ≤ rR)
    (hTheta0 : 0 ≤ theta) (hB : 1 ≤ B)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hN : qN ^ 2 = rN + theta) (hR : qR ^ 2 = rR + theta)
    (hTheta : theta ≤ B * rR)
    (hQ : qN ≤ (1 + e) * qR) :
    rN ≤ (1 + 6 * B * e) * rR := by
  have hsq : qN ^ 2 ≤ ((1 + e) * qR) ^ 2 := by
    exact pow_le_pow_left₀ hqN hQ 2
  have heSq : e ^ 2 ≤ e := by nlinarith
  have hError : ((1 + e) ^ 2 - 1) ≤ 3 * e := by nlinarith
  have hSum : 0 ≤ rR + theta := add_nonneg hrR hTheta0
  have hGrowth := mul_le_mul_of_nonneg_right hError hSum
  have hPre : rN ≤ rR + 3 * e * (rR + theta) := by
    nlinarith [hsq, hGrowth]
  have hScale : 0 ≤ 3 * e := by positivity
  have hBound := mul_le_mul_of_nonneg_left hTheta hScale
  have hBScale : 3 * (1 + B) ≤ 6 * B := by linarith
  have hBound' := mul_le_mul_of_nonneg_right hBScale (mul_nonneg he0 hrR)
  nlinarith [hPre, hBound, hBound']

/-- Initial Gram reduction has additive constant one. -/
theorem initial_backward_error
    (rN rR qN qR e : ℝ)
    (hqN : 0 ≤ qN) (hrR : 0 ≤ rR)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hN : qN ^ 2 = rN + 1) (hR : qR ^ 2 = rR + 1)
    (hQ : qN ≤ (1 + e) * qR) :
    rN - rR ≤ 3 * e * (1 + rR) := by
  have hsq := pow_le_pow_left₀ hqN hQ 2
  have heSq : e ^ 2 ≤ e := by nlinarith
  have hError : (1 + e) ^ 2 - 1 ≤ 3 * e := by nlinarith
  have hGrowth := mul_le_mul_of_nonneg_right hError (show 0 ≤ 1 + rR by linarith)
  nlinarith [hsq, hGrowth]

/-- Nonnegative relative excess used for every intermediate polynomial. -/
noncomputable def relativeNormError (a b : ℝ) : ℝ := max 0 (a / b - 1)

@[simp] theorem relativeNormError_nonneg (a b : ℝ) : 0 ≤ relativeNormError a b :=
  le_max_left _ _

/-- Convert between a relative-error number and a multiplicative norm bound. -/
theorem relativeNormError_le_iff (a b e : ℝ) (hb : 0 < b) (he : 0 ≤ e) :
    relativeNormError a b ≤ e ↔ a ≤ (1 + e) * b := by
  unfold relativeNormError
  rw [max_le_iff]
  constructor
  · intro h
    have hdiv : a / b ≤ 1 + e := by linarith [h.2]
    have hmul := (div_le_iff₀ hb).mp hdiv
    nlinarith
  · intro h
    refine ⟨he, ?_⟩
    have hdiv : a / b ≤ 1 + e := (div_le_iff₀ hb).mpr (by nlinarith)
    linarith

/-- The backward-error statement in exactly the `max(0, ratio - 1)` convention. -/
theorem relative_backward_error_transfer
    (rN rR qN qR theta B : ℝ)
    (hqN : 0 ≤ qN) (hqR : 0 ≤ qR) (hrR : 0 < rR)
    (hTheta0 : 0 ≤ theta) (hB : 1 ≤ B)
    (hN : qN ^ 2 = rN + theta) (hR : qR ^ 2 = rR + theta)
    (hTheta : theta ≤ B * rR)
    (hError : relativeNormError qN qR ≤ 1) :
    relativeNormError rN rR ≤ 6 * B * relativeNormError qN qR := by
  have hqRpos : 0 < qR := by nlinarith
  have he0 := relativeNormError_nonneg qN qR
  have hQ := (relativeNormError_le_iff qN qR (relativeNormError qN qR) hqRpos he0).mp le_rfl
  apply (relativeNormError_le_iff rN rR _ hrR (by positivity)).mpr
  exact backward_error_transfer rN rR qN qR theta B _ hqN hqR hrR.le
    hTheta0 hB he0 hError hN hR hTheta hQ

/-- Compose an arbitrary finite sequence of nonnegative backward-error factors. -/
theorem backward_error_chain (n : ℕ) (F e : ℕ → ℝ)
    (hF : ∀ i < n, 0 ≤ F i) (hStep : ∀ i < n, e i ≤ F i * e (i + 1)) :
    e 0 ≤ (∏ i ∈ Finset.range n, F i) * e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hPrefix : e 0 ≤ (∏ i ∈ Finset.range n, F i) * e n :=
      ih (fun i hi => hF i (by omega)) (fun i hi => hStep i (by omega))
    have hProd : 0 ≤ ∏ i ∈ Finset.range n, F i :=
      Finset.prod_nonneg (fun i hi => hF i (by have := Finset.mem_range.mp hi; omega))
    calc
      e 0 ≤ (∏ i ∈ Finset.range n, F i) * e n := hPrefix
      _ ≤ (∏ i ∈ Finset.range n, F i) * (F n * e (n + 1)) :=
        mul_le_mul_of_nonneg_left (hStep n (by omega)) hProd
      _ = (∏ i ∈ Finset.range (n + 1), F i) * e (n + 1) := by
        rw [Finset.prod_range_succ]
        ring

end ErrorTransfer

section OperatorCauchySchwarz

variable {ι : Type*} {E F 𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- The vector Cauchy–Schwarz step used to control the additive constant. -/
theorem norm_sum_sq_le_card_sum_sq (s : Finset ι) (v : ι → F) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2
    _ ≤ (∑ i ∈ s, ‖v i‖ ^ 2) * (∑ _i ∈ s, (1 : ℝ) ^ 2) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖v i‖) (fun _ => (1 : ℝ))
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by simp [mul_comm]

/-- A quadratic energy bound controls the sum's operator norm by `√|S| ρ`. -/
theorem operator_sum_norm_le_sqrt_card (s : Finset ι) (T : ι → E →L[𝕜] F)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hEnergy : ∀ x : E, ∑ i ∈ s, ‖T i x‖ ^ 2 ≤ rho ^ 2 * ‖x‖ ^ 2) :
    ‖∑ i ∈ s, T i‖ ≤ Real.sqrt (s.card : ℝ) * rho := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hrho)
  intro x
  have h1 := norm_sum_sq_le_card_sum_sq s (fun i => T i x)
  have h2 := mul_le_mul_of_nonneg_left (hEnergy x) (show 0 ≤ (s.card : ℝ) by positivity)
  have h3 : (Real.sqrt (s.card : ℝ) * rho * ‖x‖) ^ 2 =
      (s.card : ℝ) * rho ^ 2 * ‖x‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hTarget : 0 ≤ Real.sqrt (s.card : ℝ) * rho * ‖x‖ := by positivity
  simp only [ContinuousLinearMap.sum_apply]
  nlinarith [norm_nonneg (∑ i ∈ s, T i x)]

/-- The manuscript's `θ ≤ Bρ` follows once the coefficient energy bound
and `|W| ≤ B²` have been supplied. -/
theorem operator_sum_norm_le_support_size (s : Finset ι) (T : ι → E →L[𝕜] F)
    (rho B : ℝ) (hrho : 0 ≤ rho) (hB : 0 ≤ B)
    (hCard : (s.card : ℝ) ≤ B ^ 2)
    (hEnergy : ∀ x : E, ∑ i ∈ s, ‖T i x‖ ^ 2 ≤ rho ^ 2 * ‖x‖ ^ 2) :
    ‖∑ i ∈ s, T i‖ ≤ B * rho := by
  calc
    ‖∑ i ∈ s, T i‖ ≤ Real.sqrt (s.card : ℝ) * rho :=
      operator_sum_norm_le_sqrt_card s T rho hrho hEnergy
    _ ≤ B * rho := mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨hB,hCard⟩) hrho

/-- Specialize the coefficient-energy estimate to the actual difference support;
the cardinal bound needed here is proved from `S`, rather than supplied. -/
theorem operator_sum_norm_le_differenceSupport
    {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (T : G → E →L[𝕜] F) (rho : ℝ) (hrho : 0 ≤ rho)
    (hEnergy : ∀ x : E, ∑ w ∈ differenceSupport S, ‖T w x‖ ^ 2 ≤ rho ^ 2 * ‖x‖ ^ 2) :
    ‖∑ w ∈ differenceSupport S, T w‖ ≤ (S.card : ℝ) * rho := by
  apply operator_sum_norm_le_support_size _ T rho (S.card : ℝ) hrho (by positivity) ?_ hEnergy
  exact_mod_cast card_differenceSupport_le S

end OperatorCauchySchwarz

section HilbertCoefficientEnergy

variable {ι E F 𝕜 : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A bound on the coefficient Gram operator gives the precise quadratic energy
estimate used in the appendix's operator Cauchy–Schwarz argument. -/
theorem coefficient_energy_le_of_gram_norm
    (s : Finset ι) (T : ι → E →L[𝕜] F) (rho : ℝ)
    (hGram : ‖∑ i ∈ s, ContinuousLinearMap.adjoint (T i) ∘L T i‖ ≤ rho ^ 2)
    (x : E) :
    ∑ i ∈ s, ‖T i x‖ ^ 2 ≤ rho ^ 2 * ‖x‖ ^ 2 := by
  let G : E →L[𝕜] E := ∑ i ∈ s, ContinuousLinearMap.adjoint (T i) ∘L T i
  have hNorm : ‖G‖ ≤ rho ^ 2 := hGram
  calc
    (∑ i ∈ s, ‖T i x‖ ^ 2) = RCLike.re (inner 𝕜 (G x) x) := by
      simp only [G, ContinuousLinearMap.sum_apply, sum_inner, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left (T i) x
    _ ≤ ‖G x‖ * ‖x‖ := re_inner_le_norm _ _
    _ ≤ (‖G‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (G.le_opNorm x) (norm_nonneg _)
    _ ≤ rho ^ 2 * ‖x‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hNorm (sq_nonneg ‖x‖)
      nlinarith

/-- Operator Cauchy–Schwarz, with a Gram-operator hypothesis rather than a
pointwise energy hypothesis. -/
theorem operator_sum_norm_le_of_gram_norm
    (s : Finset ι) (T : ι → E →L[𝕜] F) (rho : ℝ) (hrho : 0 ≤ rho)
    (hGram : ‖∑ i ∈ s, ContinuousLinearMap.adjoint (T i) ∘L T i‖ ≤ rho ^ 2) :
    ‖∑ i ∈ s, T i‖ ≤ Real.sqrt (s.card : ℝ) * rho :=
  operator_sum_norm_le_sqrt_card s T rho hrho
    (coefficient_energy_le_of_gram_norm s T rho hGram)

end HilbertCoefficientEnergy

section Counts

/-- The four oriented letters of a free group on two generators. -/
abbrev Letter := Fin 4

/-- `0 ↔ 3` and `1 ↔ 2` form the two inverse pairs. -/
def inverseLetter (a : Letter) : Letter := a.rev

@[simp] theorem inverseLetter_inverse (a : Letter) :
    inverseLetter (inverseLetter a) = a := by simp [inverseLetter]

theorem inverseLetter_ne (a : Letter) : inverseLetter a ≠ a := by
  have h : ∀ b : Letter, inverseLetter b ≠ b := by decide
  exact h a

/-- Legal letters following `a`: all letters except its inverse. -/
abbrev FollowingLetter (a : Letter) := {b : Letter // b ≠ inverseLetter a}

@[simp] theorem card_followingLetter (a : Letter) :
    Fintype.card (FollowingLetter a) = 3 := by
  simp [FollowingLetter, Fintype.card_subtype_compl]

/-- A genuine reduced tail; each next letter excludes the previous inverse. -/
def ReducedTail (a : Letter) : ℕ → Type
  | 0 => Unit
  | n + 1 => Σ b : FollowingLetter a, ReducedTail b.val n

noncomputable instance reducedTailFintype (a : Letter) (n : ℕ) :
    Fintype (ReducedTail a n) := by
  induction n generalizing a with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    change Fintype (Σ b : FollowingLetter a, ReducedTail b.val n)
    letI : ∀ b : FollowingLetter a, Fintype (ReducedTail b.val n) := fun b => ih b.val
    infer_instance

/-- Exactly three choices are available for each subsequent letter. -/
@[simp] theorem card_reducedTail (a : Letter) (n : ℕ) :
    Fintype.card (ReducedTail a n) = 3 ^ n := by
  induction n generalizing a with
  | zero => simp [ReducedTail]
  | succ n ih =>
    change Fintype.card (Σ b : FollowingLetter a, ReducedTail b.val n) = _
    rw [Fintype.card_sigma]
    simp [ih, pow_succ, mul_comm]

/-- A nonempty reduced word of length `t+1` is its first letter and reduced tail. -/
abbrev ReducedWord (t : ℕ) := Σ a : Letter, ReducedTail a t

/-- Exact count of reduced words of length `t+1`. -/
theorem card_reducedWord (t : ℕ) : Fintype.card (ReducedWord t) = 4 * 3 ^ t := by
  simp [ReducedWord, Fintype.card_sigma, mul_comm]


/-- Four choices for the first letter and three for each succeeding letter. -/
theorem reduced_word_geometric_sum (r : ℕ) :
    (∑ t ∈ Finset.range r, 4 * 3 ^ t) + 2 = 2 * 3 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- The numerical bound `1 + n ∑ 4·3ᵗ ≤ 2 n 3ʳ`, for `n ≥ 1`. -/
theorem short_word_count_bound (n r : ℕ) (hn : 1 ≤ n) :
    1 + n * (∑ t ∈ Finset.range r, 4 * 3 ^ t) ≤ 2 * n * 3 ^ r := by
  have h := reduced_word_geometric_sum r
  have heq : n * ((∑ t ∈ Finset.range r, 4 * 3 ^ t) + 2) =
      n * (2 * 3 ^ r) := congrArg (n * ·) h
  nlinarith

end Counts

end Nonadditivity.Linearization
