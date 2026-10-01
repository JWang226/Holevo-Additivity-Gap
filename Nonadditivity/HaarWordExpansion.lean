/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.StructuredHaarModel
import Nonadditivity.FiniteMomentMatching
import Mathlib.Algebra.MonoidAlgebra.Lift

/-! # Literal matrix-coefficient word expansions of trace moments

Matrix coefficients are retained inside a noncommutative monoid algebra.
Evaluation is a ring homomorphism, so powers and their Haar integrals expand
into the actual word coefficients without a scalar coefficient norm estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarWordExpansion

open MeasureTheory RegularCoefficientEnergy
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator Kronecker

variable {G ι ν : Type*} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

abbrev MatrixPolynomial (G ι : Type*) [Fintype ι] [DecidableEq ι] :=
  MonoidAlgebra (Matrix ι ι ℂ) G

def coefficientHom : Matrix ι ι ℂ →+* Matrix (ι × ν) (ι × ν) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix ν ν ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' A B := Matrix.add_kronecker _ _ _
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

def wordHom (ρ : G →* Matrix ν ν ℂ) : G →* Matrix (ι × ν) (ι × ν) ℂ where
  toFun g := (1 : Matrix ι ι ℂ) ⊗ₖ ρ g
  map_one' := by rw [map_one, Matrix.one_kronecker_one]
  map_mul' g h := by rw [map_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

omit [DecidableEq G] in
theorem coefficient_word_commute (ρ : G →* Matrix ν ν ℂ) (A : Matrix ι ι ℂ) (g : G) :
    Commute (coefficientHom (ν := ν) A) (wordHom (ι := ι) ρ g) := by
  change (A ⊗ₖ (1 : Matrix ν ν ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ ρ g) =
    ((1 : Matrix ι ι ℂ) ⊗ₖ ρ g) * (A ⊗ₖ (1 : Matrix ν ν ℂ))
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

def finiteEval (ρ : G →* Matrix ν ν ℂ) :
    MatrixPolynomial G ι →+* Matrix (ι × ν) (ι × ν) ℂ :=
  MonoidAlgebra.liftNCRingHom coefficientHom (wordHom ρ) (coefficient_word_commute ρ)

omit [DecidableEq G] in
@[simp] theorem finiteEval_single (ρ : G →* Matrix ν ν ℂ) (g : G) (A : Matrix ι ι ℂ) :
    finiteEval ρ (MonoidAlgebra.single g A) = A ⊗ₖ ρ g := by
  simp only [finiteEval, MonoidAlgebra.liftNCRingHom_single, coefficientHom, wordHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

omit [DecidableEq G] in
theorem finiteEval_eq_sum (ρ : G →* Matrix ν ν ℂ) (f : MatrixPolynomial G ι) :
    finiteEval ρ f = ∑ g ∈ f.support, f g ⊗ₖ ρ g := by
  conv_lhs => rw [← MonoidAlgebra.sum_single f]
  change finiteEval ρ (∑ g ∈ f.support, MonoidAlgebra.single g (f g)) = _
  simp only [map_sum, finiteEval_single]

def regularCoefficientHom : Matrix ι ι ℂ →+* (Hilbert G ι →L[ℂ] Hilbert G ι) where
  toFun := RegularFactorization.rectLift
  map_zero' := RegularFactorization.rectLift_zero
  map_one' := RegularFactorization.rectLift_one
  map_add' := RegularFactorization.rectLift_add
  map_mul' := RegularFactorization.rectLift_mul

def regularWordHom : G →* (Hilbert G ι →L[ℂ] Hilbert G ι) where
  toFun := leftRegular
  map_one' := RegularFactorization.shift_one
  map_mul' g h := (RegularFactorization.shift_mul g h).symm

def regularEval : MatrixPolynomial G ι →+* (Hilbert G ι →L[ℂ] Hilbert G ι) :=
  MonoidAlgebra.liftNCRingHom regularCoefficientHom regularWordHom
    (fun A g => show Commute (RegularFactorization.rectLift A) (leftRegular g) from
      RegularFactorization.rectLift_shift A g)

@[simp] theorem regularEval_single (g : G) (A : Matrix ι ι ℂ) :
    regularEval (MonoidAlgebra.single g A) = RegularFactorization.term A g := by
  rw [regularEval, MonoidAlgebra.liftNCRingHom_single]
  rfl

theorem regularEval_eq_sum (f : MatrixPolynomial G ι) :
    regularEval f = ∑ g ∈ f.support, RegularFactorization.term (f g) g := by
  conv_lhs => rw [← MonoidAlgebra.sum_single f]
  change regularEval (∑ g ∈ f.support, MonoidAlgebra.single g (f g)) = _
  simp only [map_sum, regularEval_single]

theorem regularEval_eq_regularPolynomial (f : MatrixPolynomial G ι) :
    regularEval f = regularPolynomial f.support f := by
  rw [regularEval_eq_sum, RegularFactorization.polynomial_eq]

theorem regularEval_vacuum (f : MatrixPolynomial G ι) (x : CoefficientSpace ι) :
    regularEval f (lp.single 2 (1 : G) x) 1 = coefficientOperator (f 1) x := by
  rw [regularEval_eq_regularPolynomial, regularPolynomial_single_one]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  by_cases h : (1 : G) ∈ f.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h, coefficientOperator]

def normalizedTrace (A : Matrix ι ι ℂ) : ℂ := A.trace / Fintype.card ι

def vacuumTrace (f : MatrixPolynomial G ι) : ℂ := normalizedTrace (f 1)

omit [DecidableEq G] in
theorem normalizedTrace_finiteEval (ρ : G →* Matrix ν ν ℂ) (f : MatrixPolynomial G ι) :
    normalizedTrace (finiteEval ρ f) =
      ∑ g ∈ f.support, normalizedTrace (f g) * normalizedTrace (ρ g) := by
  rw [finiteEval_eq_sum]
  simp only [normalizedTrace, Matrix.trace_sum, Matrix.trace_kronecker, Fintype.card_prod,
    Nat.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g hg
  ring

omit [DecidableEq G] in
theorem normalizedTrace_pow (ρ : G →* Matrix ν ν ℂ) (f : MatrixPolynomial G ι) (p : ℕ) :
    normalizedTrace ((finiteEval ρ f)^p) =
      ∑ g ∈ (f^p).support, normalizedTrace ((f^p) g) * normalizedTrace (ρ g) := by
  rw [← map_pow, normalizedTrace_finiteEval]

omit [DecidableEq G] in
/-- The vacuum trace is tracial on the actual matrix-valued group algebra. -/
theorem vacuumTrace_mul_comm (f h : MatrixPolynomial G ι) :
    vacuumTrace (f*h) = vacuumTrace (h*f) := by
  unfold vacuumTrace normalizedTrace
  rw [MonoidAlgebra.mul_apply_left, MonoidAlgebra.mul_apply_right]
  congr 1
  simp only [Finsupp.sum, Matrix.trace_sum, mul_one, one_mul]
  apply Finset.sum_congr rfl
  intro g hg
  exact Matrix.trace_mul_comm _ _

theorem norm_diagonal_coefficient_le (f : MatrixPolynomial G ι) (i : ι) :
    ‖f 1 i i‖ ≤ ‖regularEval f‖ := by
  let x : CoefficientSpace ι := EuclideanSpace.single i 1
  let e : Hilbert G ι := lp.single 2 (1:G) x
  have hx : ‖x‖ = 1 := by simp [x, EuclideanSpace.norm_single]
  have he : ‖e‖ = 1 := by simp [e, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), hx]
  have hv : regularEval f e 1 i = f 1 i i := by
    rw [show e = lp.single 2 (1:G) x from rfl, regularEval_vacuum]
    change ((f 1) *ᵥ Pi.single i 1) i = _
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  calc
    ‖f 1 i i‖ = ‖regularEval f e 1 i‖ := by rw [hv]
    _ ≤ ‖regularEval f e 1‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖regularEval f e‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖regularEval f‖ * ‖e‖ := (regularEval f).le_opNorm e
    _ = ‖regularEval f‖ := by rw [he, mul_one]

/-- A normalized trace of matrix-valued vacuum coefficients is contractive. -/
theorem norm_vacuumTrace_le [Nonempty ι] (f : MatrixPolynomial G ι) :
    ‖vacuumTrace f‖ ≤ ‖regularEval f‖ := by
  have hc : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  unfold vacuumTrace normalizedTrace
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hc).mpr
  calc
    ‖(f 1).trace‖ ≤ ∑ i, ‖f 1 i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖regularEval f‖ := Finset.sum_le_sum fun i _ => norm_diagonal_coefficient_le f i
    _ = ‖regularEval f‖ * Fintype.card ι := by simp [mul_comm]

/-- This controls the free identity term at every moment order. -/
theorem vacuumTrace_pow_re_le [Nonempty ι] (f : MatrixPolynomial G ι) (p : ℕ) :
    (vacuumTrace (f^p)).re ≤ ‖regularEval f‖^p := by
  calc
    (vacuumTrace (f^p)).re ≤ ‖vacuumTrace (f^p)‖ := Complex.re_le_norm _
    _ ≤ ‖regularEval (f^p)‖ := norm_vacuumTrace_le _
    _ = ‖(regularEval f)^p‖ := by rw [map_pow]
    _ ≤ ‖regularEval f‖^p := by
      cases p with
      | zero => exact ContinuousLinearMap.norm_id_le
      | succ p => exact norm_pow_le' _ (Nat.succ_pos p)

/-- Keep all matrix coefficients grouped: the entire squared column energy of
the coefficients of a power is controlled by the free operator norm. -/
theorem coefficient_power_energy (f : MatrixPolynomial G ι) (p : ℕ)
    (x : CoefficientSpace ι) :
    ∑ g ∈ (f^p).support, ‖coefficientOperator ((f^p) g) x‖^2 ≤
      ‖regularEval f‖^(2*p) * ‖x‖^2 := by
  have hp : ‖regularEval (f^p)‖ ≤ ‖regularEval f‖^p := by
    rw [map_pow]
    cases p with
    | zero => exact ContinuousLinearMap.norm_id_le
    | succ p => exact norm_pow_le' _ (Nat.succ_pos p)
  have he := coefficient_energy_le (f^p).support (f^p) x
  rw [← regularEval_eq_regularPolynomial] at he
  apply he.trans
  have hs := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖x‖)
  simpa only [← pow_mul, Nat.mul_comm p 2] using hm

open scoped Pointwise in
theorem support_pow_length_le (f : MatrixPolynomial G ι) (len : G → ℕ)
    (hone : len 1 = 0) (hmul : ∀ g h, len (g*h) ≤ len g + len h)
    (r : ℕ) (hf : ∀ g ∈ f.support, len g ≤ r) (p : ℕ) :
    ∀ g ∈ (f^p).support, len g ≤ p*r := by
  induction p with
  | zero =>
      intro g hg
      have : g = 1 := by
        have hh := MonoidAlgebra.support_one_subset (by simpa only [pow_zero] using hg)
        simpa using hh
      simp [this, hone]
  | succ p ih =>
      intro g hg
      rw [pow_succ] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul _ _ hg)
      exact (hmul a b).trans (by nlinarith [ih a ha, hf b hb])

section Integration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ρ : Ω → G →* Matrix ν ν ℂ)

omit [IsProbabilityMeasure μ] [DecidableEq G] in
/-- The expected normalized trace is exactly the sum of word weights. -/
theorem integral_normalizedTrace_pow (f : MatrixPolynomial G ι) (p : ℕ)
    (hint : ∀ g, Integrable (fun ω => normalizedTrace (ρ ω g)) μ) :
    (∫ ω, normalizedTrace ((finiteEval (ρ ω) f)^p) ∂μ) =
      ∑ g ∈ (f^p).support,
        normalizedTrace ((f^p) g) * ∫ ω, normalizedTrace (ρ ω g) ∂μ := by
  simp_rw [normalizedTrace_pow]
  rw [integral_finset_sum _ (fun g _ => (hint g).const_mul _)]
  simp only [integral_const_mul]

/-- Subtracting the free moment removes precisely the identity word. -/
theorem integral_moment_error [Nonempty ν] (f : MatrixPolynomial G ι) (p : ℕ)
    (hint : ∀ g, Integrable (fun ω => normalizedTrace (ρ ω g)) μ) :
    (∫ ω, normalizedTrace ((finiteEval (ρ ω) f)^p) ∂μ) - vacuumTrace (f^p) =
      ∑ g ∈ (f^p).support.erase 1,
        normalizedTrace ((f^p) g) * ∫ ω, normalizedTrace (ρ ω g) ∂μ := by
  rw [integral_normalizedTrace_pow μ ρ f p hint]
  have hc : (Fintype.card ν : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hρ : (∫ ω, normalizedTrace (ρ ω 1) ∂μ) = 1 := by
    simp [normalizedTrace, map_one, Matrix.trace_one, hc]
  by_cases h : (1:G) ∈ (f^p).support
  · rw [← Finset.sum_erase_add _ _ h, hρ, mul_one]
    change _ + vacuumTrace (f^p) - vacuumTrace (f^p) = _
    abel
  · have hz : vacuumTrace (f^p) = 0 := by
      simp [vacuumTrace, Finsupp.notMem_support_iff.mp h, normalizedTrace]
    rw [hz, sub_zero, Finset.erase_eq_of_notMem h]

end Integration

section LengthExpansion
variable {α : Type*} [DecidableEq α]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ρ : Ω → FreeGroup α →* Matrix ν ν ℂ)

def lengthContribution (f : MatrixPolynomial (FreeGroup α) ι) (p t : ℕ) : ℂ :=
  ∑ g ∈ ((f^p).support.erase 1).filter (fun g => FreeGroup.norm g = t),
    normalizedTrace ((f^p) g) * ∫ ω, normalizedTrace (ρ ω g) ∂μ

/-- The word-length decomposition of the actual trace-moment error. -/
theorem integral_moment_error_by_length [Nonempty ν]
    (f : MatrixPolynomial (FreeGroup α) ι) (p : ℕ)
    (hlinear : ∀ g ∈ f.support, FreeGroup.norm g ≤ 1)
    (hint : ∀ g, Integrable (fun ω => normalizedTrace (ρ ω g)) μ) :
    (∫ ω, normalizedTrace ((finiteEval (ρ ω) f)^p) ∂μ) - vacuumTrace (f^p) =
      ∑ t ∈ Finset.Icc 1 p, lengthContribution μ ρ f p t := by
  rw [integral_moment_error μ ρ f p hint]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro g hg
  have hs := (Finset.mem_erase.mp hg).2
  have hn := (Finset.mem_erase.mp hg).1
  have h0 : 0 < FreeGroup.norm g := Nat.pos_of_ne_zero (by
    intro hz
    exact hn (FreeGroup.norm_eq_zero.mp hz))
  have hp := support_pow_length_le f FreeGroup.norm (by simp)
    FreeGroup.norm_mul_le 1 hlinear p g hs
  simp only [Finset.mem_Icc]
  exact ⟨h0, by simpa using hp⟩

end LengthExpansion

section ActualPolynomial
variable {G : Type} [Group G] [DecidableEq G]

def representationMatrix (π : G →* unitary (Matrix ν ν ℂ)) : G →* Matrix ν ν ℂ :=
  (unitary (Matrix ν ν ℂ)).subtype.comp π

/-- The existing polynomial's matrix coefficients, with coincident words combined. -/
def ofPolynomial (P : PolynomialReduction.Polynomial G) : MatrixPolynomial G P.Index :=
  ∑ g ∈ P.support, MonoidAlgebra.single g (P.coefficient g)

omit [DecidableEq G] in
theorem finiteEval_ofPolynomial (P : PolynomialReduction.Polynomial G)
    (π : G →* unitary (Matrix ν ν ℂ)) :
    finiteEval (representationMatrix π) (ofPolynomial P) = P.finiteEval π := by
  simp only [ofPolynomial, map_sum, finiteEval_single]
  rfl

theorem regularEval_ofPolynomial (P : PolynomialReduction.Polynomial G) :
    regularEval (ofPolynomial P) = P.regularEval := by
  simp only [ofPolynomial, map_sum, regularEval_single]
  exact (RegularFactorization.polynomial_eq P.support P.coefficient).symm

end ActualPolynomial

section CanonicalHaar

def haarRepresentation (n N : ℕ) (ω : HaarModel.Sample 2 n N) :=
  representationMatrix (StructuredHaarModel.sampleRepresentation n N ω)

theorem integrable_haar_word_trace (n N : ℕ) (g : StructuredLinearization.G n) :
    Integrable (fun ω => normalizedTrace (haarRepresentation n N ω g))
      (HaarModel.sampleMeasure 2 n N) := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  unfold normalizedTrace Matrix.trace
  apply Continuous.div_const
  apply continuous_finset_sum
  intro i hi
  exact (StructuredHaarModel.continuous_tensorRepresentation n N n g).matrix_elem i i

/-- The literal expected moment of the existing Haar polynomial is its free
vacuum moment plus the nonidentity word contributions. No integration premise
or matrix-coefficient scalarization is used. -/
theorem canonical_integral_moment_error (n N : ℕ)
    (P : PolynomialReduction.Polynomial (StructuredLinearization.G n)) (p : ℕ) :
    (∫ ω, normalizedTrace ((P.finiteEval (StructuredHaarModel.sampleRepresentation n N ω))^p)
      ∂HaarModel.sampleMeasure 2 n N) - vacuumTrace ((ofPolynomial P)^p) =
      ∑ g ∈ ((ofPolynomial P)^p).support.erase 1,
        normalizedTrace (((ofPolynomial P)^p) g) *
          ∫ ω, normalizedTrace (haarRepresentation n N ω g)
            ∂HaarModel.sampleMeasure 2 n N := by
  simpa only [haarRepresentation, finiteEval_ofPolynomial] using
    integral_moment_error (HaarModel.sampleMeasure 2 n N) (haarRepresentation n N)
      (ofPolynomial P) p (integrable_haar_word_trace n N)

end CanonicalHaar

end Nonadditivity.HaarWordExpansion
