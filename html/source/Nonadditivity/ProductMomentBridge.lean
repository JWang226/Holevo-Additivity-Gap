/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarWordExpansion
import Nonadditivity.ProductHaagerupProduct

/-! # Matrix coefficient energy and free trace moments

The normalized vacuum trace controls the sum of squared coefficient operator
norms.  Together with product Haagerup this gives the operator-norm to moment
conversion used while replacing Haar tensor factors one at a time.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.ProductMomentBridge
open HaarWordExpansion RegularCoefficientEnergy
open scoped BigOperators InnerProductSpace ENNReal Matrix Matrix.Norms.L2Operator

/-- The C-star power identity at every positive integer, obtained from its
power-of-two version and cancellation in a submultiplicative estimate. -/
theorem norm_pow_selfAdjoint {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    (x : A) (hx : IsSelfAdjoint x) {m : ℕ} (hm : 0 < m) : ‖x ^ m‖ = ‖x‖ ^ m := by
  apply le_antisymm (norm_pow_le' x hm)
  by_cases hzero : x = 0
  · simp [hzero, hm.ne']
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hzero
    have hlt : m < 2 ^ m := Nat.lt_two_pow_self
    have hd : 0 < 2 ^ m - m := Nat.sub_pos_of_lt hlt
    have hs : m + (2 ^ m - m) = 2 ^ m := Nat.add_sub_of_le hlt.le
    have hb : ‖x‖ ^ (2 ^ m) ≤ ‖x ^ m‖ * ‖x‖ ^ (2 ^ m - m) := by
      calc
        _ = ‖x ^ (2 ^ m)‖ := (hx.norm_pow_two_pow m).symm
        _ = ‖x ^ m * x ^ (2 ^ m - m)‖ := by rw [← pow_add, hs]
        _ ≤ ‖x ^ m‖ * ‖x ^ (2 ^ m - m)‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pow_le' x hd) (norm_nonneg _)
    rw [← hs, pow_add] at hb
    simp only [Nat.add_sub_cancel_left] at hb
    exact le_of_mul_le_mul_right hb (pow_pos hn _)

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [Group G] [DecidableEq G]

/-- The Frobenius bound, expressed through the actual coefficient operators. -/
theorem coefficientOperator_norm_sq_le (A : Matrix ι ι ℂ) :
    ‖coefficientOperator A‖ ^ 2 ≤
      ∑ i : ι, ‖coefficientOperator A (EuclideanSpace.single i 1)‖ ^ 2 := by
  let c : ℝ := ∑ i : ι, ‖coefficientOperator A (EuclideanSpace.single i 1)‖ ^ 2
  have hc : 0 ≤ c := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖coefficientOperator A‖ ≤ Real.sqrt c := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hx : x = ∑ i : ι, x i • EuclideanSpace.single i 1 := by
      ext j
      simp [Pi.single_apply]
    have he : coefficientOperator A x =
        ∑ i : ι, x i • coefficientOperator A (EuclideanSpace.single i 1) := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [he, mul_pow, Real.sq_sqrt hc]
    have hcs := CollinsYoun.norm_sum_smul_sq_le (fun i => x i)
      (fun i => coefficientOperator A (EuclideanSpace.single i 1))
    simpa only [← PiLp.norm_sq_eq_of_L2, mul_comm] using hcs
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rwa [Real.sq_sqrt hc] at hs

theorem coefficient_energy_eq_vacuum_norm (f : MatrixPolynomial G ι)
    (x : CoefficientSpace ι) :
    (∑ g ∈ f.support, ‖coefficientOperator (f g) x‖ ^ 2) =
      ‖regularEval f (lp.single 2 (1 : G) x)‖ ^ 2 := by
  rw [regularEval_eq_regularPolynomial, regularPolynomial_single_one]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_sum_single (p := 2) (by norm_num)
      (fun g => coefficientOperator (f g) x) f.support).symm

/-- An even vacuum moment is exactly the energy of each identity column. -/
theorem power_vacuum_column_energy (f : MatrixPolynomial G ι)
    (hf : IsSelfAdjoint (regularEval f)) (q : ℕ) (i : ι) :
    ‖regularEval (f ^ q) (lp.single 2 (1 : G) (EuclideanSpace.single i 1))‖ ^ 2 =
      ((f ^ (2*q)) 1 i i).re := by
  let e : Hilbert G ι := lp.single 2 (1 : G) (EuclideanSpace.single i 1)
  let B := regularEval f
  have hstar : (B ^ q).adjoint = B ^ q := by
    exact (hf.pow q).star_eq
  have he : (B ^ q).adjoint ∘L (B ^ q) = regularEval (f ^ (2*q)) := by
    rw [hstar, map_pow]
    change B ^ q * B ^ q = B ^ (2*q)
    rw [← pow_add]
    congr 1
    omega
  rw [map_pow]
  change ‖(B ^ q) e‖ ^ 2 = _
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, he]
  dsimp [e]
  rw [lp.inner_single_left, regularEval_vacuum, EuclideanSpace.inner_single_left]
  change (star (1 : ℂ) * ((f ^ (2*q)) 1 *ᵥ Pi.single i 1) i).re = _
  simp

theorem power_coefficient_energy_le_trace [Nonempty ι]
    (f : MatrixPolynomial G ι) (hf : IsSelfAdjoint (regularEval f)) (q : ℕ) :
    (∑ g ∈ (f^q).support, ‖coefficientOperator ((f^q) g)‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * (vacuumTrace (f^(2*q))).re := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ ∑ g ∈ (f^q).support,
        ∑ i : ι, ‖coefficientOperator ((f^q) g) (EuclideanSpace.single i 1)‖ ^ 2 :=
      Finset.sum_le_sum (fun g _ => coefficientOperator_norm_sq_le _)
    _ = ∑ i : ι, ∑ g ∈ (f^q).support,
        ‖coefficientOperator ((f^q) g) (EuclideanSpace.single i 1)‖ ^ 2 :=
      Finset.sum_comm
    _ = ∑ i : ι, ((f ^ (2*q)) 1 i i).re := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coefficient_energy_eq_vacuum_norm, power_vacuum_column_energy f hf]
    _ = _ := by
      simp only [vacuumTrace, normalizedTrace, Complex.div_natCast_re,
        Matrix.trace, Matrix.diag_apply, Complex.re_sum]
      field_simp

theorem vacuumTrace_even_nonneg [Nonempty ι]
    (f : MatrixPolynomial G ι) (hf : IsSelfAdjoint (regularEval f)) (q : ℕ) :
    0 ≤ (vacuumTrace (f^(2*q))).re := by
  have h := power_coefficient_energy_le_trace f hf q
  have he : 0 ≤ ∑ g ∈ (f^q).support, ‖coefficientOperator ((f^q) g)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact nonneg_of_mul_nonneg_right (he.trans h) (Nat.cast_pos.mpr Fintype.card_pos)

section ProductGroup
open ProductHaagerupProduct
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem radius_one (q j : ℕ) : RadiusLe q (1 : GroupIndex α j) := by
  induction j with
  | zero => trivial
  | succ j ih => exact ⟨by simp, ih⟩

omit [Fintype α] in
theorem radius_mul {a b j : ℕ} (g h : GroupIndex α j)
    (hg : RadiusLe a g) (hh : RadiusLe b h) : RadiusLe (a+b) (g*h) := by
  induction j with
  | zero => trivial
  | succ j ih =>
    exact ⟨(FreeGroup.norm_mul_le g.1 h.1).trans (Nat.add_le_add hg.1 hh.1),
      ih g.2 h.2 hg.2 hh.2⟩

open scoped Pointwise in
omit [Fintype α] in
theorem support_pow_radius {j : ℕ} (f : MatrixPolynomial (GroupIndex α j) ι)
    (hf : ∀ g ∈ f.support, RadiusLe 1 g) (q : ℕ) :
    ∀ g ∈ (f^q).support, RadiusLe q g := by
  induction q with
  | zero =>
    intro g hg
    have he : g = 1 := by
      have hh := MonoidAlgebra.support_one_subset (by simpa only [pow_zero] using hg)
      simpa using hh
    subst g
    exact radius_one _ _
  | succ q ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul _ _ hg)
    exact radius_mul a b (ih a ha) (hf b hb)

theorem regularEval_radius_norm_sq_le {q j : ℕ}
    (f : MatrixPolynomial (GroupIndex α j) ι)
    (hf : ∀ g ∈ f.support, RadiusLe q g) :
    ‖regularEval f‖ ^ 2 ≤ ((q+1 : ℕ) : ℝ)^(3*j) *
      ∑ g ∈ f.support, ‖coefficientOperator (f g)‖ ^ 2 := by
  have he : (∑ g ∈ f.support,
      (liftOperator (coefficientOperator (f g))).comp (MatrixRegularRestriction.leftRegular g)) =
      regularPolynomial f.support f := by
    unfold regularPolynomial
    apply Finset.sum_congr rfl
    intro g hg
    congr 1
  rw [regularEval_eq_regularPolynomial, ← he]
  exact finite_polynomial_norm_sq_le f.support (fun g => coefficientOperator (f g)) hf

/-- Product-group regular norm versus its actual normalized even vacuum
moment.  The stronger radius factor is retained before the usual simplification. -/
theorem norm_even_pow_le_trace [Nonempty ι] {j : ℕ}
    (f : MatrixPolynomial (GroupIndex α j) ι)
    (hf : IsSelfAdjoint (regularEval f)) (hlinear : ∀ g ∈ f.support, RadiusLe 1 g)
    (q : ℕ) (hq : 1 ≤ q) :
    ‖regularEval f‖ ^ (2*q) ≤
      ((q+1 : ℕ) : ℝ)^(3*j) * (Fintype.card ι : ℝ) * (vacuumTrace (f^(2*q))).re := by
  calc
    _ = ‖regularEval (f^q)‖^2 := by
      rw [map_pow, norm_pow_selfAdjoint _ hf (by omega)]
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ ((q+1 : ℕ) : ℝ)^(3*j) *
        ∑ g ∈ (f^q).support, ‖coefficientOperator ((f^q) g)‖ ^ 2 :=
      regularEval_radius_norm_sq_le (f^q) (support_pow_radius f hlinear q)
    _ ≤ ((q+1 : ℕ) : ℝ)^(3*j) *
        ((Fintype.card ι : ℝ) * (vacuumTrace (f^(2*q))).re) :=
      mul_le_mul_of_nonneg_left (power_coefficient_energy_le_trace f hf q) (by positivity)
    _ = _ := by ring

/-- The matrix-coefficient product-group moment conversion used in BC
Lemma 9.4, with the manuscript's factor `2*r*p^(3*j)`. -/
theorem norm_pow_le_two_card_moment [Nonempty ι] {j p : ℕ}
    (f : MatrixPolynomial (GroupIndex α j) ι)
    (hf : IsSelfAdjoint (regularEval f)) (hlinear : ∀ g ∈ f.support, RadiusLe 1 g)
    (hp : Even p) (hp2 : 2 ≤ p) :
    ‖regularEval f‖ ^ p ≤
      2 * (Fintype.card ι : ℝ) * (p : ℝ)^(3*j) * (vacuumTrace (f^p)).re := by
  obtain ⟨q,hq⟩ := hp
  have hq1 : 1 ≤ q := by omega
  have hpq : p = 2*q := by omega
  rw [hpq]
  have hv := vacuumTrace_even_nonneg f hf q
  apply (norm_even_pow_le_trace f hf hlinear q hq1).trans
  have hpow : ((q+1 : ℕ) : ℝ)^(3*j) ≤ ((2*q : ℕ) : ℝ)^(3*j) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (show q+1 ≤ 2*q by omega)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have ht := mul_le_mul_of_nonneg_right hpow hcard
  have ht' := mul_le_mul_of_nonneg_right ht hv
  calc
    _ ≤ ((2*q : ℕ) : ℝ)^(3*j) * (Fintype.card ι : ℝ) * (vacuumTrace (f^(2*q))).re := ht'
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity :
          0 ≤ ((2*q : ℕ) : ℝ)^(3*j)) hcard) hv]

/-- Reindexing only the regular norm leaves the original coefficient trace
and the original polynomial powers intact. -/
theorem regularEval_radius_norm_sq_le_of_injective {q j : ℕ}
    (φ : G →* GroupIndex α j) (hφ : Function.Injective φ)
    (f : MatrixPolynomial G ι) (hf : ∀ g ∈ f.support, RadiusLe q (φ g)) :
    ‖regularEval f‖ ^ 2 ≤ ((q+1 : ℕ) : ℝ)^(3*j) *
      ∑ g ∈ f.support, ‖coefficientOperator (f g)‖ ^ 2 := by
  have hs : ∀ g ∈ f.support.image φ, RadiusLe q g := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    exact hf a ha
  have hb := finite_polynomial_norm_sq_le (f.support.image φ)
    (fun g => coefficientOperator (Function.extend φ f 0 g)) hs
  change ‖regularPolynomial (f.support.image φ) (Function.extend φ f 0)‖^2 ≤ _ at hb
  rw [MatrixRegularRestriction.matrixPolynomial_injective_norm_eq φ hφ] at hb
  rw [regularEval_eq_regularPolynomial]
  simpa only [Finset.sum_image hφ.injOn, hφ.extend_apply] using hb

open scoped Pointwise in
omit [Fintype α] in
theorem support_pow_radius_image {j : ℕ} (φ : G →* GroupIndex α j)
    (f : MatrixPolynomial G ι) (hf : ∀ g ∈ f.support, RadiusLe 1 (φ g)) (q : ℕ) :
    ∀ g ∈ (f^q).support, RadiusLe q (φ g) := by
  induction q with
  | zero =>
    intro g hg
    have he : g = 1 := by
      have hh := MonoidAlgebra.support_one_subset (by simpa only [pow_zero] using hg)
      simpa using hh
    rw [he, map_one]
    exact radius_one _ _
  | succ q ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_mul _ _ hg)
    rw [map_mul]
    exact radius_mul (φ a) (φ b) (ih a ha) (hf b hb)

theorem norm_pow_le_two_card_moment_of_injective [Nonempty ι] {j p : ℕ}
    (φ : G →* GroupIndex α j) (hφ : Function.Injective φ)
    (f : MatrixPolynomial G ι) (hf : IsSelfAdjoint (regularEval f))
    (hlinear : ∀ g ∈ f.support, RadiusLe 1 (φ g)) (hp : Even p) (hp2 : 2 ≤ p) :
    ‖regularEval f‖ ^ p ≤
      2 * (Fintype.card ι : ℝ) * (p : ℝ)^(3*j) * (vacuumTrace (f^p)).re := by
  obtain ⟨q,hq⟩ := hp
  have hq1 : 1 ≤ q := by omega
  have hpq : p = 2*q := by omega
  rw [hpq]
  have hv := vacuumTrace_even_nonneg f hf q
  have he : ‖regularEval f‖^(2*q) = ‖regularEval (f^q)‖^2 := by
    rw [map_pow, norm_pow_selfAdjoint _ hf (by omega), ← pow_mul]
    congr 1
    omega
  have hb := regularEval_radius_norm_sq_le_of_injective φ hφ (f^q)
    (support_pow_radius_image φ f hlinear q)
  rw [he]
  apply hb.trans
  have ht := mul_le_mul_of_nonneg_left (power_coefficient_energy_le_trace f hf q)
    (by positivity : 0 ≤ ((q+1 : ℕ) : ℝ)^(3*j))
  apply ht.trans
  have hpow : ((q+1 : ℕ) : ℝ)^(3*j) ≤ ((2*q : ℕ) : ℝ)^(3*j) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (show q+1 ≤ 2*q by omega)
  have hs := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg (by positivity : 0 ≤ (Fintype.card ι : ℝ)) hv)
  nlinarith [mul_nonneg (by positivity : 0 ≤ ((2*q : ℕ) : ℝ)^(3*j))
    (mul_nonneg (by positivity : 0 ≤ (Fintype.card ι : ℝ)) hv)]

/-- The usual function-indexed product embeds into the recursive product. -/
def functionGroupHom (α : Type*) : (j : ℕ) →
    (Fin j → FreeGroup α) →* GroupIndex α j
  | 0 => { toFun := fun _ => PUnit.unit, map_one' := rfl, map_mul' := fun _ _ => rfl }
  | j+1 => {
      toFun := fun g => (g 0, functionGroupHom α j (fun r => g r.succ))
      map_one' := Prod.ext rfl (map_one (functionGroupHom α j))
      map_mul' := fun g h => Prod.ext rfl
        (map_mul (functionGroupHom α j) (fun r => g r.succ) (fun r => h r.succ)) }

omit [DecidableEq α] [Fintype α] in
theorem functionGroupHom_injective (j : ℕ) : Function.Injective (functionGroupHom α j) := by
  induction j with
  | zero => intro g h _; exact Subsingleton.elim _ _
  | succ j ih =>
    intro g h he
    have h0 := congrArg Prod.fst he
    have hs := ih (congrArg Prod.snd he)
    funext r
    exact Fin.cases h0 (fun r => congrFun hs r) r

omit [Fintype α] in
theorem radius_functionGroupHom {q j : ℕ} (g : Fin j → FreeGroup α)
    (hg : ∀ r, FreeGroup.norm (g r) ≤ q) : RadiusLe q (functionGroupHom α j g) := by
  induction j with
  | zero => trivial
  | succ j ih => exact ⟨hg 0, ih (fun r => g r.succ) (fun r => hg r.succ)⟩

/-- The full BC moment conversion on the actual function-indexed product
free group used by the structured polynomial and Haar construction. -/
theorem norm_pow_le_two_card_moment_function [Nonempty ι] {j p : ℕ}
    (f : MatrixPolynomial (Fin j → FreeGroup α) ι)
    (hf : IsSelfAdjoint (regularEval f))
    (hlinear : ∀ g ∈ f.support, ∀ r, FreeGroup.norm (g r) ≤ 1)
    (hp : Even p) (hp2 : 2 ≤ p) :
    ‖regularEval f‖ ^ p ≤
      2 * (Fintype.card ι : ℝ) * (p : ℝ)^(3*j) * (vacuumTrace (f^p)).re := by
  exact norm_pow_le_two_card_moment_of_injective (functionGroupHom α j)
    (functionGroupHom_injective j) f hf
    (fun g hg => radius_functionGroupHom g (hlinear g hg)) hp hp2

end ProductGroup

end Nonadditivity.ProductMomentBridge
