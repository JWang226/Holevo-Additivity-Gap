/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FreeCreation

/-! # Operator estimates behind Collins--Youn

The results here discharge concrete pieces of the free length-two estimate.
No external Haagerup or Collins--Youn inequality is assumed in these lemmas.
-/

noncomputable section

namespace Nonadditivity.CollinsYoun

open Nonadditivity.FreeModel Nonadditivity.FreeCreation
open scoped BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

section HilbertEstimates

variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sum_sq_of_inner_zero (f : I → E)
    (horth : ∀ i j, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  classical
  have hinner : inner ℂ (∑ i, f i) (∑ i, f i) = ∑ i, inner ℂ (f i) (f i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    exact Finset.sum_eq_single i
      (fun j _ hji => horth i j hji.symm) (by simp)
  have hr := congrArg Complex.re hinner
  have hn : ∀ x : E, Complex.re (inner ℂ x x) = ‖x‖ ^ 2 := by
    intro x
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Complex.re_sum, hn] using hr

theorem norm_sum_smul_sq_le (a : I → ℂ) (f : I → E) :
    ‖∑ i, a i • f i‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖f i‖ ^ 2 := by
  have hnorm : ‖∑ i, a i • f i‖ ≤ ∑ i, ‖a i‖ * ‖f i‖ := by
    simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => a i • f i)
  have hsum : 0 ≤ ∑ i, ‖a i‖ * ‖f i‖ := Finset.sum_nonneg (by intros; positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖a i‖) (fun i => ‖f i‖)
  nlinarith [norm_nonneg (∑ i, a i • f i)]

end HilbertEstimates

section ConeEstimates

variable {α I : Type*} [DecidableEq α] [Fintype I]

theorem mask_cone_inner_zero {s t : Letter α} (hne : s ≠ t)
    (f h : Hilbert (FreeGroup α)) :
    inner ℂ (mask (Cone s) f) (mask (Cone t) h) = 0 := by
  change (∑' x, inner ℂ (mask (Cone s) f x) (mask (Cone t) h x)) = 0
  have hz : ∀ x, inner ℂ (mask (Cone s) f x) (mask (Cone t) h x) = 0 := by
    intro x
    by_cases hs : Cone s x
    · have ht : ¬ Cone t x := fun ht => cone_disjoint hne x ⟨hs,ht⟩
      simp [mask_apply, ht]
    · simp [mask_apply, hs]
  simp_rw [hz]
  exact tsum_zero

theorem sum_cone_masks_eq (L : I → Letter α) (hL : Function.Injective L)
    (f : Hilbert (FreeGroup α)) :
    (∑ i, mask (Cone (L i)) f) = mask (fun x => ∃ i, Cone (L i) x) f := by
  classical
  ext x
  simp only [lp.coeFn_sum, Finset.sum_apply, mask_apply]
  by_cases hx : ∃ i, Cone (L i) x
  · obtain ⟨i,hi⟩ := hx
    rw [if_pos ⟨i,hi⟩]
    have hz : ∀ j ≠ i, ¬ Cone (L j) x := by
      intro j hji hj
      exact cone_disjoint (fun he => hji (hL he)) x ⟨hj,hi⟩
    calc
      (∑ j, if Cone (L j) x then f x else 0) =
          (if Cone (L i) x then f x else 0) :=
        Finset.sum_eq_single i (fun j _ hji => by simp [hz j hji]) (by simp)
      _ = f x := by simp [hi]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ Cone (L i) x := fun hi => hx ⟨i,hi⟩
    simp [hi]

/-- The energies of disjoint concrete first-letter projections are bounded
by the total Hilbert-space energy. -/
theorem sum_cone_mask_norm_sq_le (L : I → Letter α) (hL : Function.Injective L)
    (f : Hilbert (FreeGroup α)) :
    (∑ i, ‖mask (Cone (L i)) f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have hsum := norm_sum_sq_of_inner_zero (fun i => mask (Cone (L i)) f)
    (fun i j hij => mask_cone_inner_zero (fun he => hij (hL he)) f f)
  rw [sum_cone_masks_eq L hL f] at hsum
  have hn := mask_norm_le (fun x => ∃ i, Cone (L i) x) f
  nlinarith [norm_nonneg (mask (fun x => ∃ i, Cone (L i) x) f), norm_nonneg f]

/-- The corresponding annihilation operators satisfy the same row-energy bound. -/
theorem sum_annihilation_norm_sq_le (L : I → Letter α) (hL : Function.Injective L)
    (f : Hilbert (FreeGroup α)) :
    (∑ i, ‖(creation (L i)).adjoint f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  simp_rw [creation_adjoint, ContinuousLinearMap.comp_apply, leftRegular_preserves_norm]
  exact sum_cone_mask_norm_sq_le L hL f

end ConeEstimates

section LengthTwo

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem creation_comp_flip_zero (s : Letter α) :
    (creation s).comp (creation (flip s)) = 0 := by
  rw [creation_domain]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply,
    creation_apply, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hx : Cone (flip s) ((letter s)⁻¹ * x) <;> simp [hx]

def doubleCreation (i j : α) :
    Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  (creation (i,false)).comp (creation (j,true))

omit [Fintype α] in
@[simp] theorem doubleCreation_self (i : α) : doubleCreation i i = 0 := by
  simpa [doubleCreation, FreeCreation.flip] using creation_comp_flip_zero (i,false)

omit [Fintype α] in
theorem doubleCreation_norm_le (i j : α) (f : Hilbert (FreeGroup α)) :
    ‖doubleCreation i j f‖ ≤ ‖f‖ :=
  (creation_norm_le (i,false) (creation (j,true) f)).trans (creation_norm_le (j,true) f)

omit [Fintype α] in
/-- Distinct reduced two-letter creation ranges are orthogonal. -/
theorem doubleCreation_inner_zero (p q : α × α) (hpq : p ≠ q)
    (f h : Hilbert (FreeGroup α)) :
    inner ℂ (doubleCreation p.1 p.2 f) (doubleCreation q.1 q.2 h) = 0 := by
  by_cases hp : p.1 = p.2
  · simp [hp]
  by_cases hq : q.1 = q.2
  · simp [hq]
  by_cases hf : p.1 = q.1
  · have hs : p.2 ≠ q.2 := fun hs => hpq (Prod.ext hf hs)
    have hcp := creation_comp_creation_eq_shift
      (s := (p.1,false)) (t := (p.2,true)) (by simpa [FreeCreation.flip] using hp)
    have hcq := creation_comp_creation_eq_shift
      (s := (q.1,false)) (t := (q.2,true)) (by simpa [FreeCreation.flip] using hq)
    unfold doubleCreation
    rw [hcp, hcq]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hf, leftRegular_inner]
    exact creation_inner_zero (by simpa using hs) f h
  · exact creation_inner_zero (by simpa using hf) _ _

def coefficientLength (A : Matrix α α ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

omit [DecidableEq α] in
theorem coefficientLength_sq (A : Matrix α α ℂ) :
    coefficientLength A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

omit [DecidableEq α] in
theorem coefficientLength_nonneg (A : Matrix α α ℂ) : 0 ≤ coefficientLength A :=
  Real.sqrt_nonneg _

omit [DecidableEq α] in
theorem coefficientLength_eq_hsLength (A : Matrix α α ℂ) :
    coefficientLength A = AdjointPurity.hsLength A := by
  unfold coefficientLength AdjointPurity.hsLength
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]

/-- The no-cancellation operator has norm at most the coefficient ℓ² norm. -/
theorem double_creation_sum_norm_le (A : Matrix α α ℂ) :
    ‖∑ i, ∑ j, A i j • doubleCreation i j‖ ≤ coefficientLength A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (coefficientLength_nonneg A)
  intro f
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have horth : ∀ p q : α × α, p ≠ q →
      inner ℂ (A p.1 p.2 • doubleCreation p.1 p.2 f)
        (A q.1 q.2 • doubleCreation q.1 q.2 f) = 0 := by
    intro p q hpq
    simp [inner_smul_left, inner_smul_right, doubleCreation_inner_zero p q hpq f f]
  have hsum := norm_sum_sq_of_inner_zero
    (fun p : α × α => A p.1 p.2 • doubleCreation p.1 p.2 f) horth
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hsum
  dsimp only at hsum
  have henergy : (∑ i, ∑ j, ‖A i j • doubleCreation i j f‖ ^ 2) ≤
      (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_smul, mul_pow]
    have hn := doubleCreation_norm_le i j f
    have hs : ‖doubleCreation i j f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      nlinarith [norm_nonneg (doubleCreation i j f), norm_nonneg f]
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (coefficientLength_nonneg A) (norm_nonneg f))).mp
  rw [mul_pow, coefficientLength_sq, hsum]
  exact henergy

def mixed (A : Matrix α α ℂ) :
    Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  ∑ i, ∑ j, A i j • (creation (i,false)).comp (creation (j,false)).adjoint

/-- The one-cancellation operator has norm at most the coefficient ℓ² norm. -/
theorem mixed_norm_le (A : Matrix α α ℂ) : ‖mixed A‖ ≤ coefficientLength A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (coefficientLength_nonneg A)
  intro f
  let row : α → Hilbert (FreeGroup α) :=
    fun i => ∑ j, A i j • (creation (j,false)).adjoint f
  have he : mixed A f = ∑ i, creation (i,false) (row i) := by
    simp [mixed, row, map_sum]
  rw [he]
  have horth : ∀ i j : α, i ≠ j →
      inner ℂ (creation (i,false) (row i)) (creation (j,false) (row j)) = 0 := by
    intro i j hij
    exact creation_inner_zero (by simpa using hij) _ _
  have hsum := norm_sum_sq_of_inner_zero (fun i => creation (i,false) (row i)) horth
  have hrowenergy : (∑ j, ‖(creation (j,false)).adjoint f‖ ^ 2) ≤ ‖f‖ ^ 2 :=
    sum_annihilation_norm_sq_le (fun j : α => (j,false)) (by intro i j he; exact congrArg Prod.fst he) f
  have hrow : ∀ i, ‖row i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖f‖ ^ 2 := by
    intro i
    exact (norm_sum_smul_sq_le (A i) (fun j => (creation (j,false)).adjoint f)).trans
      (mul_le_mul_of_nonneg_left hrowenergy (by positivity))
  have henergy : (∑ i, ‖creation (i,false) (row i)‖ ^ 2) ≤
      (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hn := creation_norm_le (i,false) (row i)
    have hs : ‖creation (i,false) (row i)‖ ^ 2 ≤ ‖row i‖ ^ 2 := by
      nlinarith [norm_nonneg (creation (i,false) (row i)), norm_nonneg (row i)]
    exact hs.trans (hrow i)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (coefficientLength_nonneg A) (norm_nonneg f))).mp
  rw [mul_pow, coefficientLength_sq, hsum]
  exact henergy

def doubleAnnihilation (i j : α) :
    Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  (doubleCreation j i).adjoint

omit [Fintype α] in
theorem doubleAnnihilation_eq (i j : α) :
    doubleAnnihilation i j =
      (creation (i,true)).adjoint.comp (creation (j,false)).adjoint := by
  rw [doubleAnnihilation, doubleCreation, ContinuousLinearMap.adjoint_comp]

/-- The two-cancellation term has the same coefficient-norm bound, by the
actual Hilbert-space adjoint isometry. -/
theorem double_annihilation_sum_norm_le (A : Matrix α α ℂ) :
    ‖∑ i, ∑ j, A i j • doubleAnnihilation i j‖ ≤ coefficientLength A := by
  have hadj :
      ‖∑ i, ∑ j, A i j • doubleAnnihilation i j‖ =
        ‖∑ i, ∑ j, star (A i j) • doubleCreation j i‖ := by
    rw [← (ContinuousLinearMap.adjoint.norm_map
      (∑ i, ∑ j, A i j • doubleAnnihilation i j))]
    congr 1
    simp only [doubleAnnihilation, map_sum, map_smulₛₗ,
      ContinuousLinearMap.adjoint_adjoint, starRingEnd_apply]
  rw [hadj, Finset.sum_comm]
  have hbound := double_creation_sum_norm_le (fun i j => star (A j i))
  have he : coefficientLength (fun i j => star (A j i)) = coefficientLength A := by
    unfold coefficientLength
    simp only [norm_star]
    rw [Finset.sum_comm]
  exact hbound.trans_eq he

/-- The actual unnormalized single-factor regular polynomial. -/
def localPolynomial (A : Matrix α α ℂ) :
    Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  ∑ i, ∑ j, A i j • leftRegular ((FreeGroup.of i)⁻¹ * FreeGroup.of j)

/-- Splitting a polynomial with zero diagonal coefficients produces exactly
the three proved cancellation components. -/
theorem local_polynomial_three_components (A : Matrix α α ℂ)
    (hdiag : ∀ i, A i i = 0) :
    localPolynomial A = (∑ i, ∑ j, A i j • doubleCreation i j) + mixed A +
      ∑ i, ∑ j, A i j • doubleAnnihilation i j := by
  have he : ∀ i j, A i j • leftRegular ((FreeGroup.of i)⁻¹ * FreeGroup.of j) =
      A i j • doubleCreation i j +
        A i j • (creation (i,false)).comp (creation (j,false)).adjoint +
        A i j • doubleAnnihilation i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · have hl := length_two_decomposition (s := (i,false)) (t := (j,true))
        (by simpa [FreeCreation.flip] using hij)
      simp [letter, FreeCreation.flip] at hl
      rw [hl, smul_add, smul_add, doubleAnnihilation_eq]
      rfl
  unfold localPolynomial mixed
  simp_rw [he]
  simp only [Finset.sum_add_distrib]

def offDiagonal (A : Matrix α α ℂ) : Matrix α α ℂ :=
  fun i j => if i = j then 0 else A i j

omit [Fintype α] in
@[simp] theorem offDiagonal_diagonal (A : Matrix α α ℂ) (i : α) : offDiagonal A i i = 0 :=
  by simp [offDiagonal]

/-- Trace zero cancels the identical diagonal words in the actual operator. -/
theorem local_polynomial_offDiagonal (A : Matrix α α ℂ) (htrace : A.trace = 0) :
    localPolynomial A = localPolynomial (offDiagonal A) := by
  have he : ∀ i j, A i j • leftRegular ((FreeGroup.of i)⁻¹ * FreeGroup.of j) =
      offDiagonal A i j • leftRegular ((FreeGroup.of i)⁻¹ * FreeGroup.of j) +
        if i = j then A i i • ContinuousLinearMap.id ℂ (Hilbert (FreeGroup α)) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [offDiagonal]
    · simp [offDiagonal, hij]
  unfold localPolynomial
  simp_rw [he]
  simp only [Finset.sum_add_distrib]
  have hdiag :
      (∑ i, ∑ j, if i = j then A i i •
        ContinuousLinearMap.id ℂ (Hilbert (FreeGroup α)) else 0) = 0 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [← Finset.sum_smul]
    have ht : ∑ i, A i i = 0 := htrace
    rw [ht, zero_smul]
  rw [hdiag, add_zero]

theorem offDiagonal_coefficientLength_le (A : Matrix α α ℂ) :
    coefficientLength (offDiagonal A) ≤ coefficientLength A := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [offDiagonal, hij]
  · simp [offDiagonal, hij]

/-- The actual length-two Haagerup estimate for the trace-zero matrix
polynomial is proved from its three cancellation components. -/
theorem local_polynomial_norm_le_three_hs (A : Matrix α α ℂ) (htrace : A.trace = 0) :
    ‖localPolynomial A‖ ≤ 3 * AdjointPurity.hsLength A := by
  rw [local_polynomial_offDiagonal A htrace,
    local_polynomial_three_components _ (offDiagonal_diagonal A)]
  have hfirst := double_creation_sum_norm_le (offDiagonal A)
  have hmiddle := mixed_norm_le (offDiagonal A)
  have hlast := double_annihilation_sum_norm_le (offDiagonal A)
  have hn1 := norm_add_le
    (∑ i, ∑ j, offDiagonal A i j • doubleCreation i j) (mixed (offDiagonal A))
  have hn2 := norm_add_le
    ((∑ i, ∑ j, offDiagonal A i j • doubleCreation i j) + mixed (offDiagonal A))
    (∑ i, ∑ j, offDiagonal A i j • doubleAnnihilation i j)
  have hcoeff := offDiagonal_coefficientLength_le A
  rw [coefficientLength_eq_hsLength A] at hcoeff
  linarith

end LengthTwo

end Nonadditivity.CollinsYoun
