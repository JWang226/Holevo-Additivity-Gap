/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularFactorization
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! # Constructed polynomial shortening

The support at each step is obtained by cutting the actual reduced words. The
coefficient matrices are the positive-Gram factors, evaluated simultaneously
at every finite representation and at the infinite regular representation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.PolynomialReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open FiniteSetFactorization RegularCoefficientEnergy

section Support
variable {α : Type} [DecidableEq α]

def firstHalf (r : ℕ) (w : FreeGroup α) : FreeGroup α :=
  FreeGroup.mk (w.toWord.take r)

def suffix (r : ℕ) (w : FreeGroup α) : FreeGroup α :=
  FreeGroup.mk (w.toWord.drop r)

theorem firstHalf_mul_suffix (r : ℕ) (w : FreeGroup α) : firstHalf r w * suffix r w = w := by
  simp only [firstHalf, suffix, FreeGroup.mul_mk, List.take_append_drop, FreeGroup.mk_toWord]

theorem norm_firstHalf_le (r : ℕ) (w : FreeGroup α) : FreeGroup.norm (firstHalf r w) ≤ r := by
  exact FreeGroup.norm_mk_le.trans (by simp)

theorem norm_suffix_le (r : ℕ) (w : FreeGroup α) (h : FreeGroup.norm w ≤ 2*r) :
    FreeGroup.norm (suffix r w) ≤ r := by
  have hlen : w.toWord.length ≤ 2*r := h
  exact FreeGroup.norm_mk_le.trans (by simp only [List.length_drop]; omega)

/-- The actual two halves of each supported word, with the first half inverted. -/
def splitSupport (T : Finset (FreeGroup α)) (r : ℕ) : Finset (FreeGroup α) :=
  insert 1 ((T.image fun w => (firstHalf r w)⁻¹) ∪ T.image (suffix r))

@[simp] theorem one_mem_splitSupport (T : Finset (FreeGroup α)) (r : ℕ) :
    (1 : FreeGroup α) ∈ splitSupport T r := by simp [splitSupport]

theorem subset_difference_splitSupport (T : Finset (FreeGroup α)) (r : ℕ) :
    T ⊆ Linearization.differenceSupport (splitSupport T r) := by
  intro w hw
  apply Linearization.mem_differenceSupport.mpr
  refine ⟨(firstHalf r w)⁻¹, ?_, suffix r w, ?_, ?_⟩
  · simp [splitSupport, Finset.mem_image_of_mem _ hw]
  · simp [splitSupport, Finset.mem_image_of_mem _ hw]
  · simpa using firstHalf_mul_suffix r w

theorem splitSupport_degree (T : Finset (FreeGroup α)) (r : ℕ)
    (hT : ∀ w ∈ T, FreeGroup.norm w ≤ 2*r) :
    ∀ w ∈ splitSupport T r, FreeGroup.norm w ≤ r := by
  intro w hw
  simp only [splitSupport, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hw
  rcases hw with rfl | (⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩)
  · simp
  · simpa only [FreeGroup.norm_inv_eq] using norm_firstHalf_le r v
  · exact norm_suffix_le r v (hT v hv)

theorem splitSupport_card (T : Finset (FreeGroup α)) (r : ℕ) :
    (splitSupport T r).card ≤ 1 + 2*T.card := by
  calc
    (splitSupport T r).card ≤
        (((T.image fun w => (firstHalf r w)⁻¹) ∪ T.image (suffix r))).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (T.image fun w => (firstHalf r w)⁻¹).card + (T.image (suffix r)).card + 1 :=
      Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ T.card + T.card + 1 := Nat.add_le_add_right
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le) 1
    _ = 1 + 2*T.card := by omega
end Support

/-- A literal finite matrix-coefficient polynomial, with its coefficient space. -/
structure Polynomial (G : Type*) where
  Index : Type
  fintype : Fintype Index
  decEq : DecidableEq Index
  nonempty : Nonempty Index
  support : Finset G
  coefficient : G → Matrix Index Index ℂ

attribute [instance] Polynomial.fintype Polynomial.decEq Polynomial.nonempty

namespace Polynomial
variable {G : Type} [Group G] [DecidableEq G]

def finiteEval (P : Polynomial G) {ν : Type*} [Fintype ν] [DecidableEq ν]
    (π : G →* unitary (Matrix ν ν ℂ)) : Matrix (P.Index × ν) (P.Index × ν) ℂ :=
  ∑ w ∈ P.support, P.coefficient w ⊗ₖ (π w : Matrix ν ν ℂ)

def regularEval (P : Polynomial G) := regularPolynomial P.support P.coefficient

def normalizedCoefficient (P : Polynomial G) (w : G) : Matrix P.Index P.Index ℂ :=
  if w ∈ P.support then P.coefficient w else 0

theorem finiteEval_enlarge (P : Polynomial G) {ν : Type*} [Fintype ν] [DecidableEq ν]
    (π : G →* unitary (Matrix ν ν ℂ)) (S : Finset G)
    (hcover : P.support ⊆ Linearization.differenceSupport S) :
    polynomial S P.normalizedCoefficient π = P.finiteEval π := by
  unfold polynomial finiteEval
  symm
  calc
    (∑ w ∈ P.support, P.coefficient w ⊗ₖ (π w : Matrix ν ν ℂ)) =
        ∑ w ∈ P.support, P.normalizedCoefficient w ⊗ₖ (π w : Matrix ν ν ℂ) := by
      apply Finset.sum_congr rfl
      intro w hw
      simp [normalizedCoefficient, hw]
    _ = _ := Finset.sum_subset hcover (by
      intro w hw hnot
      simp [normalizedCoefficient, hnot])

theorem regularEval_enlarge (P : Polynomial G) (S : Finset G)
    (hcover : P.support ⊆ Linearization.differenceSupport S) :
    regularPolynomial (Linearization.differenceSupport S) P.normalizedCoefficient =
      P.regularEval := by
  unfold regularEval
  rw [RegularFactorization.polynomial_eq, RegularFactorization.polynomial_eq]
  symm
  calc
    (∑ w ∈ P.support, RegularFactorization.term (P.coefficient w) w) =
        ∑ w ∈ P.support, RegularFactorization.term (P.normalizedCoefficient w) w := by
      apply Finset.sum_congr rfl
      intro w hw
      simp [normalizedCoefficient, hw]
    _ = _ := Finset.sum_subset hcover (by
      intro w hw hnot
      simp [normalizedCoefficient, hnot])

/-- A genuine step of Gram factorization, including the enlarged coefficient space. -/
def step (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S) : Polynomial G where
  Index := Support S × (P.Index ⊕ P.Index)
  fintype := inferInstance
  decEq := inferInstance
  nonempty := ⟨⟨⟨1,hS⟩, Sum.inl (Classical.choice P.nonempty)⟩⟩
  support := S
  coefficient := RegularFactorization.paddedCoefficients S hS
    (dilationCoefficient P.normalizedCoefficient)

@[simp] theorem step_dimension (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S) :
    Fintype.card (P.step S hS).Index = 2 * S.card * Fintype.card P.Index := by
  simp [step, Nat.mul_add]
  ring

def correction (P : Polynomial G) (S : Finset G) : ℝ :=
  theta S (dilationCoefficient P.normalizedCoefficient)

@[simp] theorem step_finiteEval (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S)
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    (π : G →* unitary (Matrix ν ν ℂ)) :
    (P.step S hS).finiteEval π =
      paddedPolynomial S hS (dilationCoefficient P.normalizedCoefficient) π := by
  unfold finiteEval step paddedPolynomial
  rw [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro g hg
  simp [RegularFactorization.paddedCoefficients, g.property]

@[simp] theorem step_regularEval (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S) :
    (P.step S hS).regularEval =
      RegularFactorization.padded S hS (dilationCoefficient P.normalizedCoefficient) :=
  (RegularFactorization.padded_eq_regularPolynomial S hS _).symm

theorem step_regular_norm_sq (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S)
    (hcover : P.support ⊆ Linearization.differenceSupport S) :
    ‖(P.step S hS).regularEval‖ ^ 2 = ‖P.regularEval‖ + P.correction S := by
  rw [step_regularEval, RegularFactorization.padded_dilation_norm_sq,
    regularEval_enlarge P S hcover]
  rfl

theorem step_finite_norm_sq (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S)
    (hcover : P.support ⊆ Linearization.differenceSupport S)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G →* unitary (Matrix ν ν ℂ)) :
    ‖(P.step S hS).finiteEval π‖ ^ 2 = ‖P.finiteEval π‖ + P.correction S := by
  rw [step_finiteEval, paddedPolynomial_dilation_norm_sq,
    finiteEval_enlarge P π S hcover]
  rfl

theorem correction_nonneg (P : Polynomial G) (S : Finset G) : 0 ≤ P.correction S :=
  theta_nonneg S _

theorem correction_le (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S)
    (hcover : P.support ⊆ Linearization.differenceSupport S) :
    P.correction S ≤ (S.card : ℝ) * ‖P.regularEval‖ := by
  simpa [regularEval_enlarge P S hcover] using
    theta_dilation_le_card_mul_regularNorm S hS P.normalizedCoefficient

theorem step_error_transfer (P : Polynomial G) (S : Finset G) (hS : (1:G) ∈ S)
    (hcover : P.support ⊆ Linearization.differenceSupport S)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G →* unitary (Matrix ν ν ℂ)) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hQ : ‖(P.step S hS).finiteEval π‖ ≤ (1+ε) * ‖(P.step S hS).regularEval‖) :
    ‖P.finiteEval π‖ ≤ (1+6*(S.card:ℝ)*ε) * ‖P.regularEval‖ := by
  have h := RegularFactorization.finite_regular_error_transfer S hS
    P.normalizedCoefficient π ε hε hε1 (by simpa using hQ)
  simpa [P.finiteEval_enlarge π S hcover, P.regularEval_enlarge S hcover] using h

section FreeGroup
variable {α : Type} [DecidableEq α]

def halve (P : Polynomial (FreeGroup α)) (r : ℕ) : Polynomial (FreeGroup α) :=
  P.step (splitSupport P.support r) (one_mem_splitSupport _ _)

theorem halve_degree (P : Polynomial (FreeGroup α)) (r : ℕ)
    (hP : ∀ w ∈ P.support, FreeGroup.norm w ≤ 2*r) :
    ∀ w ∈ (P.halve r).support, FreeGroup.norm w ≤ r :=
  splitSupport_degree P.support r hP

/-- Repeat the actual square-root factorization, ending with words of length one. -/
def reduce (P : Polynomial (FreeGroup α)) : ℕ → Polynomial (FreeGroup α)
  | 0 => P
  | n+1 => (P.halve (2^n)).reduce n

/-- Exact enlargement multiplier of the recursively constructed coefficient space. -/
def dimensionCost (P : Polynomial (FreeGroup α)) : ℕ → ℕ
  | 0 => 1
  | n+1 => 2 * (splitSupport P.support (2^n)).card * (P.halve (2^n)).dimensionCost n

/-- Actual product of the backward-error factors `6 |S|`. -/
def errorCost (P : Polynomial (FreeGroup α)) : ℕ → ℕ
  | 0 => 1
  | n+1 => 6 * (splitSupport P.support (2^n)).card * (P.halve (2^n)).errorCost n

theorem dimensionCost_pos (P : Polynomial (FreeGroup α)) (n : ℕ) :
    0 < P.dimensionCost n := by
  induction n generalizing P with
  | zero => simp [dimensionCost]
  | succ n ih =>
    have hB := Finset.card_pos.mpr (show (splitSupport P.support (2^n)).Nonempty from
      ⟨1, one_mem_splitSupport _ _⟩)
    exact Nat.mul_pos (Nat.mul_pos (by omega) hB) (ih _)

theorem errorCost_eq (P : Polynomial (FreeGroup α)) (n : ℕ) :
    P.errorCost n = 3^n * P.dimensionCost n := by
  induction n generalizing P with
  | zero => simp [errorCost, dimensionCost]
  | succ n ih => simp only [errorCost, dimensionCost, ih, pow_succ]; ring

theorem errorCost_pos (P : Polynomial (FreeGroup α)) (n : ℕ) : 0 < P.errorCost n := by
  rw [errorCost_eq]
  exact Nat.mul_pos (by positivity) (dimensionCost_pos P n)

theorem reduce_dimension (P : Polynomial (FreeGroup α)) (n : ℕ) :
    Fintype.card (P.reduce n).Index = Fintype.card P.Index * P.dimensionCost n := by
  induction n generalizing P with
  | zero => simp [reduce, dimensionCost]
  | succ n ih =>
    rw [reduce, ih]
    change Fintype.card (P.step _ _).Index * _ = _
    rw [step_dimension]
    simp only [dimensionCost]
    ring

theorem reduce_degree (P : Polynomial (FreeGroup α)) (n : ℕ)
    (hP : ∀ w ∈ P.support, FreeGroup.norm w ≤ 2^n) :
    ∀ w ∈ (P.reduce n).support, FreeGroup.norm w ≤ 1 := by
  induction n generalizing P with
  | zero => simpa only [reduce, pow_zero] using hP
  | succ n ih =>
    apply ih (P.halve (2^n))
    apply halve_degree
    simpa only [pow_succ, Nat.mul_comm] using hP

/-- Every error-transfer hypothesis is discharged by the constructed factors.
Only the comparison for the final linear polynomial is supplied. -/
theorem reduce_error_transfer (P : Polynomial (FreeGroup α)) (n : ℕ)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : FreeGroup α →* unitary (Matrix ν ν ℂ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : ‖(P.reduce n).finiteEval π‖ ≤
      (1+ε/(P.errorCost n:ℝ))*‖(P.reduce n).regularEval‖) :
    ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  induction n generalizing P ε with
  | zero => simpa only [reduce, errorCost, Nat.cast_one, div_one] using hfinal
  | succ n ih =>
    let B := (splitSupport P.support (2^n)).card
    have hB : 1 ≤ B := Finset.one_le_card.mpr ⟨1, one_mem_splitSupport _ _⟩
    have hBreal : (1:ℝ) ≤ B := by exact_mod_cast hB
    have h6B : (0:ℝ) < 6*(B:ℝ) := by positivity
    have hδ0 : 0 ≤ ε/(6*(B:ℝ)) := div_nonneg hε h6B.le
    have hδ1 : ε/(6*(B:ℝ)) ≤ 1 := by
      apply (div_le_iff₀ h6B).mpr
      nlinarith
    have hnorm := ih (P.halve (2^n)) (ε/(6*(B:ℝ))) hδ0 hδ1 (by
      simpa only [reduce, errorCost, Nat.cast_mul, Nat.cast_ofNat, div_div,
        mul_assoc, B] using hfinal)
    have hstep := P.step_error_transfer (splitSupport P.support (2^n))
      (one_mem_splitSupport _ _) (subset_difference_splitSupport _ _) π
      (ε/(6*(B:ℝ))) hδ0 hδ1 hnorm
    have heq : 6*(B:ℝ)*(ε/(6*(B:ℝ))) = ε := mul_div_cancel₀ ε h6B.ne'
    change ‖P.finiteEval π‖ ≤ (1 + 6*(B:ℝ)*(ε/(6*(B:ℝ)))) * ‖P.regularEval‖ at hstep
    simpa only [heq] using hstep

/-- Complete deterministic reduction of a degree `2^n` polynomial to a linear one.
The output coefficients, exact dimension cost, and comparison transfer are
constructed, without any assumed family of intermediate polynomials. -/
theorem constructed_linear_reduction (P : Polynomial (FreeGroup α)) (n : ℕ)
    (hP : ∀ w ∈ P.support, FreeGroup.norm w ≤ 2^n) :
    ∃ Q : Polynomial (FreeGroup α),
      (∀ w ∈ Q.support, FreeGroup.norm w ≤ 1) ∧
      Fintype.card Q.Index = Fintype.card P.Index * P.dimensionCost n ∧
      P.errorCost n = 3^n * P.dimensionCost n ∧
      ∀ {ν : Type} [Fintype ν] [DecidableEq ν] [Nonempty ν]
        (π : FreeGroup α →* unitary (Matrix ν ν ℂ)) (ε : ℝ),
        0 ≤ ε → ε ≤ 1 →
        ‖Q.finiteEval π‖ ≤ (1+ε/(P.errorCost n:ℝ))*‖Q.regularEval‖ →
        ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  refine ⟨P.reduce n, reduce_degree P n hP, reduce_dimension P n,
    errorCost_eq P n, ?_⟩
  intro ν _ _ _ π ε hε hε1 hfinal
  exact reduce_error_transfer P n π ε hε hε1 hfinal

end FreeGroup

end Polynomial
end Nonadditivity.PolynomialReduction
