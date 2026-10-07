/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.RegularFubini

/-! # The product Collins--Youn inequality

The coefficient induction keeps the diagonal and off-diagonal energies separate.
The trace-zero recurrence removes exactly the all-diagonal contribution.
-/

noncomputable section

namespace Nonadditivity.CollinsYounProduct

open FreeModel CollinsYoun
open scoped BigOperators

set_option maxHeartbeats 800000

def branchSuccEquiv (K n : ℕ) : Branch K (n+1) ≃ Fin K × Branch K n where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by ext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv p := by ext <;> rfl

def coefficientEnergy {α : Type*} [Fintype α] (A : Matrix α α ℂ) : ℝ :=
  ∑ a, ∑ b, ‖A a b‖ ^ 2

theorem coefficientEnergy_nonneg {α : Type*} [Fintype α] (A : Matrix α α ℂ) :
    0 ≤ coefficientEnergy A := by unfold coefficientEnergy; positivity

theorem coefficientEnergy_eq_hs_sq {α : Type*} [Fintype α] (A : Matrix α α ℂ) :
    coefficientEnergy A = AdjointPurity.hsLength A ^ 2 := by
  rw [← coefficientLength_eq_hsLength, coefficientLength_sq]
  rfl

def slice {K n : ℕ} (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ)
    (i j : Fin K) : Matrix (Branch K n) (Branch K n) ℂ :=
  fun a b => A (Fin.cons i a) (Fin.cons j b)

def diagonalSum {K n : ℕ} (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    Matrix (Branch K n) (Branch K n) ℂ := ∑ i, slice A i i

def diagonalEnergy {K n : ℕ} (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) : ℝ :=
  ∑ i, coefficientEnergy (slice A i i)

def offDiagonalEnergy {K n : ℕ} (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else coefficientEnergy (slice A i j)

theorem diagonalEnergy_nonneg {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    0 ≤ diagonalEnergy A := Finset.sum_nonneg (fun _ _ => coefficientEnergy_nonneg _)

theorem offDiagonalEnergy_nonneg {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    0 ≤ offDiagonalEnergy A := by
  unfold offDiagonalEnergy
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> first | exact le_rfl | exact coefficientEnergy_nonneg _

theorem sum_branch_succ {K n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Branch K (n+1) → M) :
    (∑ a, f a) = ∑ i, ∑ a, f (Fin.cons i a) := by
  rw [← (branchSuccEquiv K n).symm.sum_comp]
  exact Fintype.sum_prod_type _

theorem coefficientEnergy_slices {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    coefficientEnergy A = ∑ i, ∑ j, coefficientEnergy (slice A i j) := by
  unfold coefficientEnergy
  rw [sum_branch_succ]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sum_branch_succ]
  rw [Finset.sum_comm]
  rfl

theorem energy_split {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    coefficientEnergy A = diagonalEnergy A + offDiagonalEnergy A := by
  rw [coefficientEnergy_slices]
  unfold diagonalEnergy offDiagonalEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∑ j, if i = j then coefficientEnergy (slice A i j) else 0) =
      coefficientEnergy (slice A i i) := by simp
  rw [← he, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem diagonalSum_trace {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    (diagonalSum A).trace = A.trace := by
  unfold diagonalSum Matrix.trace Matrix.diag
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm, sum_branch_succ]
  rfl

theorem diagonalSum_energy_le {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    coefficientEnergy (diagonalSum A) ≤ (K : ℝ) * diagonalEnergy A := by
  have hpoint : ∀ a b : Branch K n,
      ‖∑ i, slice A i i a b‖ ^ 2 ≤ (K : ℝ) * ∑ i, ‖slice A i i a b‖ ^ 2 := by
    intro a b
    simpa using norm_sum_smul_sq_le (fun _ : Fin K => (1 : ℂ))
      (fun i => slice A i i a b)
  unfold coefficientEnergy diagonalSum diagonalEnergy
  simp only [Matrix.sum_apply]
  calc
    (∑ a, ∑ b, ‖∑ i, slice A i i a b‖ ^ 2) ≤
        ∑ a, ∑ b, (K : ℝ) * ∑ i, ‖slice A i i a b‖ ^ 2 := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      exact hpoint a b
    _ = (K : ℝ) * ∑ i, ∑ a, ∑ b, ‖slice A i i a b‖ ^ 2 := by
      simp_rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ a, ∑ b, ∑ i, ‖slice A i i a b‖ ^ 2) =
            ∑ a, ∑ i, ∑ b, ‖slice A i i a b‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

/-- Two orthogonal coefficient sectors combine by the exact scalar
Cauchy--Schwarz constant, without introducing another triangle loss. -/
theorem two_sector_estimate {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a * Real.sqrt x + Real.sqrt b * Real.sqrt y) ^ 2 ≤
      (a+b) * (x+y) := by
  have hax := Real.sq_sqrt ha
  have hby := Real.sq_sqrt hb
  have hxx := Real.sq_sqrt hx
  have hyy := Real.sq_sqrt hy
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt y - Real.sqrt b * Real.sqrt x)]

def polynomial {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) :
    Hilbert (ProductFreeGroup K n) →L[ℂ] Hilbert (ProductFreeGroup K n) :=
  ∑ a, ∑ b, A a b • leftRegular ((branchWord a)⁻¹ * branchWord b)

theorem polynomial_sum {K n : ℕ} {I : Type*} [Fintype I]
    (A : I → Matrix (Branch K n) (Branch K n) ℂ) :
    polynomial (∑ i, A i) = ∑ i, polynomial (A i) := by
  unfold polynomial
  simp only [Matrix.sum_apply, Finset.sum_smul]
  calc
    (∑ a, ∑ b, ∑ i, A i a b • leftRegular ((branchWord a)⁻¹ * branchWord b)) =
        ∑ a, ∑ i, ∑ b, A i a b • leftRegular ((branchWord a)⁻¹ * branchWord b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

@[simp] theorem polynomial_zero {K n : ℕ} :
    polynomial (0 : Matrix (Branch K n) (Branch K n) ℂ) = 0 := by
  simp [polynomial]

def groupSuccEquiv (K n : ℕ) : ProductFreeGroup K (n+1) ≃*
    FreeGroup (Fin K) × ProductFreeGroup K n where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by ext j; exact Fin.cases rfl (fun _ => rfl) j
  right_inv p := by ext <;> rfl
  map_mul' a b := rfl

theorem offDiagonal_norm_energy_le {K n : ℕ} {C : ℝ}
    (hbound : ∀ B : Matrix (Branch K n) (Branch K n) ℂ,
      ‖polynomial B‖ ^ 2 ≤ C * coefficientEnergy B)
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    (∑ i, ∑ j, if i = j then 0 else ‖polynomial (slice A i j)‖ ^ 2) ≤
      C * offDiagonalEnergy A := by
  unfold offDiagonalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> first | simp | exact hbound _

/-- The exact recurrence used for both the unrestricted and the traceless
estimate. The hypotheses are numerical inequalities supplied by the operator
decomposition and the preceding induction stage. -/
theorem norm_step_sq {x d z D O C E : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d)
    (hz : 0 ≤ z) (hD : 0 ≤ D) (hO : 0 ≤ O) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hstep : x ≤ d + 3 * Real.sqrt z) (hdiag : d^2 ≤ D*C)
    (hoff : z ≤ O*E) :
    x^2 ≤ (D+9*O)*(C+E) := by
  have hd' : d ≤ Real.sqrt D * Real.sqrt C := by
    apply (sq_le_sq₀ hd (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hD, Real.sq_sqrt hC]
    exact hdiag
  have ho' : Real.sqrt z ≤ Real.sqrt O * Real.sqrt E := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [Real.sq_sqrt hz, mul_pow, Real.sq_sqrt hO, Real.sq_sqrt hE]
    exact hoff
  have htop : x ≤ Real.sqrt D * Real.sqrt C + 3 * Real.sqrt O * Real.sqrt E := by
    nlinarith
  have hcs : (Real.sqrt D * Real.sqrt C + 3 * Real.sqrt O * Real.sqrt E)^2 ≤
      (D+9*O)*(C+E) := by
    have hdd := Real.sq_sqrt hD
    have hoo := Real.sq_sqrt hO
    have hcc := Real.sq_sqrt hC
    have hee := Real.sq_sqrt hE
    nlinarith [sq_nonneg (Real.sqrt D * Real.sqrt E - 3 * Real.sqrt O * Real.sqrt C)]
  exact (sq_le_sq₀ hx (by positivity) |>.mpr htop).trans hcs

theorem polynomial_zero_factors {K : ℕ}
    (A : Matrix (Branch K 0) (Branch K 0) ℂ) :
    polynomial A = A default default •
      ContinuousLinearMap.id ℂ (Hilbert (ProductFreeGroup K 0)) := by
  simp [polynomial]

theorem zero_factor_bound {K : ℕ}
    (A : Matrix (Branch K 0) (Branch K 0) ℂ) :
    ‖polynomial A‖ ^ 2 ≤ coefficientEnergy A := by
  rw [polynomial_zero_factors]
  simp only [coefficientEnergy, Fintype.sum_unique, norm_smul]
  have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert (ProductFreeGroup K 0))
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
  nlinarith [norm_nonneg (A default default)]

theorem zero_factor_traceless {K : ℕ}
    (A : Matrix (Branch K 0) (Branch K 0) ℂ) (htrace : A.trace = 0) :
    polynomial A = 0 := by
  have he : A default default = 0 := by simpa [Matrix.trace, Matrix.diag] using htrace
  simp [polynomial_zero_factors, he]

def offPolynomialEnergy {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else ‖polynomial (slice A i j)‖ ^ 2

theorem offPolynomialEnergy_nonneg {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    0 ≤ offPolynomialEnergy A := by
  unfold offPolynomialEnergy
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  split_ifs <;> positivity

theorem difference_nonneg (K n : ℕ) :
    0 ≤ ((K : ℝ)+9)^n - (K : ℝ)^n := by
  apply sub_nonneg.mpr
  exact pow_le_pow_left₀ (by positivity) (by linarith) n

/-- Algebraic induction from the concrete one-coordinate operator splitting.
Both estimates are proved simultaneously, so the trace-zero constant retains
the exact subtraction of the all-diagonal coefficient sector. -/
theorem bounds_of_step (K : ℕ)
    (hstep : ∀ n (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ),
      ‖polynomial A‖ ≤ ‖polynomial (diagonalSum A)‖ + 3 * Real.sqrt (offPolynomialEnergy A)) :
    ∀ n,
      (∀ A : Matrix (Branch K n) (Branch K n) ℂ,
        ‖polynomial A‖ ^ 2 ≤ ((K : ℝ)+9)^n * coefficientEnergy A) ∧
      (∀ A : Matrix (Branch K n) (Branch K n) ℂ, A.trace = 0 →
        ‖polynomial A‖ ^ 2 ≤ (((K : ℝ)+9)^n - (K : ℝ)^n) * coefficientEnergy A) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro A; simpa using zero_factor_bound A
    · intro A ht; simp [zero_factor_traceless A ht]
  | succ n ih =>
    have hoff (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
        offPolynomialEnergy A ≤ ((K : ℝ)+9)^n * offDiagonalEnergy A :=
      offDiagonal_norm_energy_le ih.1 A
    constructor
    · intro A
      have hd : ‖polynomial (diagonalSum A)‖ ^ 2 ≤
          ((K : ℝ) * ((K : ℝ)+9)^n) * diagonalEnergy A := by
        calc
          _ ≤ ((K : ℝ)+9)^n * coefficientEnergy (diagonalSum A) := ih.1 _
          _ ≤ ((K : ℝ)+9)^n * ((K : ℝ) * diagonalEnergy A) :=
            mul_le_mul_of_nonneg_left (diagonalSum_energy_le A) (by positivity)
          _ = _ := by ring
      have hh := norm_step_sq (norm_nonneg (polynomial A))
        (norm_nonneg (polynomial (diagonalSum A))) (offPolynomialEnergy_nonneg A)
        (by positivity : 0 ≤ (K : ℝ) * ((K : ℝ)+9)^n)
        (by positivity : 0 ≤ ((K : ℝ)+9)^n)
        (diagonalEnergy_nonneg A) (offDiagonalEnergy_nonneg A) (hstep n A) hd (hoff A)
      rw [← energy_split] at hh
      convert hh using 1; ring
    · intro A ht
      have hdt : (diagonalSum A).trace = 0 := (diagonalSum_trace A).trans ht
      have hd : ‖polynomial (diagonalSum A)‖ ^ 2 ≤
          ((K : ℝ) * (((K : ℝ)+9)^n - (K : ℝ)^n)) * diagonalEnergy A := by
        calc
          _ ≤ (((K : ℝ)+9)^n - (K : ℝ)^n) * coefficientEnergy (diagonalSum A) :=
            ih.2 _ hdt
          _ ≤ (((K : ℝ)+9)^n - (K : ℝ)^n) * ((K : ℝ) * diagonalEnergy A) :=
            mul_le_mul_of_nonneg_left (diagonalSum_energy_le A) (difference_nonneg K n)
          _ = _ := by ring
      have hh := norm_step_sq (norm_nonneg (polynomial A))
        (norm_nonneg (polynomial (diagonalSum A))) (offPolynomialEnergy_nonneg A)
        (mul_nonneg (by positivity) (difference_nonneg K n))
        (by positivity : 0 ≤ ((K : ℝ)+9)^n)
        (diagonalEnergy_nonneg A) (offDiagonalEnergy_nonneg A) (hstep n A) hd (hoff A)
      rw [← energy_split] at hh
      convert hh using 1; ring

theorem freeNorm_eq_normalized {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) :
    freeNorm A = ‖polynomial A‖ / (K : ℝ)^n := by
  unfold freeNorm gamma polynomial
  simp only [norm_smul, norm_div, norm_one, norm_pow, Complex.norm_natCast]
  ring

theorem constant_normalization {K n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) :
    c K n ^ 2 * ((K : ℝ)^n)^2 = ((K : ℝ)+9)^n - (K : ℝ)^n := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hp : (K : ℝ)^n ≠ 0 := pow_ne_zero _ hk
  rw [c_sq hK hn]
  have he : 1 + 9 / (K : ℝ) = ((K : ℝ)+9)/(K : ℝ) := by
    field_simp
  rw [he, div_pow]
  field_simp

/-- The precise normalization used by the channel construction follows
algebraically from the unnormalized square-norm estimate. -/
theorem collinsYounBound_of_squared {K n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (hb : ∀ A : Matrix (Branch K n) (Branch K n) ℂ, A.trace = 0 →
      ‖polynomial A‖ ^ 2 ≤ (((K : ℝ)+9)^n - (K : ℝ)^n) * coefficientEnergy A) :
    CollinsYounBound K n := by
  intro A ht
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hp : 0 < (K : ℝ)^n := pow_pos hk n
  have hh := hb A ht
  rw [coefficientEnergy_eq_hs_sq] at hh
  apply (sq_le_sq₀ (freeNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [freeNorm_eq_normalized, div_pow]
  apply (div_le_iff₀ (by positivity : 0 < ((K : ℝ)^n)^2)).mpr
  calc
    _ ≤ (((K : ℝ)+9)^n - (K : ℝ)^n) * AdjointPurity.hsLength A ^ 2 := hh
    _ = _ := by
      change (((K : ℝ)+9)^n - (K : ℝ)^n) * AdjointPurity.hsLength A ^ 2 =
        (c K n * AdjointPurity.hsLength A)^2 * ((K : ℝ)^n)^2
      rw [← constant_normalization hK hn]
      ring

/-- The actual product regular polynomial obeys the one-coordinate splitting:
the diagonal coefficient is its partial trace, and the remaining operator
coefficients satisfy the proved amplified three-component Haagerup estimate. -/
theorem polynomial_step_bound {K n : ℕ}
    (A : Matrix (Branch K (n+1)) (Branch K (n+1)) ℂ) :
    ‖polynomial A‖ ≤ ‖polynomial (diagonalSum A)‖ +
      3 * Real.sqrt (offPolynomialEnergy A) := by
  change ‖∑ a, ∑ b, A a b • leftRegular ((branchWord a)⁻¹ * branchWord b)‖ ≤
    ‖polynomial (diagonalSum A)‖ + 3 * Real.sqrt (offPolynomialEnergy A)
  rw [RegularFubini.polynomial_succ_norm_eq]
  rw [diagonalSum, polynomial_sum]
  have hb := RegularFubini.coefficientPolynomial_norm_le_diagonal_offDiagonal
    (fun i j : Fin K => polynomial (slice A i j))
  simpa only [offPolynomialEnergy, polynomial, slice] using hb

/-- The unrestricted product Haagerup estimate, proved for the actual regular
representation on the product free group. -/
theorem polynomial_norm_sq_le {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) :
    ‖polynomial A‖ ^ 2 ≤ ((K : ℝ)+9)^n * coefficientEnergy A :=
  (bounds_of_step K (fun _ => polynomial_step_bound) n).1 A

/-- The all-diagonal sector is absent when the original coefficient matrix is
traceless; its exact energy K^n is subtracted from the product constant. -/
theorem traceless_polynomial_norm_sq_le {K n : ℕ}
    (A : Matrix (Branch K n) (Branch K n) ℂ) (htrace : A.trace = 0) :
    ‖polynomial A‖ ^ 2 ≤ (((K : ℝ)+9)^n - (K : ℝ)^n) * coefficientEnergy A :=
  (bounds_of_step K (fun _ => polynomial_step_bound) n).2 A htrace

/-- The full Collins--Youn estimate, with no analytic hypothesis. Only the
manuscript's numerical parameter conditions remain. -/
theorem collinsYounBound {K n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) :
    CollinsYounBound K n :=
  collinsYounBound_of_squared hK hn traceless_polynomial_norm_sq_le

end Nonadditivity.CollinsYounProduct
