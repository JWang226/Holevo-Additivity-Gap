/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingRenewal

/-! # Exact last-return segmentation of finite matrix-word powers -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarNonbacktracking

open scoped BigOperators
open HaarWordExpansion

variable {G R : Type*} [Group G] [DecidableEq G] [Ring R]

/-- Evaluation at a group word is additive for arbitrary coefficient rings. -/
def coefficientAddHom (g : G) : MonoidAlgebra R G →+ R where
  toFun f := f g
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq G] in
@[simp] theorem coefficientAddHom_apply (g : G) (f : MonoidAlgebra R G) :
    coefficientAddHom g f = f g := rfl

def removeConstant (f : MonoidAlgebra R G) : MonoidAlgebra R G :=
  f - MonoidAlgebra.single 1 (f 1)

omit [DecidableEq G] in
theorem removeConstant_add (f h : MonoidAlgebra R G) :
    removeConstant (f + h) = removeConstant f + removeConstant h := by
  change f + h - MonoidAlgebra.single 1 (f 1 + h 1) = _
  rw [MonoidAlgebra.single_add, removeConstant, removeConstant]
  abel

omit [DecidableEq G] in
theorem removeConstant_sum {I : Type*} (s : Finset I) (f : I → MonoidAlgebra R G) :
    removeConstant (∑ i ∈ s, f i) = ∑ i ∈ s, removeConstant (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [removeConstant]
  | insert i s hi ih => simp [hi, removeConstant_add, ih]

omit [DecidableEq G] in
/-- Removing the constant is right-linear over the coefficient matrix algebra. -/
theorem removeConstant_mul_constant (f : MonoidAlgebra R G) (B : R) :
    removeConstant (f * MonoidAlgebra.single 1 B) =
      removeConstant f * MonoidAlgebra.single 1 B := by
  rw [removeConstant, MonoidAlgebra.mul_single_one_apply, removeConstant, sub_mul,
    MonoidAlgebra.single_mul_single, one_mul]

omit [DecidableEq G] in
theorem removeConstant_add_constant (f : MonoidAlgebra R G) :
    removeConstant f + MonoidAlgebra.single 1 (f 1) = f := by
  simp only [removeConstant, sub_add_cancel]

omit [DecidableEq G] in
theorem removeConstant_mul_killed (A : MonoidAlgebra R G) (n : ℕ) :
    removeConstant (A * killedPolynomial A 1 n) = killedPolynomial A 1 (n + 1) := rfl

/-- Decompose an ordinary word power at its last visit to the identity.
The terminal piece has no return, while the prefix is unrestricted. -/
theorem last_return_polynomial_decomposition (A : MonoidAlgebra R G) (n : ℕ) :
    A ^ n = ∑ k ∈ Finset.range (n + 1),
      killedPolynomial A 1 k * MonoidAlgebra.single 1 ((A ^ (n - k)) 1) := by
  induction n with
  | zero => simp [killedPolynomial, MonoidAlgebra.one_def]
  | succ n ih =>
      have hkill : removeConstant (A ^ (n + 1)) =
          ∑ k ∈ Finset.range (n + 1), killedPolynomial A 1 (k + 1) *
            MonoidAlgebra.single 1 ((A ^ (n - k)) 1) := by
        rw [pow_succ', ih, Finset.mul_sum, removeConstant_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [← mul_assoc, removeConstant_mul_constant, removeConstant_mul_killed]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero,
        show killedPolynomial A 1 0 = 1 from rfl, one_mul]
      rw [← hkill]
      exact (removeConstant_add_constant _).symm

/-- The literal matrix-coefficient last-return formula at every nonidentity word. -/
theorem last_return_coefficient (A : MonoidAlgebra R G) (n : ℕ) (g : G) (hg : g ≠ 1) :
    (A ^ n) g = ∑ k ∈ Finset.range n,
      killedPolynomial A 1 (k + 1) g * (A ^ (n - 1 - k)) 1 := by
  have h := congrArg (fun f : MonoidAlgebra R G => f g)
    (last_return_polynomial_decomposition A n)
  rw [Finset.sum_range_succ'] at h
  simp only [killedPolynomial, one_mul, MonoidAlgebra.coe_add, Pi.add_apply] at h
  change (A ^ n) g = coefficientAddHom g
    (∑ k ∈ Finset.range n, killedPolynomial A 1 (k + 1) *
      MonoidAlgebra.single 1 ((A ^ (n - (k + 1))) 1)) +
    (MonoidAlgebra.single 1 ((A ^ (n - 0)) 1)) g at h
  rw [map_sum] at h
  simp only [coefficientAddHom_apply] at h
  simp only [MonoidAlgebra.mul_single_one_apply, MonoidAlgebra.single_apply,
    if_neg (Ne.symm hg), add_zero] at h
  have he (k : ℕ) : n - 1 - k = n - (k + 1) := by omega
  simpa only [he] using h

/-- Last-visit decomposition starting from an arbitrary finite word polynomial.
The first summand consists exactly of paths that avoid the cut vertex. -/
theorem last_visit_polynomial_decomposition (A T : MonoidAlgebra R G) (n : ℕ) :
    A ^ n * T = killedPolynomial A T n + ∑ k ∈ Finset.range n,
      killedPolynomial A 1 k * MonoidAlgebra.single 1 ((A ^ (n - k) * T) 1) := by
  induction n with
  | zero => simp [killedPolynomial]
  | succ n ih =>
      have hkill : removeConstant (A ^ (n + 1) * T) = killedPolynomial A T (n + 1) +
          ∑ k ∈ Finset.range n, killedPolynomial A 1 (k + 1) *
            MonoidAlgebra.single 1 ((A ^ (n - k) * T) 1) := by
        rw [pow_succ', mul_assoc, ih, mul_add, Finset.mul_sum,
          removeConstant_add, removeConstant_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [← mul_assoc, removeConstant_mul_constant, removeConstant_mul_killed]
      have htotal := removeConstant_add_constant (A ^ (n + 1) * T)
      rw [hkill] at htotal
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero,
        show killedPolynomial A 1 0 = 1 from rfl, one_mul]
      exact htotal.symm.trans (add_assoc _ _ _)

/-- A matrix-coefficient factorization across any vertex that separates the
start from the endpoint; the explicit killed remainder records the separation. -/
theorem coefficient_factorization_at_cut (A : MonoidAlgebra R G) (n : ℕ)
    (g h : G) (havoid : killedPolynomial A (MonoidAlgebra.single h⁻¹ 1) n g = 0) :
    (A ^ n) (g * h) = ∑ k ∈ Finset.range n,
      killedPolynomial A 1 k g * (A ^ (n - k)) h := by
  have hformula := congrArg (fun f : MonoidAlgebra R G => f g)
    (last_visit_polynomial_decomposition A (MonoidAlgebra.single h⁻¹ 1) n)
  change (A ^ n * MonoidAlgebra.single h⁻¹ 1 : MonoidAlgebra R G) g =
    killedPolynomial A (MonoidAlgebra.single h⁻¹ 1) n g +
      coefficientAddHom g (∑ k ∈ Finset.range n, killedPolynomial A 1 k *
        MonoidAlgebra.single 1 ((A ^ (n - k) * MonoidAlgebra.single h⁻¹ 1 : MonoidAlgebra R G) 1)) at hformula
  rw [map_sum, havoid, zero_add] at hformula
  simp only [coefficientAddHom_apply] at hformula
  simpa only [MonoidAlgebra.mul_single_apply, inv_inv, inv_one, one_mul, mul_one] using hformula

end Nonadditivity.HaarNonbacktracking
