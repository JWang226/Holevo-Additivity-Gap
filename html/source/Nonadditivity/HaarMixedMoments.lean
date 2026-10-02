/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarColumnMoments
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Exact phase selection for arbitrary Haar entry moments -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarMixedMoments
open MeasureTheory HaarModel HaarMoments HaarFourthMoments HaarColumnMoments
open scoped Matrix Matrix.Norms.L2Operator
variable {N : ℕ}

/-- An unequal pair of phase weights forces the actual Haar integral to vanish. -/
theorem integral_eq_zero_of_row_phase (f : LocalUnitary N → ℂ)
    (i : Fin (N+1)) (p q : ℕ) (hpq : p ≠ q)
    (hf : ∀ z : ℂ, ∀ hz : star z*z=1, ∀ U : LocalUnitary N,
      f (rowPhase i z hz * U) = (z^p * (star z)^q) * f U) :
    (∫ U, f U ∂haar N) = 0 := by
  let m := p+q+1
  have hm : m ≠ 0 := by dsimp [m]; omega
  let z := Complex.exp (2 * Real.pi * Complex.I / m)
  have hzprim : IsPrimitiveRoot z m := Complex.isPrimitiveRoot_exp m hm
  have hznorm : ‖z‖ = 1 := hzprim.norm'_eq_one hm
  have hz : star z*z=1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hznorm]
    norm_num
  have hne : z^p ≠ z^q := fun h => hpq (hzprim.pow_inj (by dsimp [m]; omega)
    (by dsimp [m]; omega) h)
  have h := integral_mul_left_eq_self (μ := haar N) f (rowPhase i z hz)
  simp_rw [hf, integral_const_mul] at h
  have hzq : (star z)^q * z^q = 1 := by rw [← mul_pow, hz, one_pow]
  have he : z^p * (∫ U, f U ∂haar N) = z^q * (∫ U, f U ∂haar N) := by
    calc
      _ = z^p * (((star z)^q * z^q) * (∫ U, f U ∂haar N)) := by rw [hzq, one_mul]
      _ = z^q * ((z^p * (star z)^q) * (∫ U, f U ∂haar N)) := by ring
      _ = _ := by rw [h]
  exact (mul_eq_mul_right_iff.mp he).resolve_left hne

/-- All unbalanced complex moments of a Haar entry are exactly zero. -/
theorem integral_entry_pow_mul_star_pow_of_ne (i j : Fin (N+1)) (p q : ℕ)
    (hpq : p ≠ q) :
    (∫ U : LocalUnitary N, ((U:Mat N) i j)^p * (star ((U:Mat N) i j))^q ∂haar N) = 0 := by
  apply integral_eq_zero_of_row_phase _ i p q hpq
  intro z hz U
  simp only [rowPhase_mul_entry, if_true, mul_pow, star_mul]
  ring

/-- The complete complex moment formula for one Haar entry, at every pair of orders. -/
theorem integral_entry_pow_mul_star_pow (i j : Fin (N+1)) (p q : ℕ) :
    (∫ U : LocalUnitary N, ((U:Mat N) i j)^p * (star ((U:Mat N) i j))^q ∂haar N) =
      if p=q then (p.factorial:ℂ) / ((N+1).ascFactorial p:ℂ) else 0 := by
  by_cases hpq : p=q
  · subst q
    rw [if_pos rfl]
    simp_rw [← norm_even_complex]
    rw [integral_complex_ofReal, integral_entry_norm_even]
    push_cast
    rfl
  · rw [if_neg hpq]
    exact integral_entry_pow_mul_star_pow_of_ne i j p q hpq

/-- Number of occurrences of one row in an arbitrary list of entries. -/
def multiplicity {p : ℕ} (i : Fin p → Fin (N+1)) (r : Fin (N+1)) : ℕ :=
  (Finset.univ.filter (fun a => i a=r)).card

lemma prod_row_phase {p : ℕ} (i : Fin p → Fin (N+1)) (r : Fin (N+1)) (z : ℂ) :
    (∏ a, if i a=r then z else 1) = z^(multiplicity i r) := by
  simp [multiplicity, Finset.prod_ite]

/-- A completely general entry monomial with arbitrary positive and conjugate factors. -/
def entryMonomial {p q : ℕ} (i j : Fin p → Fin (N+1)) (k l : Fin q → Fin (N+1))
    (U : LocalUnitary N) : ℂ :=
  (∏ a, (U:Mat N) (i a) (j a)) * (∏ b, star ((U:Mat N) (k b) (l b)))

lemma entryMonomial_row_phase {p q : ℕ}
    (i j : Fin p → Fin (N+1)) (k l : Fin q → Fin (N+1))
    (r : Fin (N+1)) (z : ℂ) (hz : star z*z=1) (U : LocalUnitary N) :
    entryMonomial i j k l (rowPhase r z hz * U) =
      (z^(multiplicity i r) * (star z)^(multiplicity k r)) * entryMonomial i j k l U := by
  simp only [entryMonomial, rowPhase_mul_entry, star_mul, apply_ite star, star_one,
    Finset.prod_mul_distrib, prod_row_phase]
  ring

/-- An arbitrary mixed Haar moment vanishes unless each row occurs equally often
among the ordinary entries and their conjugates. -/
theorem integral_entryMonomial_eq_zero_of_row_mismatch {p q : ℕ}
    (i j : Fin p → Fin (N+1)) (k l : Fin q → Fin (N+1))
    (r : Fin (N+1)) (hr : multiplicity i r ≠ multiplicity k r) :
    (∫ U, entryMonomial i j k l U ∂haar N) = 0 := by
  exact integral_eq_zero_of_row_phase _ r _ _ hr (entryMonomial_row_phase i j k l r)

end Nonadditivity.HaarMixedMoments

