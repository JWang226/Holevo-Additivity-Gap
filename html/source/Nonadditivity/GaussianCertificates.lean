/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GaussianQuadratic

/-! # A concrete Gaussian union budget for the one-block construction

All probability estimates are derived in `GaussianQuadratic`. This file fixes
explicit constants for combining the isometry and observable tests.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace Nonadditivity.GaussianCertificates

/-- The two finite nets fit inside the proved Gaussian probability budget. -/
theorem net_budget_lt_one (K N : ℕ) (hK : 4096 ≤ K) (hN : K ^ 2 ≤ N) :
    2 * (9 : ℝ) ^ (2 * N) * exp (-(K : ℝ) * N / 128) +
      2 * ((5 : ℝ) ^ (K ^ 2) * (9 : ℝ) ^ (2 * N)) *
        exp (-(63 / 2 : ℝ) * N) < 1 := by
  have hKr : (4096 : ℝ) ≤ K := by exact_mod_cast hK
  have hNr : (K : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hNpos : (1 : ℝ) ≤ N := by nlinarith
  have h9 : (9 : ℝ) ≤ exp 8 := by linarith [add_one_le_exp (8 : ℝ)]
  have h5 : (5 : ℝ) ≤ exp 4 := by linarith [add_one_le_exp (4 : ℝ)]
  have hp9 : (9 : ℝ) ^ (2 * N) ≤ exp (16 * N) := by
    calc
      _ ≤ (exp 8) ^ (2 * N) := pow_le_pow_left₀ (by norm_num) h9 _
      _ = _ := by rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hp5 : (5 : ℝ) ^ (K ^ 2) ≤ exp (4 * N) := by
    calc
      _ ≤ (exp 4) ^ (K ^ 2) := pow_le_pow_left₀ (by norm_num) h5 _
      _ = exp (4 * (K : ℝ) ^ 2) := by rw [← exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ _ := exp_le_exp.mpr (by nlinarith)
  have hfirst : 2 * (9 : ℝ) ^ (2 * N) * exp (-(K : ℝ) * N / 128) ≤
      2 * exp (-10 * N) := by
    calc
      _ ≤ 2 * exp (16 * N) * exp (-(K : ℝ) * N / 128) := by gcongr
      _ = 2 * exp (16 * N - (K : ℝ) * N / 128) := by
        rw [mul_assoc, ← exp_add]
        congr 2
        ring
      _ ≤ _ := by
        gcongr
        nlinarith [mul_nonneg (by linarith : 0 ≤ (K : ℝ) - 4096) (by positivity : 0 ≤ (N : ℝ))]
  have hsecond : 2 * ((5 : ℝ) ^ (K ^ 2) * (9 : ℝ) ^ (2 * N)) *
      exp (-(63 / 2 : ℝ) * N) ≤ 2 * exp (-10 * N) := by
    calc
      _ ≤ 2 * (exp (4 * N) * exp (16 * N)) * exp (-(63 / 2 : ℝ) * N) := by gcongr
      _ = 2 * exp (-(23 / 2 : ℝ) * N) := by
        rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]
        congr 2
        ring
      _ ≤ _ := by gcongr; linarith
  have hlast : 4 * exp (-10 * (N : ℝ)) < 1 := by
    rw [show -10 * (N : ℝ) = -(10 * N) by ring, exp_neg]
    apply (mul_inv_lt_iff₀ (exp_pos _)).mpr
    linarith [add_one_le_exp (10 * (N : ℝ))]
  linarith



/-- A concrete Gaussian sample simultaneously passes the two net families.
The premises are only deterministic norm, trace, and cardinality inequalities. -/
theorem exists_isometry_and_observable_tests
    {E J₀ J₁ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype J₀] [Fintype J₁]
    (K N : ℕ) (hK : 4096 ≤ K) (hN : K ^ 2 ≤ N)
    (T₀ : J₀ → E →L[ℝ] E) (T₁ : J₁ → E →L[ℝ] E)
    (hT₀ : ∀ j, (T₀ j).toLinearMap.IsSymmetric)
    (hT₁ : ∀ j, (T₁ j).toLinearMap.IsSymmetric)
    (hnorm₀ : ∀ j, (2 * (K : ℝ) * N) * ‖T₀ j‖ ≤ 1)
    (hnorm₁ : ∀ j, (2 * (K : ℝ) * N) * ‖T₁ j‖ ≤ 1)
    (hvar₀ : ∀ j, (2 * (K : ℝ) * N) *
      ((T₀ j).toLinearMap * (T₀ j).toLinearMap).trace ℝ E ≤ 1)
    (hvar₁ : ∀ j, (2 * (K : ℝ) ^ 2 * N) *
      ((T₁ j).toLinearMap * (T₁ j).toLinearMap).trace ℝ E ≤ 1)
    (hcard₀ : (Fintype.card J₀ : ℝ) ≤ (9 : ℝ) ^ (2 * N))
    (hcard₁ : (Fintype.card J₁ : ℝ) ≤ (5 : ℝ) ^ (K ^ 2) * (9 : ℝ) ^ (2 * N)) :
    ∃ z : E,
      (∀ j, |inner ℝ (T₀ j z) z - (T₀ j).toLinearMap.trace ℝ E| < 1 / 4) ∧
      (∀ j, |inner ℝ (T₁ j z) z - (T₁ j).toLinearMap.trace ℝ E| < 64 / K) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (pow_pos (by omega : 0 < K) _) hN
    exact_mod_cast this
  let T : J₀ ⊕ J₁ → E →L[ℝ] E := Sum.elim T₀ T₁
  let s : J₀ ⊕ J₁ → ℝ := Sum.elim (fun _ => (K : ℝ) * N / 16) (fun _ => (K : ℝ) * N / 2)
  let t : J₀ ⊕ J₁ → ℝ := Sum.elim (fun _ => 1 / 4) (fun _ => 64 / (K : ℝ))
  have hsym (j) : (T j).toLinearMap.IsSymmetric := by
    cases j with
    | inl j => exact hT₀ j
    | inr j => exact hT₁ j
  have hsmall (j) : s j * ‖T j‖ ≤ 1 / 4 := by
    cases j with
    | inl j => dsimp [s, T]; nlinarith [hnorm₀ j]
    | inr j => dsimp [s, T]; nlinarith [hnorm₁ j]
  have hb₀ (j : J₀) : -(K : ℝ) * N / 16 * (1 / 4) +
      4 * ((K : ℝ) * N / 16) ^ 2 *
        ((T₀ j).toLinearMap * (T₀ j).toLinearMap).trace ℝ E ≤ -(K : ℝ) * N / 128 := by
    have hv := mul_le_mul_of_nonneg_left (hvar₀ j)
      (show 0 ≤ (K : ℝ) * N / 128 by positivity)
    nlinarith
  have hb₁ (j : J₁) : -((K : ℝ) * N / 2) * (64 / (K : ℝ)) +
      4 * ((K : ℝ) * N / 2) ^ 2 *
        ((T₁ j).toLinearMap * (T₁ j).toLinearMap).trace ℝ E ≤ -(63 / 2 : ℝ) * N := by
    have hv := mul_le_mul_of_nonneg_left (hvar₁ j) (show 0 ≤ (N : ℝ) / 2 by positivity)
    have hcancel : -((K : ℝ) * N / 2) * (64 / (K : ℝ)) = -32 * N := by
      field_simp
      ring
    rw [hcancel]
    nlinarith
  have hbudget : (∑ j, 2 * exp (-s j * t j +
      4 * s j ^ 2 * ((T j).toLinearMap * (T j).toLinearMap).trace ℝ E)) < 1 := by
    calc
      _ ≤ (∑ _ : J₀, 2 * exp (-(K : ℝ) * N / 128)) +
          ∑ _ : J₁, 2 * exp (-(63 / 2 : ℝ) * N) := by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j _
          dsimp [s, t, T]
          gcongr
          convert hb₀ j using 1; ring
        · apply Finset.sum_le_sum
          intro j _
          dsimp [s, t, T]
          gcongr
          exact hb₁ j
      _ ≤ 2 * (9 : ℝ) ^ (2 * N) * exp (-(K : ℝ) * N / 128) +
          2 * ((5 : ℝ) ^ (K ^ 2) * (9 : ℝ) ^ (2 * N)) * exp (-(63 / 2 : ℝ) * N) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc
          _ ≤ ((9 : ℝ) ^ (2 * N)) * (2 * exp (-(K : ℝ) * N / 128)) +
              ((5 : ℝ) ^ (K ^ 2) * (9 : ℝ) ^ (2 * N)) * (2 * exp (-(63 / 2 : ℝ) * N)) := by
            gcongr
          _ = _ := by ring
      _ < 1 := net_budget_lt_one K N hK hN
  obtain ⟨z, hz⟩ := GaussianQuadratic.exists_simultaneous_quadratic_bounds T hsym s t
    (fun j => by cases j <;> dsimp [s] <;> positivity) hsmall hbudget
  exact ⟨z, fun j => hz (.inl j), fun j => hz (.inr j)⟩

end Nonadditivity.GaussianCertificates
