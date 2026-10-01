/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCS
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # A projective quantum union bound

Sequential orthogonal projections lose at most four times the sum of their
individual failure probabilities on the original vector. The proof uses
telescoping, Pythagoras, and finite Cauchy--Schwarz. This is the vector form
of Gao's quantum union bound (arXiv:1410.5688); see also O'Donnell and
Venkateswaran, arXiv:2103.07827. No decoding-error estimate is postulated.
-/
noncomputable section
namespace Nonadditivity.QuantumCoding
open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An actual bounded orthogonal projection, specified by its algebraic laws. -/
structure Projection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  map : E →L[ℂ] E
  symmetric : ∀ x y, ⟪map x, y⟫_ℂ = ⟪x, map y⟫_ℂ
  idempotent : ∀ x, map (map x) = map x

namespace Projection

theorem inner_map_self (P : Projection E) (x : E) :
    ⟪x, P.map x⟫_ℂ = ⟪P.map x, P.map x⟫_ℂ := by
  rw [P.symmetric, P.idempotent]

theorem pythagoras (P : Projection E) (x : E) :
    ‖x‖^2 = ‖P.map x‖^2 + ‖x-P.map x‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ), P.inner_map_self, inner_self_eq_norm_sq (𝕜 := ℂ)]
  ring

theorem inner_reject (P : Projection E) (x y : E) :
    ⟪x, y-P.map y⟫_ℂ = ⟪x-P.map x, y-P.map y⟫_ℂ := by
  rw [inner_sub_left, P.symmetric]
  simp only [map_sub, P.idempotent, sub_self, inner_zero_right, sub_zero]

/-- The unnormalized state vector after the first `n` selected outcomes. -/
def trajectory (P : ℕ → Projection E) (x : E) : ℕ → E
  | 0 => x
  | n+1 => (P n).map (trajectory P x n)

theorem energy_identity (P : ℕ → Projection E) (x : E) (n : ℕ) :
    ‖x‖^2-‖trajectory P x n‖^2 =
      ∑ i ∈ Finset.range n, ‖trajectory P x i-trajectory P x (i+1)‖^2 := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [Finset.sum_range_succ, ←ih]
    have hp := (P n).pythagoras (trajectory P x n)
    simp only [trajectory] at hp ⊢
    linarith

theorem displacement_identity (P : ℕ → Projection E) (x : E) (n : ℕ) :
    x-trajectory P x n =
      ∑ i ∈ Finset.range n, (trajectory P x i-trajectory P x (i+1)) := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih => rw [Finset.sum_range_succ, ←ih]; abel

theorem overlap_identity (P : ℕ → Projection E) (x : E) (n : ℕ) :
    ⟪x, x-trajectory P x n⟫_ℂ =
      ∑ i ∈ Finset.range n,
        ⟪x-(P i).map x, trajectory P x i-trajectory P x (i+1)⟫_ℂ := by
  rw [displacement_identity, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (P i).inner_reject x (trajectory P x i)

/-- Gao's bound, without a dimension factor or a normalization assumption. -/
theorem union_bound (P : ℕ → Projection E) (x : E) (n : ℕ) :
    ‖x‖^2-‖trajectory P x n‖^2 ≤
      4*∑ i ∈ Finset.range n, ‖x-(P i).map x‖^2 := by
  let a : ℕ → ℝ := fun i => ‖x-(P i).map x‖
  let b : ℕ → ℝ := fun i => ‖trajectory P x i-trajectory P x (i+1)‖
  let D := ‖x‖^2-‖trajectory P x n‖^2
  let B := ∑ i ∈ Finset.range n, a i^2
  let s := ∑ i ∈ Finset.range n, a i*b i
  have hD : D = ∑ i ∈ Finset.range n, b i^2 := energy_identity P x n
  have hD0 : 0≤D := by rw [hD]; positivity
  have hB0 : 0≤B := by dsimp [B]; positivity
  have hs0 : 0≤s := by dsimp [s,a,b]; positivity
  have hc : s^2≤B*D := by
    rw [hD]
    exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) a b
  have ho : (⟪x, x-trajectory P x n⟫_ℂ).re ≤ s := by
    rw [overlap_identity, Complex.re_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  have he : D ≤ 2*s := by
    have hn := norm_sub_sq x (trajectory P x n) (𝕜 := ℂ)
    have hn0 := sq_nonneg ‖x-trajectory P x n‖
    have hid : (⟪x, x-trajectory P x n⟫_ℂ).re =
        ‖x‖^2-(⟪x, trajectory P x n⟫_ℂ).re := by
      rw [inner_sub_right, Complex.sub_re]
      congr 1
      exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    simp only [RCLike.re_eq_complex_re] at hn
    rw [hid] at ho
    dsimp [D]
    linarith
  have hsq : D^2≤4*B*D := by
    have hh := mul_self_le_mul_self hD0 he
    nlinarith
  change D ≤ 4*B
  by_contra h
  have hpos : 0 < D*(D-4*B) := mul_pos (by linarith) (by linarith)
  nlinarith

end Projection
end Nonadditivity.QuantumCoding
