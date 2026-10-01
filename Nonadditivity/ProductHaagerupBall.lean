/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductHaagerupHomogeneous

/-! # Polynomial radius growth in Haagerup's inequality

The length sectors are combined by Cauchy--Schwarz.  The resulting squared
constant is `(radius + 1)^3`, independent of the free group's number of generators.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.ProductHaagerupBall
open scoped BigOperators InnerProductSpace
open ProductHaagerupCreation ProductHaagerupHomogeneous

abbrev BallWords (α : Type*) (q : ℕ) := Σ l : Fin (q+1), Words α l.val

variable {α E : Type*} [DecidableEq α] [Fintype α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def energy {q : ℕ} (B : BallWords α q → E →L[ℂ] E) : ℝ := ∑ w, ‖B w‖ ^ 2

def polynomial {q : ℕ} (B : BallWords α q → E →L[ℂ] E) :
    WordHilbert α E →L[ℂ] WordHilbert α E :=
  ∑ l : Fin (q+1), ProductHaagerupHomogeneous.polynomial (fun w => B ⟨l,w⟩)

/-- Actual operator-valued convolution in a free-group ball satisfies the
radius-cubed squared-norm estimate. -/
theorem polynomial_norm_sq_le {q : ℕ} (B : BallWords α q → E →L[ℂ] E)
    (hred : ∀ w, ¬ FreeGroup.IsReduced w.2.1 → B w = 0) :
    ‖polynomial B‖ ^ 2 ≤ ((q+1 : ℕ) : ℝ)^3 * energy B := by
  let e : Fin (q+1) → ℝ := fun l => coefficientEnergy (fun w => B ⟨l,w⟩)
  have he (l : Fin (q+1)) : 0 ≤ e l := coefficientEnergy_nonneg _
  have hn : ‖polynomial B‖ ≤ ∑ l : Fin (q+1), (l.val+1 : ℕ) * Real.sqrt (e l) := by
    unfold polynomial
    exact (norm_sum_le Finset.univ (fun l : Fin (q+1) =>
      ProductHaagerupHomogeneous.polynomial (fun w => B ⟨l,w⟩))).trans
      (Finset.sum_le_sum (fun l _ =>
      polynomial_norm_le _ (fun w hw => hred ⟨l,w⟩ hw)))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun l : Fin (q+1) => ((l.val+1 : ℕ) : ℝ)) (fun l => Real.sqrt (e l))
  have hweights : (∑ l : Fin (q+1), (((l.val+1 : ℕ) : ℝ))^2) ≤
      ((q+1 : ℕ) : ℝ)^3 := by
    calc
      _ ≤ ∑ _l : Fin (q+1), (((q+1 : ℕ) : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro l _
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast (by omega : l.val+1 ≤ q+1)
      _ = _ := by simp; ring
  have hsum : (∑ l : Fin (q+1), (Real.sqrt (e l))^2) = energy B := by
    simp_rw [Real.sq_sqrt (he _)]
    simp only [e, coefficientEnergy, energy, Fintype.sum_sigma]
  have hs := pow_le_pow_left₀ (norm_nonneg (polynomial B)) hn 2
  apply hs.trans (hcs.trans _)
  rw [hsum]
  exact mul_le_mul_of_nonneg_right hweights (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end Nonadditivity.ProductHaagerupBall
