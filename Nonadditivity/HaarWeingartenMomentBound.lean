/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarWeingartenSymmetry

/-! # Assembly of weighted Haar moment estimates

This finite-sum step records exactly how the matching count, singleton support
bound, and weighted inverse row bound combine.  Its explicit inputs are separate
finite combinatorial estimates, not an assumed Haar moment formula.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarInvariantTensor

open MeasureTheory HaarModel
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- The complete summation step, with arbitrary nonnegative weight parameters.
`h` is the high-multiplicity exponent and `e` the number of singleton entries. -/
theorem norm_moment_le_of_matching_and_inverse {N p : ℕ} (hp : p ≤ N+1)
    (i j k l : Tuple N p) (h e : ℕ) (r η C : ℝ)
    (hr : 0 ≤ r) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hpη : (p:ℝ) ≤ r*η^2)
    (hmatching : ∀ π : Perm p, matchingMultiplicity i j k l π ≤ p^(π.support.card+h))
    (hsingle : ∀ π : Perm p, 0 < matchingMultiplicity i j k l π → e ≤ 2*π.support.card)
    (hinverse : (∑ π : Perm p, r^π.support.card * ‖weingarten N p 1 π‖) ≤ C) :
    ‖∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N‖ ≤
      C*(p:ℝ)^h*η^e := by
  have hpoint (π : Perm p) :
      (matchingMultiplicity i j k l π : ℝ) * ‖weingarten N p 1 π‖ ≤
        ((p:ℝ)^h * η^e) * (r^π.support.card * ‖weingarten N p 1 π‖) := by
    by_cases hz : matchingMultiplicity i j k l π = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
      positivity
    · have he := hsingle π (Nat.pos_of_ne_zero hz)
      have hd : (p:ℝ)^π.support.card ≤ r^π.support.card * η^e := by
        calc
          _ ≤ (r*η^2)^π.support.card := pow_le_pow_left₀ (by positivity) hpη _
          _ = r^π.support.card * η^(2*π.support.card) := by rw [mul_pow, ← pow_mul]
          _ ≤ r^π.support.card * η^e :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη0 hη1 he) (pow_nonneg hr _)
      have hc : (matchingMultiplicity i j k l π : ℝ) ≤ (p:ℝ)^h * (p:ℝ)^π.support.card := by
        have hc' : (matchingMultiplicity i j k l π : ℝ) ≤ (p:ℝ)^(π.support.card+h) :=
          by exact_mod_cast hmatching π
        simpa only [pow_add, mul_comm] using hc'
      calc
        _ ≤ ((p:ℝ)^h * (p:ℝ)^π.support.card) * ‖weingarten N p 1 π‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ ((p:ℝ)^h * (r^π.support.card*η^e)) * ‖weingarten N p 1 π‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (norm_nonneg _)
        _ = _ := by ring
  calc
    _ ≤ ∑ π : Perm p, (matchingMultiplicity i j k l π : ℝ) * ‖weingarten N p 1 π‖ :=
      norm_integral_entryMonomial_le_relative hp i j k l
    _ ≤ ∑ π : Perm p, ((p:ℝ)^h*η^e) * (r^π.support.card*‖weingarten N p 1 π‖) :=
      Finset.sum_le_sum (fun π _ => hpoint π)
    _ = ((p:ℝ)^h*η^e) * (∑ π : Perm p, r^π.support.card*‖weingarten N p 1 π‖) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((p:ℝ)^h*η^e)*C := mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = C*(p:ℝ)^h*η^e := by ring

end Nonadditivity.HaarInvariantTensor
