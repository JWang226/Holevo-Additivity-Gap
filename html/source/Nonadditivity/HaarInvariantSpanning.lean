/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarInvariantCommutant

/-! # The unitary invariant tensors are spanned by permutations

The proof uses only phase invariance, matrix tensor powers, and finite-dimensional
spectral linear algebra.  The resulting inverse-Gram formula is an identity for
actual Haar integrals, with no invariant-spanning assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Nonadditivity.HaarInvariantTensor

open MeasureTheory HaarModel HaarAveraging
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

/-- Invariants are exactly the permutation contractions in the stable range. -/
theorem invariant_eq_contractions {N p : ℕ} (e : Fin p ↪ Fin (N+1))
    (v : Pair N p → ℂ) (hv : ∀ U : LocalUnitary N, mixed N p U *ᵥ v = v) :
    v = contractions N p *ᵥ (fun σ : Perm p => v (e ∘ σ,e)) := by
  classical
  let c : Perm p → ℂ := fun σ => v (e ∘ σ,e)
  let w : Pair N p → ℂ := v - contractions N p *ᵥ c
  have hw (U : LocalUnitary N) : mixed N p U *ᵥ w = w := by
    dsimp [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, mixed_mul_contractions, hv]
  have hws (σ : Perm p) : w (e ∘ σ,e) = 0 := by
    change v (e ∘ σ,e) - (contractions N p *ᵥ c) (e ∘ σ,e) = 0
    rw [contractions_row_mulVec]
    exact sub_self _
  have hwe (x : Tuple N p) : w (x,e) = 0 := by
    by_cases hm : ∀ r, HaarMixedMoments.multiplicity x r = HaarMixedMoments.multiplicity e r
    · obtain ⟨σ, hσ⟩ := exists_perm_of_multiplicity_eq x e hm
      rw [hσ]
      exact hws σ
    · push_neg at hm
      obtain ⟨r, hr⟩ := hm
      exact invariant_eq_zero_of_multiplicity_ne w hw x e r hr
  let T : Matrix (Tuple N p) (Tuple N p) ℂ := fun x y => w (x,y)
  have hTu (U : LocalUnitary N) :
      power p (U : HaarFourthMoments.Mat N) * T = T * power p (U : HaarFourthMoments.Mat N) := by
    apply (mixed_fixed_iff_commute U T).mp
    exact hw U
  have hT : T = 0 := eq_zero_of_commute_power_of_column_zero e T
    (HaarInvariantCommutant.commute_power_of_unitary T hTu) hwe
  funext xy
  have h := congrFun (congrFun hT xy.1) xy.2
  change v xy - (contractions N p *ᵥ c) xy = 0 at h
  exact sub_eq_zero.mp h

theorem invariant_mem_range_contractions {N p : ℕ} (hp : p ≤ N+1)
    (v : Pair N p → ℂ) (hv : ∀ U : LocalUnitary N, mixed N p U *ᵥ v = v) :
    ∃ c : Perm p → ℂ, v = contractions N p *ᵥ c := by
  let e : Fin p ↪ Fin (N+1) := ⟨Fin.castLE hp, Fin.castLE_injective hp⟩
  exact ⟨_, invariant_eq_contractions e v hv⟩

/-- Exact arbitrary-order Weingarten integration: the actual Haar projection is
the inverse-Gram projection onto the permutation contraction tensors. -/
theorem average_eq_weingarten {N p : ℕ} (hp : p ≤ N+1) :
    average (mixed N p) = contractions N p * weingarten N p * (contractions N p)ᴴ := by
  classical
  let e : Fin p ↪ Fin (N+1) := ⟨Fin.castLE hp, Fin.castLE_injective hp⟩
  let P := average (mixed N p)
  let B := contractions N p
  let C : Matrix (Perm p) (Pair N p) ℂ := fun σ ab => P (e ∘ σ,e) ab
  have hfactor : P = B * C := by
    ext xy ab
    have hv (U : LocalUnitary N) :
        mixed N p U *ᵥ (fun xy => P xy ab) = (fun xy => P xy ab) := by
      funext xy
      change (mixed N p U * average (mixed N p)) xy ab = average (mixed N p) xy ab
      rw [mul_average _ (continuous_mixed N p) (mixed_mul N p)]
    exact congrFun (invariant_eq_contractions e (fun xy => P xy ab) hv) xy
  have hleft : Bᴴ * P = Bᴴ := by
    have h := congrArg Matrix.conjTranspose (average_mul_contractions N p)
    simpa only [Matrix.conjTranspose_mul, (mixed_average_hermitian N p).eq] using h
  have hgram : gram N p * C = Bᴴ := by
    change (Bᴴ * B) * C = Bᴴ
    rw [Matrix.mul_assoc, ← hfactor, hleft]
  have hc : C = weingarten N p * Bᴴ := by
    rw [← hgram, ← Matrix.mul_assoc, weingarten_mul_gram hp, Matrix.one_mul]
  rw [show average (mixed N p) = B*C from hfactor, hc, ← Matrix.mul_assoc]

/-- The full entrywise unitary Weingarten formula, proved for normalized Haar
measure at every degree up to the dimension. -/
theorem integral_entryMonomial_eq_weingarten {N p : ℕ} (hp : p ≤ N+1)
    (i j k l : Tuple N p) :
    (∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N) =
      ∑ σ : Perm p, ∑ τ : Perm p,
        (if i = k ∘ σ then 1 else 0) * weingarten N p σ τ *
          (if j = l ∘ τ then 1 else 0) := by
  have h := congrFun (congrFun (average_eq_weingarten hp) (i,k)) (j,l)
  change (∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N) = _ at h
  rw [h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, contractions,
    apply_ite star, star_one, star_zero, Finset.sum_mul]
  rw [Finset.sum_comm]

end Nonadditivity.HaarInvariantTensor
