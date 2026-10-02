/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCS

/-! # Crossing pair contractions

The two paired indices in `Aᵢ Bⱼ Cᵢ Dⱼ` cross. Applying ordinary
Cauchy--Schwarz separately to the two sums loses a cardinal factor. An actual
isometric permutation of the two memory registers avoids that loss.
-/

noncomputable section

namespace Nonadditivity.NoncommutativeCS

open scoped BigOperators InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Swapping two finite Hilbert direct sums preserves the Hilbert norm. -/
def swap : DirectSum I (DirectSum J E) ≃ₗᵢ[𝕜] DirectSum J (DirectSum I E) where
  toFun x := WithLp.toLp 2 (fun j => WithLp.toLp 2 (fun i => x i j))
  invFun x := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => x j i))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_comm

omit [CompleteSpace E] in
@[simp] theorem swap_apply (x : DirectSum I (DirectSum J E)) (j : J) (i : I) :
    swap (𝕜 := 𝕜) x j i = x i j := rfl

/-- Both indices may remain open across a uniformly bounded middle factor. -/
theorem crossing_sum_norm_le
    (A C : I → E →L[𝕜] E) (B D : J → E →L[𝕜] E)
    (X : I → J → E →L[𝕜] E) (q : ℝ) (hq : 0 ≤ q)
    (hX : ∀ i j, ‖X i j‖ ≤ q) :
    ‖∑ i, ∑ j, A i ∘L B j ∘L X i j ∘L C i ∘L D j‖ ≤
      Real.sqrt ‖rowGram A‖ * Real.sqrt ‖rowGram B‖ * q *
        Real.sqrt ‖columnGram C‖ * Real.sqrt ‖columnGram D‖ := by
  let M : DirectSum I (DirectSum J E) →L[𝕜] DirectSum I (DirectSum J E) :=
    diagonal (fun i => diagonal (X i))
  have hM : ‖M‖ ≤ q := diagonal_norm_le _ q hq
    (fun i => diagonal_norm_le _ q hq (hX i))
  let S : DirectSum J (DirectSum I E) →L[𝕜] DirectSum I (DirectSum J E) :=
    (swap (𝕜 := 𝕜) (E := E) (I := J) (J := I)).toLinearIsometry.toContinuousLinearMap
  have hS : ‖S‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  let V := (amplify (I := J) (column C)) ∘L column D
  have hV : ‖V‖ ≤ Real.sqrt ‖columnGram C‖ * Real.sqrt ‖columnGram D‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul ((amplify_norm_le _).trans (column_norm_le C)) (column_norm_le D)
        (norm_nonneg _) (Real.sqrt_nonneg _))
  let W := row A ∘L amplify (I := I) (row B)
  have hW : ‖W‖ ≤ Real.sqrt ‖rowGram A‖ * Real.sqrt ‖rowGram B‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (row_norm_le A) ((amplify_norm_le _).trans (row_norm_le B))
        (norm_nonneg _) (Real.sqrt_nonneg _))
  have hid : ∑ i, ∑ j, A i ∘L B j ∘L X i j ∘L C i ∘L D j = W ∘L M ∘L S ∘L V := by
    ext x
    simp [W, M, S, V, swap, map_sum]
  rw [hid]
  calc
    _ ≤ ‖W‖ * (‖M‖ * (‖S‖ * ‖V‖)) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (Real.sqrt ‖rowGram A‖ * Real.sqrt ‖rowGram B‖) *
        (q * (1 * (Real.sqrt ‖columnGram C‖ * Real.sqrt ‖columnGram D‖))) :=
      mul_le_mul hW (mul_le_mul hM (mul_le_mul hS hV (norm_nonneg _) (by norm_num))
        (by positivity) hq) (by positivity) (by positivity)
    _ = _ := by ring

/-- A crossing pair partition, with the exact four Gram factors. -/
theorem crossing_pair_norm_le
    (A C : I → E →L[𝕜] E) (B D : J → E →L[𝕜] E) :
    ‖∑ i, ∑ j, A i ∘L B j ∘L C i ∘L D j‖ ≤
      Real.sqrt ‖rowGram A‖ * Real.sqrt ‖rowGram B‖ *
        Real.sqrt ‖columnGram C‖ * Real.sqrt ‖columnGram D‖ := by
  simpa only [ContinuousLinearMap.id_comp, mul_one] using
    crossing_sum_norm_le A C B D (fun _ _ => ContinuousLinearMap.id 𝕜 E) 1 (by norm_num)
      (fun _ _ => ContinuousLinearMap.norm_id_le)

end Nonadditivity.NoncommutativeCS
