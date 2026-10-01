/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FreeModel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

noncomputable section

namespace Nonadditivity.ShiftNorm

open FreeModel
open scoped BigOperators ENNReal

variable {G : Type*} [Group G] [DecidableEq G]

omit [DecidableEq G] in
theorem leftRegular_norm_le (g : G) : ‖leftRegular g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simp [leftRegular_preserves_norm]

def orbitSegment (g : G) (m : ℕ) : Hilbert G :=
  ∑ k ∈ Finset.range m, lp.single 2 (g ^ k) (1 : ℂ)

theorem orbitSegment_norm_sq (g : G) (hg : Function.Injective (fun k : ℕ => g ^ k))
    (m : ℕ) : ‖orbitSegment g m‖ ^ 2 = m := by
  classical
  have hs : orbitSegment g m =
      ∑ x ∈ (Finset.range m).image (fun k => g ^ k), lp.single 2 x (1 : ℂ) := by
    rw [Finset.sum_image]
    · rfl
    · exact fun _ _ _ _ h => hg h
  rw [hs]
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num)
    (fun _ : G => (1 : ℂ)) ((Finset.range m).image (fun k => g ^ k))
  simpa [Finset.card_image_of_injective _ hg] using h

theorem orbitSegment_shift_sub (g : G) (m : ℕ) :
    leftRegular g (orbitSegment g m) - orbitSegment g m =
      lp.single 2 (g ^ m) (1 : ℂ) - lp.single 2 1 (1 : ℂ) := by
  classical
  induction m with
  | zero => simp [orbitSegment]
  | succ m ih =>
      simp only [orbitSegment, Finset.sum_range_succ] at ih ⊢
      rw [map_add, leftRegular_single]
      rw [pow_succ']
      linear_combination (norm := module) ih

theorem orbitSegment_shift_error (g : G) (m : ℕ) :
    ‖leftRegular g (orbitSegment g m) - orbitSegment g m‖ ≤ 2 := by
  rw [orbitSegment_shift_sub]
  have h := norm_sub_le (lp.single 2 (g ^ m) (1 : ℂ) : Hilbert G) (lp.single 2 (1 : G) (1 : ℂ))
  norm_num at h
  exact h

theorem orbitSegment_symmetric_error (g : G) (m : ℕ) :
    ‖(leftRegular g + leftRegular g⁻¹) (orbitSegment g m) -
      (2 : ℂ) • orbitSegment g m‖ ≤ 4 := by
  let v := orbitSegment g m
  have heq : (leftRegular g + leftRegular g⁻¹) v - (2 : ℂ) • v =
      (leftRegular g v - v) - leftRegular g⁻¹ (leftRegular g v - v) := by
    rw [map_sub]
    have hcancel : leftRegular g⁻¹ (leftRegular g v) = v := by
      rw [← ContinuousLinearMap.comp_apply, ← leftRegular_mul]
      simp
    rw [hcancel, ContinuousLinearMap.add_apply]
    module
  rw [heq]
  calc
    _ ≤ ‖leftRegular g v - v‖ + ‖leftRegular g⁻¹ (leftRegular g v - v)‖ :=
      norm_sub_le _ _
    _ = 2 * ‖leftRegular g v - v‖ := by rw [leftRegular_preserves_norm]; ring
    _ ≤ 4 := by linarith [orbitSegment_shift_error g m]

/-- A bilateral shift and its inverse have sum norm exactly two. The lower
bound uses genuine finitely supported vectors on a growing cyclic orbit. -/
theorem norm_shift_add_inverse (g : G)
    (hg : Function.Injective (fun k : ℕ => g ^ k)) :
    ‖leftRegular g + leftRegular g⁻¹‖ = 2 := by
  apply le_antisymm
  · calc
      _ ≤ ‖leftRegular g‖ + ‖leftRegular g⁻¹‖ := norm_add_le _ _
      _ ≤ 2 := by linarith [leftRegular_norm_le g, leftRegular_norm_le g⁻¹]
  · by_contra h
    have hpos : 0 < 2 - ‖leftRegular g + leftRegular g⁻¹‖ := by linarith
    obtain ⟨m, hm⟩ := exists_nat_gt ((4 / (2 - ‖leftRegular g + leftRegular g⁻¹‖)) ^ 2)
    let v := orbitSegment g m
    have hv : ‖v‖ ^ 2 = m := orbitSegment_norm_sq g hg m
    have he : ‖(leftRegular g + leftRegular g⁻¹) v - (2 : ℂ) • v‖ ≤ 4 :=
      orbitSegment_symmetric_error g m
    have hb : 2 * ‖v‖ ≤ ‖leftRegular g + leftRegular g⁻¹‖ * ‖v‖ + 4 := by
      have ht := norm_sub_le ((leftRegular g + leftRegular g⁻¹) v)
        ((leftRegular g + leftRegular g⁻¹) v - (2 : ℂ) • v)
      simp only [sub_sub_cancel, norm_smul, Complex.norm_ofNat] at ht
      linarith [(leftRegular g + leftRegular g⁻¹).le_opNorm v]
    have hnv : ‖v‖ ≤ 4 / (2 - ‖leftRegular g + leftRegular g⁻¹‖) := by
      apply (le_div_iff₀ hpos).mpr
      nlinarith
    have hs := pow_le_pow_left₀ (norm_nonneg v) hnv 2
    linarith

end Nonadditivity.ShiftNorm
