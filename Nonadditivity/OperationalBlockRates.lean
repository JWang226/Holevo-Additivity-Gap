/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalCapacity
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Full-length rate preservation when padding fixed-size channel blocks -/

noncomputable section
namespace Nonadditivity.Operational.BlockRates
open Filter Topology

/-- Number of complete blocks of `k+1` uses within a length-`n+1` code. -/
def blockCount (k n : ℕ) : ℕ := (n+1)/(k+1)

/-- Positive-power index of the complete blocks; only its eventual values matter. -/
def blockIndex (k n : ℕ) : ℕ := blockCount k n - 1

theorem blockCount_tendsto (k : ℕ) : Tendsto (blockCount k) atTop atTop :=
  (Nat.tendsto_div_const_atTop (Nat.succ_ne_zero k)).comp (tendsto_add_atTop_nat 1)

theorem blockIndex_tendsto (k : ℕ) : Tendsto (blockIndex k) atTop atTop :=
  (tendsto_sub_atTop_nat 1).comp (blockCount_tendsto k)

theorem blockCount_pos {k n : ℕ} (h : k ≤ n) : 0 < blockCount k n := by
  unfold blockCount
  exact Nat.div_pos (by omega) (by omega)

theorem blockIndex_add_one {k n : ℕ} (h : k ≤ n) :
    blockIndex k n + 1 = blockCount k n := by
  unfold blockIndex
  exact Nat.sub_add_cancel (blockCount_pos h)

/-- At most `k` padding uses are discarded, so their relative cost vanishes. -/
theorem coveredFraction_tendsto_one (k : ℕ) :
    Tendsto (fun n => (blockCount k n : ℝ) * ((k+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hmod := (tendsto_mod_div_atTop_nhds_zero_nat (Nat.succ_pos k)).comp
    (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ => 1 - (((n+1)%(k+1) : ℕ) : ℝ) /
      ((n+1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hmod
  convert hlim using 1
  funext n
  have hn : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hid : ((((n+1)%(k+1) : ℕ) : ℝ)) + ((k+1 : ℕ) : ℝ) * (blockCount k n : ℝ) =
      ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.mod_add_div (n+1) (k+1)
  field_simp
  nlinarith

theorem blockCount_ratio_tendsto (k : ℕ) :
    Tendsto (fun n => (blockCount k n : ℝ) / ((n+1 : ℕ) : ℝ))
      atTop (𝓝 (1 / ((k+1 : ℕ) : ℝ))) := by
  have h := (coveredFraction_tendsto_one k).div_const ((k+1 : ℕ) : ℝ)
  convert h using 1
  funext n
  have hk : (((k+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem blockIndex_ratio_tendsto (k : ℕ) :
    Tendsto (fun n => ((blockIndex k n+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ))
      atTop (𝓝 (1 / ((k+1 : ℕ) : ℝ))) := by
  apply (blockCount_ratio_tendsto k).congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [blockIndex_add_one hn]

/-- Any eventual lower communication rate on complete blocks transfers to all
lengths with exactly the factor `k+1`, including the intervening padded lengths. -/
theorem rescaled_rate (k : ℕ) (f : ℕ → ℝ) {R : ℝ}
    (hR : ∀ r < R, ∀ᶠ n in atTop, r ≤ f n / ((n+1 : ℕ) : ℝ)) :
    ∀ r < R / ((k+1 : ℕ) : ℝ),
      ∀ᶠ n in atTop, r ≤ f (blockIndex k n) / ((n+1 : ℕ) : ℝ) := by
  intro r hr
  have hk : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have hrR : r * ((k+1 : ℕ) : ℝ) < R := (lt_div_iff₀ hk).mp hr
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hrs' : r < s / ((k+1 : ℕ) : ℝ) := (lt_div_iff₀ hk).mpr hrs
  have hlimit : Tendsto (fun n => s *
      (((blockIndex k n+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ)))
      atTop (𝓝 (s / ((k+1 : ℕ) : ℝ))) := by
    simpa only [mul_one_div] using (blockIndex_ratio_tendsto k).const_mul s
  have hlower := (blockIndex_tendsto k).eventually (hR s hsR)
  have hnear : ∀ᶠ n in atTop, r < s *
      (((blockIndex k n+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ)) :=
    hlimit.eventually (lt_mem_nhds hrs')
  filter_upwards [hlower, hnear] with n hn hsn
  have hden : (0 : ℝ) < ((blockIndex k n+1 : ℕ) : ℝ) := by positivity
  have hn' := (le_div_iff₀ hden).mp hn
  apply hsn.le.trans
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hn' (by positivity)

/-- Vanishing errors remain vanishing under the complete-block subsequence. -/
theorem error_subsequence {E : ℕ → ℝ} (k : ℕ)
    (hE : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun n => E (blockIndex k n)) atTop (𝓝 0) :=
  hE.comp (blockIndex_tendsto k)

end Nonadditivity.Operational.BlockRates
