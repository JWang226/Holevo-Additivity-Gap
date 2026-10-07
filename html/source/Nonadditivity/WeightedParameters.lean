/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeightedBlock
import Nonadditivity.WeightedBellScalar

/-! A strict amplification budget leaves room for a nonzero perturbation of the
unitary probabilities before choosing the finite-moment damping order. -/
noncomputable section
namespace Nonadditivity.WeightedParameters
open BlockScalars Filter Topology
open scoped Matrix.Norms.L2Operator

/-- A positive scalar gap absorbs the exact output-filter error `δ(2+δ)`. -/
theorem exists_norm_budget {a b c : ℝ} (hab : a<b) (hc : 0<c) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ a*c+δ*(2+δ)≤b*c := by
  let d : ℝ := (b-a)*c
  have hd : 0<d := mul_pos (sub_pos.mpr hab) hc
  let δ : ℝ := min 1 (d/3)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  have hδone : δ≤1 := min_le_left _ _
  have hδd : δ≤d/3 := min_le_right _ _
  refine ⟨δ,hδ,hδone,?_⟩
  have hsq : δ^2≤δ := by nlinarith
  dsimp [d] at hδd
  nlinarith

/-- Spend half the entropy tolerance on uniform damping and retain a strictly
positive norm budget for nonuniform probabilities. -/
theorem exists_amplification_budget {c η : ℝ} (hc : 0<c) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧
      amplification (η/2)*c+δ*(2+δ)≤amplification η*c := by
  apply exists_norm_budget ?_ hc
  unfold amplification
  exact Real.exp_lt_exp.mpr (by linarith)

theorem exists_collinsYoun_budget {K n : ℕ} {η : ℝ}
    (hK : 2≤K) (hn : 1≤n) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧
      amplification (η/2)*collinsYounConstant K n+δ*(2+δ) ≤
        amplification η*collinsYounConstant K n :=
  exists_amplification_budget (collinsYounConstant_pos hK hn) hη

/-- A function vanishing at zero is small at some strictly positive parameter,
with any prescribed positive upper bound on that parameter. -/
theorem exists_positive_small_of_tendsto {f : ℝ → ℝ}
    (hf : Tendsto f (𝓝 0) (𝓝 0)) {ε b : ℝ} (hε : 0<ε) (hb : 0<b) :
    ∃ t : ℝ, 0<t ∧ t<b ∧ f t<ε := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), f t<ε := hf.eventually (gt_mem_nhds hε)
  obtain ⟨r,hr,hclose⟩ := Metric.eventually_nhds_iff.mp hevent
  let t : ℝ := min (r/2) (b/2)
  have ht : 0<t := lt_min (by positivity) (by positivity)
  have htr : t<r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htb : t<b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨t,ht,htb,hclose ?_⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using htr

/-- Choose genuine nonuniform probabilities as close as required to the uniform
output scaling, before any finite input dimension or moment order is chosen. -/
theorem exists_small_perturbation {K : ℕ} [NeZero K] (hK : 2≤K) (n : ℕ)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ t : ℝ, 0<t ∧ t<1/(K : ℝ) ∧
      ‖WeightedBlock.outputScale (WeightedBellScalar.perturbedWeights hK t) n-1‖≤δ := by
  have hKpos : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hlim := WeightedBlock.outputScale_norm_sub_one_tendsto
    (WeightedBellScalar.perturbedWeights hK)
    (WeightedBellScalar.continuous_perturbedWeights_apply hK)
    (WeightedBellScalar.perturbedWeights_zero hK) n
  obtain ⟨t,ht,htK,hsmall⟩ := exists_positive_small_of_tendsto hlim hδ
    (show 0<1/(K : ℝ) by positivity)
  exact ⟨t,ht,htK,hsmall.le⟩

end Nonadditivity.WeightedParameters
