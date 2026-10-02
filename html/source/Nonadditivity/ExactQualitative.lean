/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DeterministicQualitative
import Nonadditivity.WeightedBlockBell
import Nonadditivity.WeightedParameters
import Nonadditivity.WeightedPositivity

/-! # The exact qualitative bounds without Haar assumptions

A nonzero arbitrarily small perturbation of the branch weights supplies a
strict Bell entropy reserve. Its effect on the adjoint certificate fits inside
the prescribed single-use tolerance. Finite-moment damping is chosen only after
this reserve is fixed, so its entropy error is absorbed completely. This proves
the displayed qualitative bounds with no error in the two-use lower bound.

The construction is different from the manuscript's Haar construction and does
not supply its sharp prescribed local dimension.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Nonadditivity.ExactQualitative
open Entropy Channels Channels.KrausChannel AdjointPurity BlockConstruction
open Conversion BlockScalars ActualConsequences FiniteBlockModel
open WeightedBellScalar WeightedBlock
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The manuscript's qualitative channel dimensions and exact two-use lower
bound, now with every analytic existence premise discharged. -/
theorem exists_actual_channel_bounds_with_dimensions {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ (T : FiniteQuantumChannel) (N : ℕ), 0 < N ∧
      Fintype.card T.Input = 2 * N^n * K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.log2 K/(K : ℝ) ≤ T.chiTwo := by
  classical
  letI : NeZero K := ⟨by omega⟩
  let ε : ℝ := η * Real.log 2
  have hε : 0 < ε := mul_pos hη Scalar.log_two_pos
  obtain ⟨δ,hδ,_,hbudget⟩ := WeightedParameters.exists_collinsYoun_budget hK hn hε
  obtain ⟨s,hs,hsK,hscale⟩ := WeightedParameters.exists_small_perturbation hK n hδ
  let q := perturbedWeights hK s
  have hq (i : Fin K) : 0 ≤ q i := (perturbedWeights_positive hK hs.le hsK i).le
  have hsum : ∑ i, q i=1 := perturbedWeights_sum hK s
  let margin : ℝ := (n : ℝ)*(2*s^2*Real.log K)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hmargin : 0 < margin := mul_pos hnpos (perturbation_margin_pos hK hs)
  obtain ⟨τ,hτ,hstable⟩ := EntropyStability.exists_damped_bell_entropy_modulus
    (ο := ZMod (K^n)) margin hmargin
  obtain ⟨m,hm,horder⟩ := DampedRealization.exists_moment_order
    (ο := ZMod (K^n)) (amplification_gt_one (half_pos hε))
    (collinsYounConstant_pos hK hn) hτ
  let U := baseUnitary K (4*m)
  let B := blockChannel U n
  obtain ⟨F,G,hF,hres,hGF,hcert,hloss⟩ := horder _ _ B (by
    intro A _ ht hu
    exact block_adjoint_normalized_moment_le hK hn m A ht hu.le)
  let W := weightedBlock U q hq hsum n
  let D := DampedChannel.damped W F hF hres
  letI : DecidableEq ((ZMod (K^n) × ZMod (K^n)) ×
      (Bool × TensorChainIndex (LocalIndex K (4*m)) n)) := instDecidableEqProd
  let T := converted D
  have hweighted := WeightedCertificate.damped_weighted_certificate B (outputScale q n)
    (outputScale_isHermitian q n) (block_adjoint_outputScale_sq U q hq hsum n)
    F hF hres hδ.le hscale hcert
  rw [← weightedBlock_eq_weighted U q hq hsum n] at hweighted
  have hfinal : ∀ A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ,
      A.IsHermitian → A.trace=0 →
      ‖D.adjointMap A‖ ≤ amplification ε*collinsYounConstant K n*hsLength A := by
    intro A hA ht
    exact (hweighted A hA ht).trans
      (mul_le_mul_of_nonneg_right hbudget (hsLength_nonneg A))
  have hsingle : T.holevo ≤ (n : ℝ)*Real.log (1+9/(K : ℝ))+ε := by
    have h := converted_holevo_le_of_adjoint_certificate D
      (amplification_times_constant_pos (η := ε) hK hn).le hfinal
    simp only [Nat.cast_pow] at h
    exact h.trans (log_purity_factor_le_eta hK hε)
  have hb := weightedBlock_canonical_entropy_le U q hq hsum n
  have hsq : ∑ i, q i^2 = 1/(K : ℝ)+2*s^2 := perturbedWeights_sum_sq hK s
  rw [hsq] at hb
  have hd := hstable W F hF hres hloss
  have hjoint : ((D.tensor D.conjugate).output BellOutput.bellState).vonNeumann ≤
      (n : ℝ)*(2*Real.log K-Real.log K/(K : ℝ)) := by
    calc
      _ ≤ (DampedBellStability.pairedBellOutput W).vonNeumann + margin := hd
      _ ≤ (n : ℝ)*(2*Real.log K-(1/(K : ℝ)+2*s^2)*Real.log K)+margin :=
        add_le_add hb (le_refl margin)
      _ = _ := by dsimp only [margin]; ring
  have hpair := converted_tensor_holevo_lower D BellOutput.bellState
  have hlower : (n : ℝ)*Real.log K/(K : ℝ) ≤ (T.tensor T).holevo := by
    have hc := two_use_entropy_cancellation K n
    linarith
  have hpos : 0 < T.holevoBits := by
    apply WeightedPositivity.converted_damped_weightedBlock_holevoBits_pos
      U q hq hsum hn ⟨⟨0,by omega⟩,?_⟩ F G hF hres hGF
    change perturbedWeights hK s ⟨0,by omega⟩ ≠ _
    rw [perturbedWeights_zero_index]
    linarith
  refine ⟨FiniteQuantumChannel.ofKraus T, Fintype.card (LocalIndex K (4*m)),
    Fintype.card_pos, ?_, ?_, hpos, ?_, ?_⟩
  · exact Qualitative.constructed_input_dimension (LocalIndex K (4*m)) n
  · exact ZMod.card _
  · exact HolevoBits.natural_upper_to_bits n hsingle
  · exact HolevoBits.natural_lower_to_bits n hlower

theorem exists_actual_channel_bounds_positive {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.log2 K/(K : ℝ) ≤ T.chiTwo := by
  obtain ⟨T,_,_,_,_,h⟩ := exists_actual_channel_bounds_with_dimensions hK hn hη
  exact ⟨T,h⟩

/-- The exact qualitative additive lower bound for the same genuine channel. -/
theorem exists_actual_channel_gap {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.deltaK K-2*η ≤ T.gap := by
  obtain ⟨T,hp,hu,hl⟩ := exists_actual_channel_bounds_positive hK hn hη
  refine ⟨T,hp,hu,?_⟩
  exact Scalar.holevo_gap hu (by simpa only [mul_div_assoc] using hl)

end Nonadditivity.ExactQualitative
