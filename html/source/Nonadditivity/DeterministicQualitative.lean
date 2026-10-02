/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DampedRealization
import Nonadditivity.FiniteBlockModel
import Nonadditivity.CanonicalBlockBell
import Nonadditivity.EntropyStability
import Nonadditivity.DampedPositivity
import Nonadditivity.ActualConsequences

/-! # Unconditional qualitative finite-channel realization

Finite quotients match the required free trace moments exactly. An invertible
input damping suppresses the exceptional spectral subspaces, and its normalized
trace loss controls the Bell entropy. Both Holevo errors may be made arbitrarily
small. No Haar convergence or quantitative random-matrix estimate is assumed.

The two-use lower bound includes a freely prescribed error. This does not assert
the manuscript's exact no-error lower bound or its sharp local matrix dimension.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Nonadditivity.DeterministicQualitative
open Entropy Channels Channels.KrausChannel AdjointPurity BlockConstruction
open Conversion BlockScalars ActualConsequences FiniteBlockModel
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- Actual finite CPTP channels with both qualitative estimates and the genuine
input/output dimensions. The local dimension is finite but is not sharply bounded. -/
theorem exists_actual_channel_bounds_with_dimensions {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ (T : FiniteQuantumChannel) (N : ℕ), 0 < N ∧
      Fintype.card T.Input = 2 * N^n * K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.log2 K/(K : ℝ)-η ≤ T.chiTwo := by
  classical
  letI : NeZero K := ⟨by omega⟩
  let ε : ℝ := η * Real.log 2
  have hε : 0 < ε := mul_pos hη Scalar.log_two_pos
  obtain ⟨δ,hδ,hstable⟩ := EntropyStability.exists_damped_bell_entropy_modulus
    (ο := ZMod (K^n)) ε hε
  obtain ⟨p,hp,horder⟩ := DampedRealization.exists_moment_order
    (ο := ZMod (K^n)) (amplification_gt_one hε) (collinsYounConstant_pos hK hn) hδ
  let U := baseUnitary K (4*p)
  let B := blockChannel U n
  obtain ⟨F,G,hF,hres,hGF,hcert,hloss⟩ := horder _ _ B (by
    intro A _ ht hu
    exact block_adjoint_normalized_moment_le hK hn p A ht hu.le)
  let D := DampedChannel.damped B F hF hres
  letI : DecidableEq ((ZMod (K^n) × ZMod (K^n)) ×
      (Bool × TensorChainIndex (LocalIndex K (4*p)) n)) := instDecidableEqProd
  let T := converted D
  have hsingle : T.holevo ≤ (n : ℝ)*Real.log (1+9/(K : ℝ))+ε := by
    have h := converted_holevo_le_of_adjoint_certificate D
      (amplification_times_constant_pos (η := ε) hK hn).le hcert
    simp only [Nat.cast_pow] at h
    exact h.trans (log_purity_factor_le_eta hK hε)
  have hb := CanonicalBlockBell.block_channel_canonical_entropy_le U n
  have hd := hstable B F hF hres hloss
  have hjoint : ((D.tensor D.conjugate).output BellOutput.bellState).vonNeumann ≤
      (n : ℝ)*(2*Real.log K-Real.log K/(K : ℝ))+ε := by
    exact hd.trans (add_le_add hb (le_refl ε))
  have hpair := converted_tensor_holevo_lower D BellOutput.bellState
  have hlower : (n : ℝ)*Real.log K/(K : ℝ)-ε ≤ (T.tensor T).holevo := by
    have hc := two_use_entropy_cancellation K n
    linarith
  have hpos : 0 < T.holevoBits := DampedPositivity.converted_damped_block_holevoBits_pos
    hK U hn F G hF hres hGF
  refine ⟨FiniteQuantumChannel.ofKraus T, Fintype.card (LocalIndex K (4*p)),
    Fintype.card_pos, ?_, ?_, hpos, ?_, ?_⟩
  · exact Qualitative.constructed_input_dimension (LocalIndex K (4*p)) n
  · exact ZMod.card _
  · exact HolevoBits.natural_upper_to_bits n hsingle
  · have h := div_le_div_of_nonneg_right hlower Scalar.log_two_pos.le
    change (n : ℝ)*Scalar.log2 K/(K : ℝ)-η ≤ (T.tensor T).holevo / Real.log 2
    convert h using 1
    dsimp [Scalar.log2, ε]
    field_simp

/-- Unconditional channel bounds in bits. In particular, no analytic input
structure, convergence premise, or assumed channel certificate occurs here. -/
theorem exists_actual_channel_bounds_positive {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.log2 K/(K : ℝ)-η ≤ T.chiTwo := by
  obtain ⟨T,_,_,_,_,h⟩ := exists_actual_channel_bounds_with_dimensions hK hn hη
  exact ⟨T,h⟩

end Nonadditivity.DeterministicQualitative
