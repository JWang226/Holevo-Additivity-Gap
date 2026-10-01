/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarRefinedCoefficientBound
import Nonadditivity.HaarPathClassAssembly
import Nonadditivity.HaarPrescribedDimension

/-! # The unconditional prescribed-dimension Haar and channel bounds

Actual Haar integration, refined path classes, operator coefficient sums,
finite scalar majorants, and tensor replacement are joined here. No random
matrix, path-counting, or coefficient estimate remains an input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Nonadditivity.HaarPrescribedDimension
open HaarOperatorPathBridge HaarOperatorCurry HaarOnePairAssembly
  HaarWordExpansion HaarIteratedMoments StructuredHaarConsequences
open scoped Matrix Matrix.Norms.L2Operator

/-- The literal mixed moment contributions satisfy the tracked length budget. -/
theorem onePairLengthBounds {N p : ℕ} (hp : 2≤p)
    (hN : 2^80*(p:ℝ)^80≤N+1) : OnePairLengthBounds N p := by
  classical
  intro j ι _ _ _ f _ hlinear t ht
  have ht0 : 0<t := (Finset.mem_Icc.mp ht).1
  have htp : t≤p := (Finset.mem_Icc.mp ht).2
  have hA := operatorCurry_linear f (fun w hw => (hlinear w hw).1)
  have hb : ∀ P : HaarPathGraph.Path (Fin (N+1)) 2 t, pathWeight P≠0 →
      ‖refinedCoefficientSum (operatorCurry f) p P‖ ≤ (N+1:ℝ)^P.vertices.card *
        (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
          (p:ℝ)^(9*P.defectTwice+11)*‖regularEval f‖^p) := by
    intro P _
    have h := coefficient_bound (operatorCurry f) hA p (by omega) P ht0
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,operatorCurry_norm,mul_assoc] using h
  have h := norm_pathOperatorSum_le_of_coefficient_bound hp ht0 htp hN
    (operatorCurry f) (pow_nonneg (norm_nonneg (regularEval f)) p) hb
  exact mixedLengthContribution_le_of_pathSum N p t ht0 f h

/-- The full one-pair trace comparison in the manuscript's growing moment range. -/
theorem onePairTraceBound {N p : ℕ} (hp : 2≤p)
    (hN : 2^80*(p:ℝ)^80≤N+1) : OnePairTraceBound N p :=
  onePairTraceBound_of_lengthBounds hp hN (onePairLengthBounds hp hN)

/-- The exact canonical Haar expectation needed by the channel construction. -/
theorem explicitHaarExpectation {K n : ℕ} (hK : 2≤K) (hn : Quantitative.n₀ K≤n) :
    ExplicitHaarExpectation K n := by
  have hKreal : (2:ℝ)≤K := by exact_mod_cast hK
  have hlogK := Real.log_le_log (by norm_num : (0:ℝ)<2) hKreal
  have hh : (2:ℝ)/3≤Real.log (K:ℝ) := by linarith [Real.log_two_gt_d9]
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn2 : (2:ℝ)≤n := by linarith
  have hp := (Quantitative.moment_parameter_bounds hh hn2).2.1
  have hD := HaarMomentConstants.prescribed_dimension_strong hh hn2
  have he : sampleSize K n+1=Quantitative.dimensionChoice (Real.log K) n :=
    sampleSize_add_one K n
  rw [←he,Nat.cast_add,Nat.cast_one] at hD
  exact explicitHaarExpectation_of_onePairTraceBound hK hn (onePairTraceBound hp hD)

/-- A genuine finite CPTP channel with the manuscript's prescribed dimensions
and the supplementary single-use lower bound, on the same channel witness. -/
theorem exists_prescribed_channel_with_lower_bound {K n : ℕ}
    (hK : 2≤K) (hn : Quantitative.n₀ K≤n) :
    ∃ T : ActualConsequences.FiniteQuantumChannel,
      Fintype.card T.Input = 2*(localDimension K n)^n*K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧
      2*(n:ℝ)/(K:ℝ) ≤ T.chi ∧
      T.chi ≤ (n:ℝ)*Scalar.aK K+2*Scalar.log2 (kappa n) ∧
      (n:ℝ)*Scalar.log2 K/(K:ℝ)≤T.chiTwo ∧
      (n:ℝ)*Scalar.deltaK K-4*Scalar.log2 (kappa n)≤T.gap := by
  letI : NeZero K := ⟨by omega⟩
  obtain ⟨ω,hupper,hlower,_⟩ := exists_explicit_channel hK hn
    (explicitHaarExpectation hK hn)
  let U := StructuredHaarModel.derivedUnitary K n (sampleSize K n) hK ω
  let T := ActualConsequences.FiniteQuantumChannel.ofKraus
    (Conversion.converted (BlockConstruction.blockChannel U n))
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ n by linarith)
  have hp : 0 < T.chi := PositiveHolevo.block_converted_holevoBits_pos hK U hn1
  have hs : 2*(n:ℝ)/(K:ℝ) ≤ T.chi :=
    PositiveHolevo.block_converted_holevoBits_lower hK U n
  have he : (2*Scalar.log2 (kappa n))*Real.log 2 = 2*Real.log (kappa n) := by
    dsimp [Scalar.log2]
    field_simp
  have hu : T.chi ≤ (n:ℝ)*Scalar.aK K+2*Scalar.log2 (kappa n) :=
    HolevoBits.natural_upper_to_bits n (by simpa only [he] using hupper)
  have hl : (n:ℝ)*Scalar.log2 K/(K:ℝ) ≤ T.chiTwo :=
    HolevoBits.natural_lower_to_bits n hlower
  refine ⟨T,explicit_input_dimension,ZMod.card _,hp,hs,hu,hl,?_⟩
  unfold ActualConsequences.FiniteQuantumChannel.gap Scalar.deltaK
  rw [mul_sub,←mul_div_assoc]
  nlinarith only [hu,hl]

/-- A genuine finite CPTP channel with the manuscript's prescribed dimensions
and its one-use, two-use, and additive-gap bounds, all in bits. -/
theorem exists_prescribed_channel {K n : ℕ} (hK : 2≤K) (hn : Quantitative.n₀ K≤n) :
    ∃ T : ActualConsequences.FiniteQuantumChannel,
      Fintype.card T.Input = 2*(localDimension K n)^n*K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧
      T.chi ≤ (n:ℝ)*Scalar.aK K+2*Scalar.log2 (kappa n) ∧
      (n:ℝ)*Scalar.log2 K/(K:ℝ)≤T.chiTwo ∧
      (n:ℝ)*Scalar.deltaK K-4*Scalar.log2 (kappa n)≤T.gap := by
  obtain ⟨T,hinput,houtput,hpos,_,hupper,hlower,hgap⟩ :=
    exists_prescribed_channel_with_lower_bound hK hn
  exact ⟨T,hinput,houtput,hpos,hupper,hlower,hgap⟩

end Nonadditivity.HaarPrescribedDimension
