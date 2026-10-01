/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.StructuredHaarModel
import Nonadditivity.StructuredFiniteChannel
import Nonadditivity.HaarConsequences

/-! # Explicit-dimension channels from the sole remaining Haar estimate

The hypothesis below is a literal expectation inequality for actual linear
matrix polynomials evaluated in independent Haar pairs. Every net, embedding,
coefficient budget, error transfer, probability-space construction, and channel
conversion is proved by the imported constructions.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.StructuredHaarConsequences
open MeasureTheory StructuredHaarModel StructuredLinearization PolynomialReduction
open Entropy Channels.KrausChannel BlockConstruction FreeModel
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology

/-- The manuscript's exact integer local dimension. -/
def localDimension (K n : ℕ) : ℕ := Quantitative.dimensionChoice (Real.log K) n

theorem localDimension_pos (K n : ℕ) : 0 < localDimension K n := by
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

/-- Convert to the canonical Haar model's `N+1` indexing convention. -/
def sampleSize (K n : ℕ) : ℕ := localDimension K n - 1

@[simp] theorem sampleSize_add_one (K n : ℕ) : sampleSize K n + 1 = localDimension K n :=
  Nat.sub_add_cancel (localDimension_pos K n)

/-- The remaining analytic assertion, specialized only to the manuscript's
explicit N and even moment choice. There is no coefficient-size restriction.
The expectation, representation and regular norm are literal mathematical objects. -/
def ExplicitHaarExpectation (K n : ℕ) : Prop :=
  ∀ H : Polynomial (StructuredLinearization.G n),
    (∀ w ∈ H.support, w=1 ∨ ∃ x : Fin n × Fin 2,
      w=ProductPolynomialReduction.generator x ∨ w=(ProductPolynomialReduction.generator x)⁻¹) →
    (∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
      (π : StructuredLinearization.G n →* unitary (Matrix ν ν ℂ)),
      (H.finiteEval π).IsHermitian) →
    (∫ ω : HaarModel.Sample 2 n (sampleSize K n),
      ‖H.finiteEval (sampleRepresentation n (sampleSize K n) ω)‖
        ∂HaarModel.sampleMeasure 2 n (sampleSize K n)) ≤
      ‖H.regularEval‖ * Real.exp (Quantitative.haarLogMultiplier (Real.log K) n
        (Real.log (2*(Fintype.card H.Index:ℝ))))

/-- The exact net amplification for mesh `1/n`. -/
def kappa (n : ℕ) : ℝ := ((n:ℝ)+1)/((n:ℝ)-1)

theorem kappa_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ kappa n := by
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold kappa
  exact (le_div_iff₀ (by linarith)).mpr (by linarith)

variable {K n : ℕ} [NeZero K]

/-- Full explicit-dimension realization. The only remaining hypothesis is
`ExplicitHaarExpectation`; all prior separate dimension/error budgets are gone. -/
theorem exists_explicit_certificate (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hHaar : ExplicitHaarExpectation K n) :
    ∃ ω : HaarModel.Sample 2 n (sampleSize K n),
      ∀ A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ, A.IsHermitian → A.trace=0 →
        ‖(blockChannel (derivedUnitary K n (sampleSize K n) hK ω) n).adjointMap A‖ ≤
          (kappa n*c K n)*AdjointPurity.hsLength A := by
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hnr : (1:ℝ) < n := by linarith
  obtain ⟨tests,hne,htnorm,htsymm,hnet,H,hlinear,hL,htransfer⟩ :=
    exists_net_linearization hK hn
  have hL0 : 0 ≤ Real.log (2*(Fintype.card H.Index:ℝ)) := by
    have hc : (1:ℝ) ≤ Fintype.card H.Index := by exact_mod_cast Fintype.card_pos (α := H.Index)
    exact Real.log_nonneg (by linarith)
  obtain ⟨_,_,_,hlog⟩ := Quantitative.quantitative_certificate hK hn hL0 hL
  have htol : 0 < Quantitative.tolerance (Real.log K) n := by
    unfold Quantitative.tolerance
    positivity
  have hm : Real.exp (Quantitative.haarLogMultiplier (Real.log K) n
      (Real.log (2*(Fintype.card H.Index:ℝ)))) ≤ 1+Quantitative.tolerance (Real.log K) n := by
    have hh := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log (by linarith : 0 < 1+Quantitative.tolerance (Real.log K) n/2)] at hh
    linarith
  obtain ⟨ω,hω⟩ := exists_le_integral (integrable_polynomial_norm n (sampleSize K n) H)
  have he := hHaar H hlinear (fun ν _ _ _ π => (htransfer ν π).1)
  have hcomparison : ‖H.finiteEval (sampleRepresentation n (sampleSize K n) ω)‖ ≤
      (1+Quantitative.tolerance (Real.log K) n)*‖H.regularEval‖ := by
    exact hω.trans (he.trans (by nlinarith [mul_le_mul_of_nonneg_left hm (norm_nonneg H.regularEval)]))
  have hp := (htransfer (TensorChainIndex (Fin (sampleSize K n+1)) n)
    (sampleRepresentation n (sampleSize K n) ω)).2 (by
      simpa only [Quantitative.tolerance] using hcomparison)
  have hcert := StructuredFiniteChannel.certificate_of_finitePaired_bound
    (derivedUnitary K n (sampleSize K n) hK ω)
    (fun b => sampleRepresentation n (sampleSize K n) ω
      (InitialNetReduction.shortProductEmbedding K n hK (branchWord b)))
    (sampleRepresentation_branchWord K n (sampleSize K n) hK ω) tests
    (1/(n:ℝ)) ((1+1/(n:ℝ))*c K n) (by positivity)
    ((div_lt_one (by linarith)).mpr hnr) (by unfold c; positivity) hnet hp
  have hκ : ((1+1/(n:ℝ))*c K n)/(1-1/(n:ℝ)) = kappa n*c K n := by
    unfold kappa
    field_simp
  exact ⟨ω,by simpa only [hκ] using hcert⟩

/-- The actual converted channel has exactly the claimed input dimension. -/
theorem explicit_input_dimension :
    Fintype.card ((ZMod (K^n) × ZMod (K^n)) ×
      (Bool × TensorChainIndex (Fin (sampleSize K n+1)) n)) =
        2 * (localDimension K n)^n * K^(2*n) := by
  rw [Conversion.converted_input_dimension,Entropy.tensorChainIndex_card]
  simp only [Fintype.card_fin,sampleSize_add_one,pow_mul,Nat.mul_comm 2 n]

/-- The full finite channel bounds at the exact explicit dimensions. -/
theorem exists_explicit_channel (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hHaar : ExplicitHaarExpectation K n) :
    ∃ ω : HaarModel.Sample 2 n (sampleSize K n),
      let T := Conversion.converted (blockChannel (derivedUnitary K n (sampleSize K n) hK ω) n)
      T.holevo ≤ (n:ℝ)*Real.log (1+9/(K:ℝ)) + 2*Real.log (kappa n) ∧
      (n:ℝ)*Real.log K/(K:ℝ) ≤ (T.tensor T).holevo ∧
      (n:ℝ)*BlockScalars.gapCoefficient K - 4*Real.log (kappa n) ≤
        (T.tensor T).holevo - 2*T.holevo := by
  obtain ⟨ω,hω⟩ := exists_explicit_certificate hK hn hHaar
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2:ℝ) ≤ n by linarith)
  have hκ := kappa_ge_one hn2
  have hbounds := block_converted_bounds_of_certificate
    (derivedUnitary K n (sampleSize K n) hK ω) n
    (show 0 ≤ kappa n*c K n by unfold c; positivity) hω
  have hscalar := BlockScalars.log_purity_factor_le (n := n) hK hκ
  change Real.log (1+(K:ℝ)^n*(kappa n*c K n)^2) ≤ _ at hscalar
  refine ⟨ω,?_,hbounds.2.1,?_⟩
  · exact hbounds.1.trans (by simpa only [Nat.cast_pow] using hscalar)
  · dsimp [BlockScalars.gapCoefficient]
    have hb := hbounds.2.2
    calc
      (n:ℝ)*(Real.log (K:ℝ)/(K:ℝ)-2*Real.log (1+9/(K:ℝ))) - 4*Real.log (kappa n) =
          (n:ℝ)*Real.log (K:ℝ)/(K:ℝ) -
            2*((n:ℝ)*Real.log (1+9/(K:ℝ)) + 2*Real.log (kappa n)) := by ring
      _ ≤ _ := by linarith


/-- Review-facing form: a genuine finite CPTP channel, the exact manuscript
input/output dimensions, strictly positive one-use Holevo information, and all
bounds in bits. Its sole nonnumeric premise is the literal Haar expectation. -/
theorem exists_explicit_finite_channel (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hHaar : ExplicitHaarExpectation K n) :
    ∃ T : ActualConsequences.FiniteQuantumChannel,
      Fintype.card T.Input = 2*(localDimension K n)^n*K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧
      T.chi ≤ (n:ℝ)*Scalar.aK K + 2*Scalar.log2 (kappa n) ∧
      (n:ℝ)*Scalar.log2 K/(K:ℝ) ≤ T.chiTwo ∧
      (n:ℝ)*Scalar.deltaK K - 4*Scalar.log2 (kappa n) ≤ T.gap := by
  obtain ⟨ω,hupper,hlower,_⟩ := exists_explicit_channel hK hn hHaar
  let U := derivedUnitary K n (sampleSize K n) hK ω
  let T := ActualConsequences.FiniteQuantumChannel.ofKraus (Conversion.converted (blockChannel U n))
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ n by linarith)
  have hp : 0 < T.chi := PositiveHolevo.block_converted_holevoBits_pos hK U hn1
  have he : (2*Scalar.log2 (kappa n))*Real.log 2 = 2*Real.log (kappa n) := by
    dsimp [Scalar.log2]
    field_simp
  have hu : T.chi ≤ (n:ℝ)*Scalar.aK K + 2*Scalar.log2 (kappa n) :=
    HolevoBits.natural_upper_to_bits n (by simpa only [he] using hupper)
  have hl : (n:ℝ)*Scalar.log2 K/(K:ℝ) ≤ T.chiTwo :=
    HolevoBits.natural_lower_to_bits n hlower
  refine ⟨T,explicit_input_dimension,ZMod.card _,hp,hu,hl,?_⟩
  unfold ActualConsequences.FiniteQuantumChannel.gap Scalar.deltaK
  rw [mul_sub,← mul_div_assoc]
  nlinarith only [hu,hl]

end Nonadditivity.StructuredHaarConsequences
