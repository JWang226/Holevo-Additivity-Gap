/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.InitialNetReduction
import Nonadditivity.StructuredReductionCosts

/-! # Actual structured linearization

The tensor-coordinate partitions and one-factor word balls are applied to the
same polynomial and coefficients, followed by the norm-preserving Hermitian
dilation.  Every intermediate polynomial is explicitly constructed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
namespace Nonadditivity.StructuredLinearization
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open PolynomialReduction

variable {n K : ℕ} [NeZero K]
abbrev G (n : ℕ) := Fin n → FreeGroup (Fin 2)

def tensor (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n)) :
    Polynomial (G n) := TensorPartitionReduction.reduce v P (Nat.clog 2 n)

def linear (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n)) (ell : ℕ) :
    Polynomial (G n) := WordBallReduction.stage (tensor v P) ell (Nat.clog 2 ell)

def final (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n)) (ell : ℕ) :
    Polynomial (G n) := (linear v P ell).dilate

def dimensionMultiplier (v : Fin n → Fin K → FreeGroup (Fin 2)) (ell : ℕ) : ℕ :=
  TensorPartitionReduction.dimensionCost v (Nat.clog 2 n) *
    WordBallReduction.dimensionCost n ell (Nat.clog 2 ell)

def errorMultiplier (v : Fin n → Fin K → FreeGroup (Fin 2)) (ell : ℕ) : ℕ :=
  TensorPartitionReduction.errorCost v (Nat.clog 2 n) *
    WordBallReduction.errorCost n ell (Nat.clog 2 ell)

theorem dimensionMultiplier_pos (v : Fin n → Fin K → FreeGroup (Fin 2)) (ell : ℕ) :
    0 < dimensionMultiplier v ell :=
  Nat.mul_pos (TensorPartitionReduction.dimensionCost_pos _ _)
    (WordBallReduction.dimensionCost_pos _ _ _)

theorem errorMultiplier_pos (v : Fin n → Fin K → FreeGroup (Fin 2)) (ell : ℕ) :
    0 < errorMultiplier v ell :=
  Nat.mul_pos (TensorPartitionReduction.errorCost_pos _ _)
    (WordBallReduction.errorCost_pos _ _ _)

theorem errorMultiplier_eq (v : Fin n → Fin K → FreeGroup (Fin 2)) (ell : ℕ) :
    errorMultiplier v ell = 3^(Nat.clog 2 n + Nat.clog 2 ell)*dimensionMultiplier v ell := by
  simp only [errorMultiplier,dimensionMultiplier,TensorPartitionReduction.errorCost_eq,
    WordBallReduction.errorCost_eq,pow_add]
  ring

theorem tensor_bound (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n))
    (hP : P.support ⊆ TensorPartitionReduction.stageSupport v 0)
    (ell : ℕ) (hn : 1 ≤ n) (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ell) :
    ∀ w ∈ (tensor v P).support, WordBallReduction.SingleFactorBound ell w := by
  intro w hw
  exact TensorPartitionReduction.stageSupport_single_factor v _ ell hn
    (Nat.le_pow_clog (by omega) n) hv w
    (TensorPartitionReduction.reduce_support v P hP _ hw)

theorem linear_letters (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n))
    (hP : P.support ⊆ TensorPartitionReduction.stageSupport v 0)
    (ell : ℕ) (hn : 1 ≤ n) (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ell) :
    ∀ w ∈ (linear v P ell).support, w=1 ∨ ∃ x : Fin n × Fin 2,
      w=ProductPolynomialReduction.generator x ∨ w=(ProductPolynomialReduction.generator x)⁻¹ :=
  WordBallReduction.stage_clog_linear (tensor v P) ell hn (tensor_bound v P hP ell hn hv)

theorem final_letters (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n))
    (hP : P.support ⊆ TensorPartitionReduction.stageSupport v 0)
    (ell : ℕ) (hn : 1 ≤ n) (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ell) :
    ∀ w ∈ (final v P ell).support, w=1 ∨ ∃ x : Fin n × Fin 2,
      w=ProductPolynomialReduction.generator x ∨ w=(ProductPolynomialReduction.generator x)⁻¹ := by
  intro w hw
  change w ∈ (linear v P ell).support ∪ (linear v P ell).support.image Inv.inv at hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact linear_letters v P hP ell hn hv w hw
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    rcases linear_letters v P hP ell hn hv u hu with rfl | ⟨x,rfl | rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inr ⟨x,Or.inr rfl⟩
    · exact Or.inr ⟨x,Or.inl (by simp)⟩

theorem final_dimension (v : Fin n → Fin K → FreeGroup (Fin 2))
    (P : Polynomial (G n)) (ell : ℕ) :
    Fintype.card (final v P ell).Index = 2*Fintype.card P.Index*dimensionMultiplier v ell := by
  simp only [final,linear,tensor,Polynomial.dilate_dimension,WordBallReduction.stage_dimension,
    TensorPartitionReduction.reduce_dimension,dimensionMultiplier]
  ring

theorem final_isHermitian (v : Fin n → Fin K → FreeGroup (Fin 2))
    (P : Polynomial (G n)) (ell : ℕ)
    {ν : Type*} [Fintype ν] [DecidableEq ν]
    (π : G n →* unitary (Matrix ν ν ℂ)) : ((final v P ell).finiteEval π).IsHermitian :=
  Polynomial.dilate_finite_isHermitian _ π

/-- Transfer through the two concrete stage families and the final dilation. -/
theorem final_error_transfer (v : Fin n → Fin K → FreeGroup (Fin 2)) (P : Polynomial (G n))
    (hP : P.support ⊆ TensorPartitionReduction.stageSupport v 0)
    (ell : ℕ) (hn : 1 ≤ n) (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ell)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G n →* unitary (Matrix ν ν ℂ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : ‖(final v P ell).finiteEval π‖ ≤
      (1+ε/(errorMultiplier v ell:ℝ))*‖(final v P ell).regularEval‖) :
    ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  have hE : (0:ℝ) < TensorPartitionReduction.errorCost v (Nat.clog 2 n) := by
    exact_mod_cast TensorPartitionReduction.errorCost_pos v (Nat.clog 2 n)
  have hE1 : (1:ℝ) ≤ TensorPartitionReduction.errorCost v (Nat.clog 2 n) := by
    exact_mod_cast TensorPartitionReduction.errorCost_pos v (Nat.clog 2 n)
  have hδ0 : 0 ≤ ε/(TensorPartitionReduction.errorCost v (Nat.clog 2 n):ℝ) :=
    div_nonneg hε hE.le
  have hδ1 : ε/(TensorPartitionReduction.errorCost v (Nat.clog 2 n):ℝ) ≤ 1 :=
    (div_le_iff₀ hE).mpr (by linarith)
  apply TensorPartitionReduction.reduce_error_transfer v P hP _ π ε hε hε1
  apply WordBallReduction.stage_error_transfer (tensor v P) ell _ hn
    (tensor_bound v P hP ell hn hv) π _ hδ0 hδ1
  simpa only [final,Polynomial.dilate_finite_norm,Polynomial.dilate_regular_norm,
    errorMultiplier,Nat.cast_mul,div_div,linear] using hfinal


section Initial
open FreeModel StructuredCostBounds
variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

def individualWord (v : Fin n → Fin K → FreeGroup (Fin 2)) (a : Branch K n) : G n :=
  fun i => v i (a i)

def initialPolynomial (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n) : Polynomial (G n) :=
  InitialNetReduction.polynomial (individualWord v) A b₀

def testFinal (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n) (ell : ℕ) :
    Polynomial (G n) := final v (initialPolynomial v A b₀) ell

def referenceNorm (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) : ℝ :=
  ‖InitialNetReduction.regularPaired (individualWord v) A‖

def fullError (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (ell : ℕ) : ℝ :=
  3*(1+1/referenceNorm v A)*(errorMultiplier v ell:ℝ)

theorem initialPolynomial_support (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n) :
    (initialPolynomial v A b₀).support ⊆ TensorPartitionReduction.stageSupport v 0 :=
  TensorPartitionReduction.initial_support_subset v

theorem testFinal_dimension (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n) (ell : ℕ) :
    Fintype.card (testFinal v A b₀ ell).Index =
      2 * Fintype.card J * K^n * dimensionMultiplier v ell := by
  rw [testFinal,final_dimension]
  simp only [initialPolynomial,InitialNetReduction.polynomial_dimension,
    Branch,Fintype.card_fun,Fintype.card_fin]
  ring

theorem fullError_pos (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (ell : ℕ)
    (hρ : 0 < referenceNorm v A) : 0 < fullError v A ell := by
  have he : (0:ℝ) < errorMultiplier v ell := by exact_mod_cast errorMultiplier_pos v ell
  unfold fullError
  positivity

/-- Complete error transfer through the initial, undoubled Gram construction,
all balanced tensor splits, all one-factor word cuts, and the final dilation. -/
theorem testFinal_error_transfer (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n)
    (hA : ∀ j, (A j).IsHermitian) (hAn : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j)
    (ell : ℕ) (hn : 1 ≤ n) (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ell)
    (hρ : 0 < referenceNorm v A)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G n →* unitary (Matrix ν ν ℂ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : ‖(testFinal v A b₀ ell).finiteEval π‖ ≤
      (1+ε/fullError v A ell)*‖(testFinal v A b₀ ell).regularEval‖) :
    ‖InitialNetReduction.finitePaired (fun b => π (individualWord v b)) A‖ ≤
      (1+ε)*referenceNorm v A := by
  let F := 3*(1+1/referenceNorm v A)
  have hF : 0 < F := by dsimp [F]; positivity
  have hF1 : 1 ≤ F := by dsimp [F]; have := one_div_nonneg.mpr hρ.le; linarith
  have hδ0 : 0 ≤ ε/F := div_nonneg hε hF.le
  have hδ1 : ε/F ≤ 1 := (div_le_iff₀ hF).mpr (by linarith)
  have hQ := final_error_transfer v (initialPolynomial v A b₀)
    (initialPolynomial_support v A b₀) ell hn hv π (ε/F) hδ0 hδ1 (by
      simpa only [testFinal,fullError,F,div_div] using hfinal)
  have ht := InitialNetReduction.initial_relative_transfer (individualWord v) A hA hAn
    e he b₀ π (ε/F) (referenceNorm v A) hδ0 hδ1 hρ (le_refl _) hQ
  have hc : 3*(1+1/referenceNorm v A)*(ε/F) = ε := mul_div_cancel₀ ε hF.ne'
  simpa only [hc] using ht

/-- The actual complete error multiplier meets the manuscript's exponential
budget, with every intermediate cardinality and logarithmic estimate proved. -/
theorem fullError_bound (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ)
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hρ : Real.sqrt 2*(K:ℝ)^(-((n:ℝ)+1)/2) ≤ referenceNorm v A) :
    fullError v A (wordLength K) ≤ Real.exp (Quantitative.gamma (Real.log K)*n) := by
  simpa only [fullError,errorMultiplier,Nat.cast_mul,one_div,tensorSteps,wordSteps]
    using StructuredReductionCosts.actual_error_bound v hK hn hρ

/-- The actual coefficient size, including the final Hermitian doubling, meets
`log(2m) ≤ 2 K^(2n) log(1+2n)`. -/
theorem testFinal_log_dimension (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n)
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hJ : Fintype.card J ≤ netCardBound K n) :
    Real.log (2*(Fintype.card (testFinal v A b₀ (wordLength K)).Index:ℝ)) ≤
      2*(K:ℝ)^(2*n)*Real.log (1+2*(n:ℝ)) := by
  have hd : Fintype.card (initialPolynomial v A b₀).Index ≤ netCardBound K n*K^n := by
    simp only [initialPolynomial,InitialNetReduction.polynomial_dimension,
      Branch,Fintype.card_fun,Fintype.card_fin]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (K^n) hJ
  have hs := StructuredReductionCosts.actual_coefficient_bound v hK hn hd
    (Fintype.card_pos (α := (initialPolynomial v A b₀).Index))
  rw [testFinal,final_dimension]
  simpa only [dimensionMultiplier,tensorSteps,wordSteps,Nat.cast_mul,Nat.cast_ofNat,
    mul_assoc] using hs

/-- The manuscript's chosen small final error suffices at every finite unitary
representation.  This theorem is entirely deterministic. -/
theorem testFinal_error_transfer_exp (v : Fin n → Fin K → FreeGroup (Fin 2))
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (b₀ : Branch K n)
    (hA : ∀ j, (A j).IsHermitian) (hAn : ∀ j, ‖A j‖ ≤ 1)
    (e : J ≃ J) (he : ∀ j, A (e j) = -A j)
    (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n)
    (hv : ∀ i a, FreeGroup.norm (v i a) ≤ wordLength K)
    (hρ : Real.sqrt 2*(K:ℝ)^(-((n:ℝ)+1)/2) ≤ referenceNorm v A)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G n →* unitary (Matrix ν ν ℂ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : ‖(testFinal v A b₀ (wordLength K)).finiteEval π‖ ≤
      (1+ε*Real.exp (-(Quantitative.gamma (Real.log K)*n)))*
        ‖(testFinal v A b₀ (wordLength K)).regularEval‖) :
    ‖InitialNetReduction.finitePaired (fun b => π (individualWord v b)) A‖ ≤
      (1+ε)*referenceNorm v A := by
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hρpos : 0 < referenceNorm v A := lt_of_lt_of_le (by positivity) hρ
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ n by linarith)
  apply testFinal_error_transfer v A b₀ hA hAn e he _ hn1 hv hρpos π ε hε hε1
  apply hfinal.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply add_le_add le_rfl
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hε (fullError_pos v A _ hρpos)
    (fullError_bound v A hK hn hρ)

end Initial

section ActualNet
open FreeModel FiniteRealization StructuredCostBounds
local instance (tests : Finset (ObservableSpace (Branch K n))) : DecidableEq tests := Classical.decEq _

/-- Steps 1--3 of the explicit-dimension argument on the actual prescribed net:
an actual self-adjoint linear polynomial with the exact manuscript coefficient
budget and the prescribed exponential error transfer.  This result has only
numeric hypotheses.  The finite-Haar comparison in Step 4 is not asserted here. -/
theorem exists_net_linearization (hK : 2 ≤ K) (hn : Quantitative.n₀ K ≤ n) :
    ∃ tests : Finset (ObservableSpace (Branch K n)), tests.Nonempty ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      UnitSphereNet tests (1/(n:ℝ)) ∧
      ∃ H : Polynomial (G n),
        (∀ w ∈ H.support, w=1 ∨ ∃ x : Fin n × Fin 2,
          w=ProductPolynomialReduction.generator x ∨ w=(ProductPolynomialReduction.generator x)⁻¹) ∧
        Real.log (2*(Fintype.card H.Index:ℝ)) ≤
          2*(K:ℝ)^(2*n)*Real.log (1+2*(n:ℝ)) ∧
        ∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
          (π : G n →* unitary (Matrix ν ν ℂ)),
          (H.finiteEval π).IsHermitian ∧
          (‖H.finiteEval π‖ ≤
            (1+Real.exp (-(Quantitative.gamma (Real.log K)*n))/(n:ℝ))*‖H.regularEval‖ →
            ‖InitialNetReduction.finitePaired
              (fun b => π (InitialNetReduction.shortProductEmbedding K n hK (branchWord b)))
              (fun j : tests => observableMatrix j.val)‖ ≤ (1+1/(n:ℝ))*c K n) := by
  classical
  obtain ⟨_,hn64,_,_⟩ := Quantitative.threshold_consequences hK hn
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ n by linarith)
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨tests,hne,hnorm,hsymm,hnet,hcard,hlower,hupper⟩ :=
    NetPolynomial.exists_net_polynomial hK hn1
  letI : Nonempty tests := hne.to_subtype
  let v : Fin n → Fin K → FreeGroup (Fin 2) := fun _ => InitialNetReduction.shortWord K hK
  let A : tests → Matrix (Branch K n) (Branch K n) ℂ := fun j => observableMatrix j.val
  let b₀ : Branch K n := fun _ => 0
  have hA : ∀ j, (A j).IsHermitian := fun j => observableMatrix_isHermitian j.val
  have hAn : ∀ j, ‖A j‖ ≤ 1 := by
    intro j
    have hh : AdjointPurity.hsLength (A j) = 1 := by
      rw [← observable_norm_eq_hsLength]
      exact hnorm j.val j.property
    exact (InitialNetReduction.norm_le_hsLength (A j) (hA j)).trans hh.le
  let e := NetPolynomial.netNegationEquiv tests hsymm
  have he : ∀ j, A (e j) = -A j := fun _ => rfl
  have hv : ∀ i a, FreeGroup.norm (v i a) ≤ wordLength K := by
    intro i a
    simpa only [v,wordLength,Nat.log2_eq_log_two] using
      InitialNetReduction.shortWord_norm_le K hK a
  have href : referenceNorm v A = ‖NetPolynomial.netRegularPolynomial tests‖ := by
    change ‖InitialNetReduction.regularPaired
      (fun b => InitialNetReduction.shortProductEmbedding K n hK (branchWord b)) A‖ = _
    rw [InitialNetReduction.regularPaired_injective_norm_eq
      (InitialNetReduction.shortProductEmbedding K n hK)
      (InitialNetReduction.shortProductEmbedding_injective K n hK),
      InitialNetReduction.net_regularPaired_eq]
  have hρ : Real.sqrt 2*(K:ℝ)^(-((n:ℝ)+1)/2) ≤ referenceNorm v A := by rwa [href]
  have hJ : Fintype.card tests ≤ netCardBound K n := by
    simp only [Fintype.card_coe]
    change tests.card ≤ (1+2*n)^(K^(2*n)-1)
    exact_mod_cast hcard
  let H := testFinal v A b₀ (wordLength K)
  refine ⟨tests,hne,hnorm,hsymm,hnet,H,?_,?_,?_⟩
  · exact final_letters v (initialPolynomial v A b₀) (initialPolynomial_support v A b₀)
      _ hn1 hv
  · exact testFinal_log_dimension v A b₀ hK hn hJ
  · intro ν _ _ _ π
    refine ⟨final_isHermitian v (initialPolynomial v A b₀) _ π,?_⟩
    intro hH
    have ht := testFinal_error_transfer_exp v A b₀ hA hAn e he hK hn hv hρ π
      (1/(n:ℝ)) (by positivity) (by apply (div_le_iff₀ (by linarith)).mpr; linarith) (by
        simpa only [H,one_div,div_eq_mul_inv,mul_comm,mul_one] using hH)
    rw [href] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hupper (by positivity))

end ActualNet
end Nonadditivity.StructuredLinearization
