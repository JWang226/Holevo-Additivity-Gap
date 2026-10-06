/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.CanonicalBlockBell
import Nonadditivity.WeightedCertificate
import Mathlib.Topology.Instances.Matrix

/-! # Weighted block channels and their exact output scaling

Changing the local random-unitary probabilities changes each complementary
output by a diagonal scaling. The full tensor block has the corresponding
product scaling, independent of its input dimension.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
namespace Nonadditivity.WeightedBlock
open Entropy Channels Channels.KrausChannel BlockConstruction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker Topology

variable {K : ℕ} [NeZero K]

/-- Product of the local output scaling coefficients, in the actual tensor basis. -/
def chainScale (p : Fin K → ℝ) : (n : ℕ) → TensorChainIndex (Fin K) n → ℝ
  | 0, _ => 1
  | n+1, a => chainScale p n a.1 * Real.sqrt ((K:ℝ)*p a.2)

/-- The scaling matrix in the standardized output basis. -/
def outputScale (p : Fin K → ℝ) (n : ℕ) : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ :=
  Matrix.diagonal (fun a => (chainScale p n ((blockOutputEquiv K n).symm a):ℂ))

theorem outputScale_isHermitian (p : Fin K → ℝ) (n : ℕ) :
    (outputScale p n).IsHermitian := by
  change (Matrix.diagonal _).conjTranspose = _
  simp [outputScale]

theorem scale_mul_uniform (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (a : Fin K) :
    Real.sqrt ((K:ℝ)*p a)*Real.sqrt (1/(K:ℝ)) = Real.sqrt (p a) := by
  rw [←Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) (hp a))]
  congr 1
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  field_simp

theorem chainScale_uniform (n : ℕ) (a : TensorChainIndex (Fin K) n) :
    chainScale (fun _ => 1/(K:ℝ)) n a = 1 := by
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chainScale,ih]
    simp [hK]

theorem outputScale_uniform (n : ℕ) : outputScale (K := K) (fun _ => 1/(K:ℝ)) n = 1 := by
  unfold outputScale
  simp only [chainScale_uniform]
  simp

/-- Continuity requires no positivity restriction on the parameterized weights. -/
theorem continuous_chainScale (p : ℝ → Fin K → ℝ) (hp : ∀a, Continuous (fun t => p t a))
    (n : ℕ) (a : TensorChainIndex (Fin K) n) :
    Continuous (fun t => chainScale (p t) n a) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (ih a.1).mul ((continuous_const.mul (hp a.2)).sqrt)

/-- The scaling is continuous in the finite-dimensional operator norm. -/
theorem continuous_outputScale (p : ℝ → Fin K → ℝ) (hp : ∀a, Continuous (fun t => p t a))
    (n : ℕ) : Continuous (fun t => outputScale (p t) n) := by
  apply continuous_matrix
  intro a b
  by_cases hab : a=b
  · subst b
    simpa [outputScale,Matrix.diagonal_apply] using
      Complex.continuous_ofReal.comp (continuous_chainScale p hp n ((blockOutputEquiv K n).symm a))
  · simpa [outputScale,Matrix.diagonal_apply,hab] using
      (continuous_const : Continuous (fun _ : ℝ => (0:ℂ)))

theorem outputScale_norm_sub_one_tendsto (p : ℝ → Fin K → ℝ)
    (hp : ∀a, Continuous (fun t => p t a)) (hp0 : p 0 = fun _ => 1/(K:ℝ)) (n : ℕ) :
    Filter.Tendsto (fun t => ‖outputScale (p t) n-1‖) (nhds 0) (nhds 0) := by
  have hc : ContinuousAt (fun t => ‖outputScale (p t) n-1‖) 0 :=
    ((continuous_outputScale p hp n).sub continuous_const).norm.continuousAt
  simpa only [hp0,outputScale_uniform,sub_self,norm_zero] using hc.tendsto

section Channel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual tensor block of the weighted complementary channels. -/
def weightedComplementary (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ) :
    KrausChannel (TensorChainIndex ι n) (TensorChainIndex (Fin K) n) (TensorChainIndex ι n) :=
  tensorChain (fun j => (randomUnitary p hp hsum (U j)).complementary) n

/-- The genuine weighted block in the manuscript's standard output basis. -/
def weightedBlock (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ) :
    KrausChannel (TensorChainIndex ι n) (ZMod (K^n)) (TensorChainIndex ι n) :=
  (weightedComplementary U p hp hsum n).reindex (Equiv.refl _) (blockOutputEquiv K n)

theorem weightedComplementary_kraus_entry (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ)
    (k b : TensorChainIndex ι n) (a : TensorChainIndex (Fin K) n) :
    (weightedComplementary U p hp hsum n).kraus k a b =
      (chainScale p n a:ℂ)*(BlockBell.blockComplementary U n).kraus k a b := by
  induction n with
  | zero => simp [weightedComplementary,BlockBell.blockComplementary,tensorChain,
      emptyTensorChannel,chainScale]
  | succ n ih =>
    rcases k with ⟨k₀,k₁⟩
    rcases b with ⟨b₀,b₁⟩
    rcases a with ⟨a₀,a₁⟩
    change (weightedComplementary U p hp hsum n).kraus k₀ a₀ b₀ *
        ((randomUnitary p hp hsum (U n)).complementary).kraus k₁ a₁ b₁ =
      (chainScale p (n+1) (a₀,a₁):ℂ) *
        ((BlockBell.blockComplementary U n).kraus k₀ a₀ b₀ *
          ((uniformUnitary (U n)).complementary).kraus k₁ a₁ b₁)
    simp only [complementary,randomUnitary,uniformUnitary,Matrix.smul_apply,smul_eq_mul,
      Fintype.card_fin]
    rw [ih]
    have hs : (Real.sqrt (p a₁):ℂ) =
        (Real.sqrt ((K:ℝ)*p a₁):ℂ)*(Real.sqrt (1/(K:ℝ)):ℂ) := by
      rw [←Complex.ofReal_mul,scale_mul_uniform p hp a₁]
    rw [hs]
    simp only [chainScale,Complex.ofReal_mul]
    ring

/-- The exact Kraus scaling, including standard output-basis transport. -/
theorem weightedBlock_kraus (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ)
    (k : TensorChainIndex ι n) :
    (weightedBlock U p hp hsum n).kraus k = outputScale p n*(blockChannel U n).kraus k := by
  ext a b
  simp only [weightedBlock,blockChannel,reindex,Matrix.submatrix_apply,Equiv.refl_symm,
    Equiv.refl_apply,outputScale,Matrix.diagonal_mul]
  exact weightedComplementary_kraus_entry U p hp hsum n k b ((blockOutputEquiv K n).symm a)

/-- The scaling obeys the exact channel-normalization identity. -/
theorem block_adjoint_outputScale_sq (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ) :
    (blockChannel U n).adjointMap (outputScale p n*outputScale p n)=1 := by
  have hc := (weightedBlock U p hp hsum n).complete
  simp only [weightedBlock_kraus,Matrix.conjTranspose_mul,
    (outputScale_isHermitian p n).eq,Matrix.mul_assoc] at hc
  simpa only [adjointMap,Matrix.mul_assoc] using hc

/-- The weighted channel map is output conjugation by the fixed diagonal scale. -/
theorem weightedBlock_map (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ)
    (X : Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ) :
    (weightedBlock U p hp hsum n).map X = outputScale p n*(blockChannel U n).map X*outputScale p n := by
  simp only [map,weightedBlock_kraus,Matrix.conjTranspose_mul,
    (outputScale_isHermitian p n).eq,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]

end Channel

/-- The weighted tensor construction is the actual output-scaled channel used
by the perturbation certificate theorem. -/
theorem weightedBlock_eq_weighted {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀a, 0 ≤ p a) (hsum : ∑ a, p a=1) (n : ℕ) :
    weightedBlock U p hp hsum n =
      WeightedCertificate.weighted (blockChannel U n) (outputScale p n)
        (outputScale_isHermitian p n) (block_adjoint_outputScale_sq U p hp hsum n) := by
  apply KrausChannel.ext
  funext k
  exact weightedBlock_kraus U p hp hsum n k

end Nonadditivity.WeightedBlock
