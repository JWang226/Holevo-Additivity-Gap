/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.StructuredLinearization
import Nonadditivity.HaarModel
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average

/-! # Concrete tensor representation of independent Haar generator pairs

The explicit construction samples two independent Haar matrices per tensor
factor, then evaluates the proved logarithmic-length words. The derived K
unitaries within each factor are not asserted independent or Haar.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
namespace Nonadditivity.StructuredHaarModel
open MeasureTheory Entropy Channels.KrausChannel
open scoped Matrix Matrix.Norms.L2Operator Kronecker BigOperators Topology

section Tensor
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def kroneckerUnitary (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ)) :
    unitary (Matrix (ι×κ) (ι×κ) ℂ) :=
  ⟨(U:Matrix ι ι ℂ) ⊗ₖ (V:Matrix κ κ ℂ), by
    apply Unitary.mem_iff.mpr
    constructor
    · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker]
      rw [← Matrix.mul_kronecker_mul]
      change (star (U:Matrix ι ι ℂ)*(U:Matrix ι ι ℂ)) ⊗ₖ
        (star (V:Matrix κ κ ℂ)*(V:Matrix κ κ ℂ)) = 1
      rw [(Unitary.mem_iff.mp U.property).1,(Unitary.mem_iff.mp V.property).1,
        Matrix.one_kronecker_one]
    · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker]
      rw [← Matrix.mul_kronecker_mul]
      change ((U:Matrix ι ι ℂ)*star (U:Matrix ι ι ℂ)) ⊗ₖ
        ((V:Matrix κ κ ℂ)*star (V:Matrix κ κ ℂ)) = 1
      rw [(Unitary.mem_iff.mp U.property).2,(Unitary.mem_iff.mp V.property).2,
        Matrix.one_kronecker_one]⟩

/-- A literal product-free-group representation on the tensor input space. -/
def tensorRepresentation (u : ℕ → (FreeGroup (Fin 2) →* unitary (Matrix ι ι ℂ))) :
    (r : ℕ) → (Fin r → FreeGroup (Fin 2)) →*
      unitary (Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ)
  | 0 => 1
  | r+1 =>
    { toFun := fun g => kroneckerUnitary (tensorRepresentation u r (Fin.init g)) (u r (g (Fin.last r)))
      map_one' := by
        apply Subtype.ext
        change (tensorRepresentation u r (Fin.init (1 : Fin (r+1) → FreeGroup (Fin 2))) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
          (u r 1 : Matrix ι ι ℂ) = 1
        have hi : Fin.init (1 : Fin (r+1) → FreeGroup (Fin 2)) = 1 := rfl
        rw [hi,map_one,map_one]
        exact Matrix.one_kronecker_one
      map_mul' := by
        intro g h
        apply Subtype.ext
        have hi : Fin.init (g*h) = Fin.init g * Fin.init h := rfl
        change (tensorRepresentation u r (Fin.init (g*h)) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
          (u r ((g*h) (Fin.last r)) : Matrix ι ι ℂ) = _
        rw [hi,map_mul]
        change ((tensorRepresentation u r (Fin.init g) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) *
          (tensorRepresentation u r (Fin.init h) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ)) ⊗ₖ
          (u r (g (Fin.last r)*h (Fin.last r)) : Matrix ι ι ℂ) = _
        rw [map_mul]
        exact Matrix.mul_kronecker_mul _ _ _ _ }

/-- The representation evaluates individual branch words to the actual ordered
tensor words used by the Kraus-channel construction. -/
theorem tensorRepresentation_word {K : ℕ}
    (u : ℕ → (FreeGroup (Fin 2) →* unitary (Matrix ι ι ℂ)))
    (w : ℕ → Fin K → FreeGroup (Fin 2)) (r : ℕ) (a : FreeModel.Branch K r) :
    (tensorRepresentation u r (fun i => w i.val (a i)) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) =
      tensorWord (fun j b => u j (w j b)) r ((FreeBridge.chainBranchEquiv K r).symm a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (tensorRepresentation u r (fun i => w i.val (a i.castSucc)) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
      (u r (w r (a (Fin.last r))) : Matrix ι ι ℂ) = _
    change (tensorRepresentation u r (fun i => w i.val (a i.castSucc)) :
      Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
      (u r (w r (a (Fin.last r))) : Matrix ι ι ℂ) =
      tensorWord (fun j b => u j (w j b)) r
        ((FreeBridge.chainBranchEquiv K r).symm (Fin.init a)) ⊗ₖ
      (u r (w r (a (Fin.last r))) : Matrix ι ι ℂ)
    congr 1
    simpa only [Fin.init] using ih (Fin.init a)
end Tensor

/-- Local free-group evaluation in each independently sampled Haar pair. -/
def localRepresentation (n N : ℕ) (ω : HaarModel.Sample 2 n N) (j : ℕ) :
    FreeGroup (Fin 2) →* HaarModel.LocalUnitary N :=
  FreeGroup.lift (HaarModel.sampleUnitary 2 n N ω j)

/-- The canonical tensor representation of all sampled pairs. -/
def sampleRepresentation (n N : ℕ) (ω : HaarModel.Sample 2 n N) :
    StructuredLinearization.G n →*
      unitary (Matrix (TensorChainIndex (Fin (N+1)) n) (TensorChainIndex (Fin (N+1)) n) ℂ) :=
  tensorRepresentation (localRepresentation n N ω) n

/-- The actual K derived unitaries, obtained from the logarithmic-length embedding. -/
def derivedUnitary (K n N : ℕ) (hK : 2 ≤ K) (ω : HaarModel.Sample 2 n N)
    (j : ℕ) (a : Fin K) : HaarModel.LocalUnitary N :=
  localRepresentation n N ω j (InitialNetReduction.shortWord K hK a)

@[simp] theorem sampleRepresentation_branchWord (K n N : ℕ) (hK : 2 ≤ K)
    (ω : HaarModel.Sample 2 n N) (a : FreeModel.Branch K n) :
    (sampleRepresentation n N ω
      (InitialNetReduction.shortProductEmbedding K n hK (FreeModel.branchWord a)) : Matrix _ _ ℂ) =
      tensorWord (derivedUnitary K n N hK ω) n ((FreeBridge.chainBranchEquiv K n).symm a) :=
  tensorRepresentation_word (localRepresentation n N ω)
    (fun _ => InitialNetReduction.shortWord K hK) n a

/-- Every fixed word is continuous in its two unitary arguments. -/
theorem continuous_localRepresentation (n N j : ℕ) (g : FreeGroup (Fin 2)) :
    Continuous (fun ω : HaarModel.Sample 2 n N => localRepresentation n N ω j g) := by
  have hl : ∀ l : List (Fin 2 × Bool), Continuous
      (fun ω : HaarModel.Sample 2 n N => localRepresentation n N ω j (FreeGroup.mk l)) := by
    intro l
    induction l with
    | nil => simpa using (continuous_const : Continuous (fun _ : HaarModel.Sample 2 n N => (1:HaarModel.LocalUnitary N)))
    | cons x l ih =>
      simp only [localRepresentation,FreeGroup.lift_mk,List.map_cons,List.prod_cons] at ih ⊢
      apply Continuous.mul _ ih
      cases hx : x.2
      · exact (HaarModel.continuous_sampleUnitary 2 n N j x.1).inv
      · exact HaarModel.continuous_sampleUnitary 2 n N j x.1
  simpa only [FreeGroup.mk_toWord] using hl g.toWord

/-- Continuity holds for every fixed product-group word, without a linearity assumption. -/
theorem continuous_tensorRepresentation (n N r : ℕ) (g : Fin r → FreeGroup (Fin 2)) :
    Continuous (fun ω : HaarModel.Sample 2 n N =>
      (tensorRepresentation (localRepresentation n N ω) r g : Matrix (TensorChainIndex (Fin (N+1)) r) (TensorChainIndex (Fin (N+1)) r) ℂ)) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    apply continuous_matrix
    intro a b
    change Continuous (fun ω : HaarModel.Sample 2 n N =>
      (tensorRepresentation (localRepresentation n N ω) r (Fin.init g) : Matrix (TensorChainIndex (Fin (N+1)) r) (TensorChainIndex (Fin (N+1)) r) ℂ) a.1 b.1 *
      (localRepresentation n N ω r (g (Fin.last r)) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a.2 b.2)
    exact ((ih (Fin.init g)).matrix_elem _ _).mul
      ((continuous_subtype_val.comp (continuous_localRepresentation n N r (g (Fin.last r)))).matrix_elem _ _)

/-- The literal finite polynomial norm is a continuous, integrable random variable. -/
theorem continuous_polynomial (n N : ℕ)
    (H : PolynomialReduction.Polynomial (StructuredLinearization.G n)) :
    Continuous (fun ω : HaarModel.Sample 2 n N => H.finiteEval (sampleRepresentation n N ω)) := by
  unfold PolynomialReduction.Polynomial.finiteEval
  apply continuous_finset_sum
  intro w hw
  apply continuous_matrix
  intro a b
  exact continuous_const.mul ((continuous_tensorRepresentation n N n w).matrix_elem a.2 b.2)

theorem integrable_polynomial_norm (n N : ℕ)
    (H : PolynomialReduction.Polynomial (StructuredLinearization.G n)) :
    Integrable (fun ω : HaarModel.Sample 2 n N => ‖H.finiteEval (sampleRepresentation n N ω)‖)
      (HaarModel.sampleMeasure 2 n N) :=
  (continuous_polynomial n N H).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Nonadditivity.StructuredHaarModel
