/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FiniteFreeModel
import Nonadditivity.FiniteMomentMatching
import Nonadditivity.FiniteRegularMatrix
import Nonadditivity.StructuredHaarModel
import Nonadditivity.StructuredFiniteChannel

/-! # Exact finite block-channel moments

Finite quotients separating bounded free words give actual finite tensor
unitaries. Their block-channel trace moments agree exactly with the free trace.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.FiniteBlockModel
open Entropy Channels.KrausChannel FreeModel FreeBridge FiniteRealization
open scoped Matrix Matrix.Norms.L2Operator Kronecker BigOperators
open StructuredHaarModel (kroneckerUnitary)

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ}

/-- A literal product-free-group representation on the tensor input space. -/
def tensorRepresentation (u : ℕ → (FreeGroup (Fin K) →* unitary (Matrix ι ι ℂ))) :
    (r : ℕ) → (Fin r → FreeGroup (Fin K)) →*
      unitary (Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ)
  | 0 => 1
  | r+1 =>
    { toFun := fun g => kroneckerUnitary (tensorRepresentation u r (Fin.init g)) (u r (g (Fin.last r)))
      map_one' := by
        apply Subtype.ext
        change (tensorRepresentation u r (Fin.init (1 : Fin (r+1) → FreeGroup (Fin K))) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
          (u r 1 : Matrix ι ι ℂ) = 1
        have hi : Fin.init (1 : Fin (r+1) → FreeGroup (Fin K)) = 1 := rfl
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
theorem tensorRepresentation_word
    (u : ℕ → (FreeGroup (Fin K) →* unitary (Matrix ι ι ℂ)))
    (w : ℕ → Fin K → FreeGroup (Fin K)) (r : ℕ) (a : FreeModel.Branch K r) :
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

/-- The normalized regular character tensorizes exactly. -/
theorem tensorRepresentation_trace
    (u : ℕ → (FreeGroup (Fin K) →* unitary (Matrix ι ι ℂ))) (R : ℕ)
    (hu : ∀ j w, FreeGroup.norm w ≤ R →
      (u j w : Matrix ι ι ℂ).trace = (Fintype.card ι : ℂ)*(if w=1 then 1 else 0))
    (r : ℕ) (w : Fin r → FreeGroup (Fin K)) (hw : ∀ j, FreeGroup.norm (w j) ≤ R) :
    (tensorRepresentation u r w : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ).trace =
      (Fintype.card (TensorChainIndex ι r):ℂ)*(if w=1 then 1 else 0) := by
  induction r with
  | zero =>
    have he : w=1 := by funext i; exact Fin.elim0 i
    simp [tensorRepresentation,he]
  | succ r ih =>
    change ((tensorRepresentation u r (Fin.init w) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
      (u r (w (Fin.last r)) : Matrix ι ι ℂ)).trace = _
    rw [Matrix.trace_kronecker,ih (Fin.init w) (fun j => hw j.castSucc),
      hu r (w (Fin.last r)) (hw (Fin.last r))]
    have he : w=1 ↔ Fin.init w=1 ∧ w (Fin.last r)=1 := by
      constructor
      · rintro rfl; exact ⟨rfl,rfl⟩
      · rintro ⟨ha,hb⟩
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · exact hb
        · exact congrFun ha i
    by_cases ha : Fin.init w=1 <;> by_cases hb : w (Fin.last r)=1 <;>
      simp [he,ha,hb,TensorChainIndex,Fintype.card_prod]

end Tensor

section FiniteModel

/-- The finite group of completed translations on the word ball. -/
abbrev LocalIndex (K R : ℕ) := Equiv.Perm (FiniteFreeModel.Ball (Fin K) R)

/-- Genuine local unitary evaluation with exactly regular trace through radius R. -/
def localRepresentation (K R : ℕ) :
    FreeGroup (Fin K) →* unitary (Matrix (LocalIndex K R) (LocalIndex K R) ℂ) :=
  (FiniteRegularMatrix.regularUnitary (LocalIndex K R)).comp (FiniteFreeModel.model R)

theorem localRepresentation_trace (K R : ℕ) (w : FreeGroup (Fin K))
    (hw : FreeGroup.norm w ≤ R) :
    (localRepresentation K R w : Matrix (LocalIndex K R) (LocalIndex K R) ℂ).trace =
      (Fintype.card (LocalIndex K R):ℂ)*(if w=1 then 1 else 0) := by
  change (FiniteRegularMatrix.regularUnitary (LocalIndex K R) (FiniteFreeModel.model R w) :
    Matrix (LocalIndex K R) (LocalIndex K R) ℂ).trace = _
  rw [FiniteRegularMatrix.regularUnitaryHom_trace]
  simp only [FiniteFreeModel.model_eq_one_iff R w hw]

/-- The concrete local unitaries supplied to the existing block-channel constructor. -/
def baseUnitary (K R : ℕ) (_j : ℕ) (a : Fin K) :
    unitary (Matrix (LocalIndex K R) (LocalIndex K R) ℂ) :=
  localRepresentation K R (FreeGroup.of a)

/-- The concrete tensor representation, with matrix codomain for algebraic moments. -/
def representation (K R n : ℕ) : ProductFreeGroup K n →*
    Matrix (TensorChainIndex (LocalIndex K R) n) (TensorChainIndex (LocalIndex K R) n) ℂ where
  toFun w := tensorRepresentation (fun _ => localRepresentation K R) n w
  map_one' := congrArg Subtype.val (map_one (tensorRepresentation (fun _ => localRepresentation K R) n))
  map_mul' v w := congrArg Subtype.val (map_mul (tensorRepresentation (fun _ => localRepresentation K R) n) v w)

theorem representation_trace (K R n : ℕ) (w : ProductFreeGroup K n)
    (hw : ∀j, FreeGroup.norm (w j) ≤ R) :
    (representation K R n w).trace =
      (Fintype.card (TensorChainIndex (LocalIndex K R) n):ℂ)*(if w=1 then 1 else 0) :=
  tensorRepresentation_trace (fun _ => localRepresentation K R) R
    (fun _ => localRepresentation_trace K R) n w hw

theorem representation_branchWord (K R n : ℕ) (a : Branch K n) :
    representation K R n (branchWord a) =
      tensorWord (baseUnitary K R) n ((chainBranchEquiv K n).symm a) :=
  tensorRepresentation_word (fun _ => localRepresentation K R)
    (fun _ => FreeGroup.of) n a

theorem representation_inv (K R n : ℕ) (w : ProductFreeGroup K n) :
    representation K R n w⁻¹ = (representation K R n w).conjTranspose := by
  change ((tensorRepresentation (fun _ => localRepresentation K R) n w⁻¹) :
    Matrix (TensorChainIndex (LocalIndex K R) n) (TensorChainIndex (LocalIndex K R) n) ℂ) = _
  rw [map_inv]
  rfl

/-- The algebraic finite polynomial is exactly the actual block adjoint. -/
theorem finiteEval_eq_block_adjoint (K R n : ℕ) [NeZero K]
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    FiniteMomentMatching.finiteEval (representation K R n) (FiniteMomentMatching.gammaPolynomial A) =
      (BlockConstruction.blockChannel (baseUnitary K R) n).adjointMap
        (StructuredFiniteChannel.outputMatrix A) := by
  rw [FiniteMomentMatching.finiteEval_gammaPolynomial,
    StructuredFiniteChannel.block_adjoint_eq_branch_polynomial]
  simp only [Finset.smul_sum,smul_smul,map_mul,representation_inv,representation_branchWord]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [Branch,one_div]

/-- Exact finite moments for every observable, with the genuine HS factor. -/
theorem block_adjoint_moment_le {K n : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hn : 1 ≤ n) (p : ℕ)
    (A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ) (hA : A.trace=0) :
    (((BlockConstruction.blockChannel (baseUnitary K (4*p)) n).adjointMap A)^(2*p)).trace.re ≤
      (Fintype.card (TensorChainIndex (LocalIndex K (4*p)) n):ℝ)*
        (c K n*AdjointPurity.hsLength A)^(2*p) := by
  let B := A.submatrix (branchToOutput K n) (branchToOutput K n)
  have ht : B.trace=0 := (trace_submatrix_equiv _ A).trans hA
  have hb := FiniteMomentMatching.gamma_trace_pow_re_le hK hn
    (representation K (4*p) n) B ht (2*p) (fun w hw =>
      representation_trace K (4*p) n w (by simpa only [←Nat.mul_assoc] using hw))
  rw [finiteEval_eq_block_adjoint] at hb
  have he : StructuredFiniteChannel.outputMatrix B = A := by
    ext a b
    simp [StructuredFiniteChannel.outputMatrix,B]
  rw [he] at hb
  simpa only [B,hsLength_submatrix_equiv] using hb

/-- Normalized even moments of every traceless HS-unit-ball test are at most c^(2p).
All matrices here belong to an explicitly constructed genuine block channel. -/
theorem block_adjoint_normalized_moment_le {K n : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hn : 1 ≤ n) (p : ℕ)
    (A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ) (hA : A.trace=0)
    (hhs : AdjointPurity.hsLength A ≤ 1) :
    (((BlockConstruction.blockChannel (baseUnitary K (4*p)) n).adjointMap A)^(2*p)).trace.re /
      (Fintype.card (TensorChainIndex (LocalIndex K (4*p)) n):ℝ) ≤ (c K n)^(2*p) := by
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).mpr
  apply (block_adjoint_moment_le hK hn p A hA).trans
  rw [mul_comm ((c K n)^(2*p))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by unfold c AdjointPurity.hsLength; positivity)
  exact (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _)).trans_eq (mul_one _)

end FiniteModel

end Nonadditivity.FiniteBlockModel
