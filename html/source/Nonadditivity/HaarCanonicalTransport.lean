/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarRecursiveSample
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # Coordinate transport to the manuscript's canonical Haar model -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarIteratedMoments
open MeasureTheory HaarModel HaarWordExpansion HaarTensorReplacement
open ProductHaagerupProduct ProductMomentBridge
open scoped BigOperators Matrix Matrix.Norms.L2Operator

theorem uncurry_measurePreserving (N n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin 2) (LocalUnitary N)).symm
      (recursiveMeasure N n) (sampleMeasure 2 n N) := by
  refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable, ?_⟩
  apply (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (MeasurableEquiv.curry _ _ _).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry (Fin n) (Fin 2) (LocalUnitary N)).symm ⁻¹'
      (Set.univ.pi s) = Set.univ.pi (fun i => Set.univ.pi (fun a => s (i,a))) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Prod.forall]
  rw [he]
  unfold recursiveMeasure
  rw [Measure.pi_pi]
  simp only [pairMeasure, Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun x : Fin n × Fin 2 => haar N (s x))).symm

def tensorTupleEquiv (N : ℕ) : (n : ℕ) → TensorIndex N n ≃ (Fin n → Fin (N+1))
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n+1 => {
      toFun := fun x => Fin.cons x.1 (tensorTupleEquiv N n x.2)
      invFun := fun x => (x 0, (tensorTupleEquiv N n).symm (fun r => x r.succ))
      left_inv := fun x => by simp
      right_inv := fun x => by
        simp only [Equiv.apply_symm_apply]
        funext r
        exact Fin.cases rfl (fun _ => rfl) r }

def tensorChainEquiv (N n : ℕ) :
    TensorIndex N n ≃ Entropy.TensorChainIndex (Fin (N+1)) n :=
  (tensorTupleEquiv N n).trans (FreeBridge.chainTupleEquiv (Fin (N+1)) n).symm

theorem recursiveRepresentation_entry (N n : ℕ) (U : Fin n → Pair N)
    (g : Fin n → FreeGroup (Fin 2)) (a b : TensorIndex N n) :
    recursiveRepresentation N n U (functionGroupHom (Fin 2) n g) a b =
      ∏ r, (pairRepresentation N (U r) (g r) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
        (tensorTupleEquiv N n a r) (tensorTupleEquiv N n b r) := by
  induction n with
  | zero => cases a; cases b; simp [recursiveRepresentation, tensorTupleEquiv, Matrix.one_apply]
  | succ n ih =>
    change (pairRepresentation N (U 0) (g 0) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) a.1 b.1 *
      recursiveRepresentation N n (fun r => U r.succ)
        (functionGroupHom (Fin 2) n (fun r => g r.succ)) a.2 b.2 = _
    rw [ih, Fin.prod_univ_succ]
    rfl

theorem tensorRepresentation_entry {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : ℕ → FreeGroup (Fin 2) →* unitary (Matrix ν ν ℂ)) (n : ℕ)
    (g : Fin n → FreeGroup (Fin 2)) (a b : Entropy.TensorChainIndex ν n) :
    (StructuredHaarModel.tensorRepresentation u n g : Matrix _ _ ℂ) a b =
      ∏ r, (u r.val (g r) : Matrix ν ν ℂ)
        (FreeBridge.chainTupleEquiv ν n a r) (FreeBridge.chainTupleEquiv ν n b r) := by
  induction n with
  | zero => cases a; cases b; simp [StructuredHaarModel.tensorRepresentation, Matrix.one_apply]
  | succ n ih =>
    rcases a with ⟨a₁,a₂⟩
    rcases b with ⟨b₁,b₂⟩
    change (StructuredHaarModel.tensorRepresentation u n (Fin.init g) : Matrix _ _ ℂ) a₁ b₁ *
      (u n (g (Fin.last n)) : Matrix ν ν ℂ) a₂ b₂ = _
    rw [ih, Fin.prod_univ_castSucc]
    simp only [FreeBridge.chainTupleEquiv_succ, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.init, Fin.val_castSucc, Fin.val_last]

theorem recursiveRepresentation_eq_sample (N n : ℕ) (U : Fin n → Pair N)
    (g : Fin n → FreeGroup (Fin 2)) :
    recursiveRepresentation N n U (functionGroupHom (Fin 2) n g) =
      (StructuredHaarModel.sampleRepresentation n N (Function.uncurry U) g : Matrix _ _ ℂ).submatrix
        (tensorChainEquiv N n) (tensorChainEquiv N n) := by
  ext a b
  rw [recursiveRepresentation_entry]
  change _ = (StructuredHaarModel.tensorRepresentation
    (StructuredHaarModel.localRepresentation n N (Function.uncurry U)) n g : Matrix _ _ ℂ)
      (tensorChainEquiv N n a) (tensorChainEquiv N n b)
  rw [tensorRepresentation_entry]
  apply Finset.prod_congr rfl
  intro r hr
  have he : StructuredHaarModel.localRepresentation n N (Function.uncurry U) r =
      pairRepresentation N (U r) := by
    unfold StructuredHaarModel.localRepresentation pairRepresentation
    congr 1
    funext x
    rw [sampleUnitary_coordinate]
    rfl
  rw [he]
  simp only [tensorChainEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]

section PolynomialTransport
variable {G H ι : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι]

def transportPolynomial (φ : G →* H) : MatrixPolynomial G ι →+* MatrixPolynomial H ι :=
  MonoidAlgebra.mapDomainRingHom _ φ

@[simp] theorem transportPolynomial_single (φ : G →* H) (g : G) (A : Matrix ι ι ℂ) :
    transportPolynomial φ (MonoidAlgebra.single g A) = MonoidAlgebra.single (φ g) A :=
  MonoidAlgebra.mapDomain_single

theorem transportPolynomial_adjoint (φ : G →* H) (f : MatrixPolynomial G ι) :
    transportPolynomial φ (adjointPolynomial f) = adjointPolynomial (transportPolynomial φ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk =>
    change transportPolynomial φ (adjointPolynomial ((f : MatrixPolynomial G ι)+k)) = _
    rw [adjointPolynomial_add, map_add, hf, hk, map_add, adjointPolynomial_add]
  | single g A => simp only [adjointPolynomial_single, transportPolynomial_single, map_inv]

theorem transportPolynomial_selfAdjoint (φ : G →* H) (f : MatrixPolynomial G ι)
    (hf : IsSelfAdjoint (regularEval f)) :
    IsSelfAdjoint (regularEval (transportPolynomial φ f)) := by
  rw [regularEval_selfAdjoint_iff] at hf ⊢
  rw [← transportPolynomial_adjoint, hf]

theorem transportPolynomial_regular_norm (φ : G →* H) (hφ : Function.Injective φ)
    (f : MatrixPolynomial G ι) : ‖regularEval (transportPolynomial φ f)‖ = ‖regularEval f‖ := by
  have he : regularEval (transportPolynomial φ f) =
      RegularCoefficientEnergy.regularPolynomial (f.support.image φ) (Function.extend φ f 0) := by
    rw [MatrixRegularRestriction.matrixPolynomial_image_eq φ hφ]
    conv_lhs => rw [← MonoidAlgebra.sum_single f]
    change regularEval (transportPolynomial φ (∑ g ∈ f.support, MonoidAlgebra.single g (f g))) = _
    simp only [map_sum, transportPolynomial_single, regularEval_single]
    rw [MatrixRegularRestriction.coefficientPolynomial]
    rw [← Finset.sum_coe_sort f.support]
    rfl
  rw [he, MatrixRegularRestriction.matrixPolynomial_injective_norm_eq φ hφ,
    regularEval_eq_regularPolynomial]

end PolynomialTransport

theorem finiteEval_transport_sample_norm (N n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Fin n → Pair N) (f : MatrixPolynomial (Fin n → FreeGroup (Fin 2)) ι) :
    ‖finiteEval (recursiveRepresentation N n U)
      (transportPolynomial (functionGroupHom (Fin 2) n) f)‖ =
      ‖finiteEval (representationMatrix
        (StructuredHaarModel.sampleRepresentation n N (Function.uncurry U))) f‖ := by
  let e : (ι × TensorIndex N n) ≃ (ι × Entropy.TensorChainIndex (Fin (N+1)) n) :=
    Equiv.prodCongr (Equiv.refl ι) (tensorChainEquiv N n)
  have he : finiteEval (recursiveRepresentation N n U)
      (transportPolynomial (functionGroupHom (Fin 2) n) f) =
      (finiteEval (representationMatrix
        (StructuredHaarModel.sampleRepresentation n N (Function.uncurry U))) f).submatrix e e := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f k hf hk =>
      change finiteEval (recursiveRepresentation N n U)
        (transportPolynomial (functionGroupHom (Fin 2) n)
          ((f : MatrixPolynomial (Fin n → FreeGroup (Fin 2)) ι)+k)) = _
      rw [map_add, map_add, map_add, Matrix.submatrix_add, hf, hk]
      rfl
    | single g A =>
      simp only [transportPolynomial_single, finiteEval_single,
        recursiveRepresentation_eq_sample]
      rfl
  rw [he, MatrixNormReindex.submatrix_equiv_norm]

/-- Exact identification with the pre-existing canonical Haar sample and its
literal tensor representation, at every moment order. -/
theorem canonicalMoment_eq_iteratedMoment (N p n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : MatrixPolynomial (Fin n → FreeGroup (Fin 2)) ι) :
    (∫ ω : Sample 2 n N,
      ‖finiteEval (representationMatrix (StructuredHaarModel.sampleRepresentation n N ω)) f‖^p
        ∂sampleMeasure 2 n N) =
      iteratedMoment N p n (transportPolynomial (functionGroupHom (Fin 2) n) f) := by
  rw [← recursiveMoment_eq_iteratedMoment]
  have hm := (uncurry_measurePreserving N n).integral_comp' (fun ω : Sample 2 n N =>
    ‖finiteEval (representationMatrix (StructuredHaarModel.sampleRepresentation n N ω)) f‖^p)
  rw [← hm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun U => congrArg (fun x : ℝ => x^p)
    (finiteEval_transport_sample_norm N n U f).symm)

end Nonadditivity.HaarIteratedMoments
