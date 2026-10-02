/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DampedChannel
import Nonadditivity.SpectralDamping
import Nonadditivity.InitialNetReduction

/-! # Dimension-free stability under small output weights

Output multiplication by a normalized Hermitian weight matrix gives an actual
Kraus channel. Its damped adjoint certificate changes by at most δ(2+δ), where
δ bounds the operator norm of the weight matrix minus the identity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
namespace Nonadditivity.WeightedCertificate
open Channels Channels.KrausChannel AdjointPurity
open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {ι ο κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- A genuine channel obtained by multiplying every output Kraus operator by V. -/
def weighted (T : KrausChannel ι ο κ) (V : Matrix ο ο ℂ) (hV : V.IsHermitian)
    (hcomplete : T.adjointMap (V*V)=1) : KrausChannel ι ο κ where
  kraus k := V*T.kraus k
  complete := by
    simpa only [Matrix.conjTranspose_mul,hV.eq,Matrix.mul_assoc,adjointMap]
      using hcomplete

@[simp] theorem weighted_kraus (T : KrausChannel ι ο κ) (V : Matrix ο ο ℂ)
    (hV : V.IsHermitian) (hcomplete : T.adjointMap (V*V)=1) (k : κ) :
    (weighted T V hV hcomplete).kraus k = V*T.kraus k := rfl

theorem weighted_map (T : KrausChannel ι ο κ) (V : Matrix ο ο ℂ)
    (hV : V.IsHermitian) (hcomplete : T.adjointMap (V*V)=1) (X : Matrix ι ι ℂ) :
    (weighted T V hV hcomplete).map X = V*T.map X*V := by
  simp only [map,weighted,Matrix.conjTranspose_mul,hV.eq,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]

theorem weighted_adjointMap (T : KrausChannel ι ο κ) (V : Matrix ο ο ℂ)
    (hV : V.IsHermitian) (hcomplete : T.adjointMap (V*V)=1) (A : Matrix ο ο ℂ) :
    (weighted T V hV hcomplete).adjointMap A = T.adjointMap (V*A*V) := by
  simp only [adjointMap,weighted,Matrix.conjTranspose_mul,hV.eq,Matrix.mul_assoc]

/-- Positivity makes the actual Kraus adjoint monotone. -/
theorem adjointMap_mono (T : KrausChannel ι ο κ) {A B : Matrix ο ο ℂ} (hAB : A≤B) :
    T.adjointMap A ≤ T.adjointMap B := by
  rw [Matrix.le_iff] at hAB ⊢
  have h := T.adjointMap_posSemidef (B-A) hAB
  have he : T.adjointMap (B-A) = T.adjointMap B-T.adjointMap A :=
    (T.adjointLinearMap).map_sub B A
  rwa [he] at h

theorem adjointMap_real_smul_one (T : KrausChannel ι ο κ) (r : ℝ) :
    T.adjointMap (r • (1 : Matrix ο ο ℂ)) = r • (1 : Matrix ι ι ℂ) := by
  change T.adjointMap ((r : ℂ) • 1) = (r : ℂ) • 1
  rw [adjointMap_smul,adjointMap_one]

/-- Every genuine channel adjoint contracts the norm of Hermitian observables. -/
theorem adjointMap_norm_le (T : KrausChannel ι ο κ) (A : Matrix ο ο ℂ)
    (hA : A.IsHermitian) : ‖T.adjointMap A‖ ≤ ‖A‖ := by
  letI : CStarAlgebra (Matrix ο ο ℂ) := {}
  have hu : A ≤ ‖A‖ • (1 : Matrix ο ο ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hA.isSelfAdjoint.le_algebraMap_norm_self
  have hl : (-‖A‖) • (1 : Matrix ο ο ℂ) ≤ A := by
    have h := hA.neg.isSelfAdjoint.le_algebraMap_norm_self
    simpa only [norm_neg,Algebra.algebraMap_eq_smul_one,neg_smul,neg_neg] using
      neg_le_neg h
  apply SpectralDamping.norm_le_of_bounds _ (T.adjointMap_isHermitian A hA) (norm_nonneg _)
  · simpa only [adjointMap_real_smul_one] using adjointMap_mono T hl
  · simpa only [adjointMap_real_smul_one] using adjointMap_mono T hu

/-- Every Hermitian damping with positive discarded mass is an operator contraction. -/
theorem damping_norm_le_one (F : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) : ‖F‖ ≤ 1 := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  have hp : (F*F).PosSemidef := by
    simpa only [hF.eq] using Matrix.posSemidef_conjTranspose_mul_self F
  have hn : ‖F*F‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp.nonneg).mpr (Matrix.le_iff.mpr hres)
  rw [hF.isSelfAdjoint.norm_mul_self] at hn
  nlinarith [norm_nonneg F]

/-- Sandwiching by a contraction cannot increase the operator norm. -/
theorem sandwich_norm_le (F X : Matrix ι ι ℂ) (hF : ‖F‖ ≤ 1) : ‖F*X*F‖ ≤ ‖X‖ := by
  calc
    ‖F*X*F‖ ≤ (‖F‖*‖X‖)*‖F‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖X‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hF (norm_nonneg _)) hF (norm_nonneg _) (by positivity)
    _ = ‖X‖ := by ring

/-- A small change of output weights has a dimension-free operator bound. -/
theorem weighted_observable_sub_norm_le (V A : Matrix ο ο ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hV : ‖V-1‖ ≤ δ) :
    ‖V*A*V-A‖ ≤ δ*(2+δ)*‖A‖ := by
  have hv : ‖V‖ ≤ 1+δ := by
    calc
      ‖V‖ = ‖(V-1)+1‖ := by rw [sub_add_cancel]
      _ ≤ ‖V-1‖+‖(1 : Matrix ο ο ℂ)‖ := norm_add_le _ _
      _ ≤ 1+δ := by rw [norm_one]; linarith
  have he : V*A*V-A = (V-1)*A*V+A*(V-1) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(V-1)*A*V‖+‖A*(V-1)‖ := norm_add_le _ _
    _ ≤ ‖V-1‖*‖A‖*‖V‖+‖A‖*‖V-1‖ := add_le_add
      ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_mul_le _ _)
    _ ≤ δ*‖A‖*(1+δ)+‖A‖*δ := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_right hV (norm_nonneg _)) hv
        (norm_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
    _ = _ := by ring

/-- The same damping matrix retains the original certificate up to a vanishing,
input-dimension-independent loss in the output weights. -/
theorem damped_weighted_certificate (T : KrausChannel ι ο κ)
    (V : Matrix ο ο ℂ) (hV : V.IsHermitian) (hcomplete : T.adjointMap (V*V)=1)
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef)
    {t δ : ℝ} (hδ : 0 ≤ δ) (hweight : ‖V-1‖ ≤ δ)
    (hcert : ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 →
      ‖(DampedChannel.damped T F hF hres).adjointMap A‖ ≤ t*hsLength A) :
    ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 →
      ‖(DampedChannel.damped (weighted T V hV hcomplete) F hF hres).adjointMap A‖ ≤
        (t+δ*(2+δ))*hsLength A := by
  intro A hA ht
  have hc : (V*A*V-A).IsHermitian := by
    change (V*A*V-A).conjTranspose = V*A*V-A
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,hV.eq,hA.eq,Matrix.mul_assoc]
  have he : (DampedChannel.damped (weighted T V hV hcomplete) F hF hres).adjointMap A =
      (DampedChannel.damped T F hF hres).adjointMap A + F*T.adjointMap (V*A*V-A)*F := by
    rw [DampedChannel.damped_adjointMap_traceless _ _ _ _ _ ht,
      DampedChannel.damped_adjointMap_traceless _ _ _ _ _ ht,weighted_adjointMap]
    have hs := (T.adjointLinearMap).map_sub (V*A*V) A
    change T.adjointMap (V*A*V-A)=T.adjointMap (V*A*V)-T.adjointMap A at hs
    rw [hs,Matrix.mul_sub,Matrix.sub_mul]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have herror : ‖F*T.adjointMap (V*A*V-A)*F‖ ≤ δ*(2+δ)*hsLength A := by
    calc
      _ ≤ ‖T.adjointMap (V*A*V-A)‖ := sandwich_norm_le F (T.adjointMap (V*A*V-A)) (damping_norm_le_one F hF hres)
      _ ≤ ‖V*A*V-A‖ := adjointMap_norm_le T _ hc
      _ ≤ δ*(2+δ)*‖A‖ := weighted_observable_sub_norm_le V A hδ hweight
      _ ≤ δ*(2+δ)*hsLength A := mul_le_mul_of_nonneg_left
        (InitialNetReduction.norm_le_hsLength A hA) (by positivity)
  have h := add_le_add (hcert A hA ht) herror
  convert h using 1
  ring

end Nonadditivity.WeightedCertificate
