/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathRefinedCounting
import Nonadditivity.HaarRefinedVertexFibre
import Nonadditivity.HaarOperatorPathSum

/-! # Exact regrouping over the genuine refined path quotient

The finite path sum is transported to literal refined fibres. The resulting
operator coefficient sum remains inside each class before any norm is taken.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarRefinedVertexFibre
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

/-- A quotient fibre is exactly the literal refined class of its chosen
representative. -/
def refinedQuotientFibreEquiv (C : RefinedClass V d m) :
    {P : Path V d m // Quotient.mk refinedPathSetoid P=C} ≃
      HaarRefinedVertexFibre.Fibre (Quotient.out C) where
  toFun P := ⟨P.val,by
    apply @Quotient.exact _ refinedPathSetoid
    exact (Quotient.out_eq C).trans P.property.symm⟩
  invFun P := ⟨P.val,by
    exact (Quotient.sound P.property).symm.trans (Quotient.out_eq C)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact class regrouping; this statement uses no invariance assumption. -/
theorem sum_paths_eq_sum_refined {R : Type*} [AddCommMonoid R]
    (f : Path V d m → R) :
    ∑ P, f P = ∑ C : RefinedClass V d m,
      ∑ P : HaarRefinedVertexFibre.Fibre (Quotient.out C), f P.val := by
  classical
  rw [← Fintype.sum_fiberwise (Quotient.mk refinedPathSetoid) f]
  apply Finset.sum_congr rfl
  intro C _
  exact (refinedQuotientFibreEquiv C).sum_comp (fun P => f P.val)

/-- Pulling an invariant scalar through the genuine class fibre leaves the
operator coefficients grouped together. -/
theorem sum_paths_smul_eq_sum_refined {R : Type*} [AddCommMonoid R] [Module ℂ R]
    (w : Path V d m → ℂ) (f : Path V d m → R)
    (hw : ∀ P Q, RefinedPattern P Q → w P=w Q) :
    ∑ P, w P • f P = ∑ C : RefinedClass V d m,
      w (Quotient.out C) • ∑ P : HaarRefinedVertexFibre.Fibre (Quotient.out C), f P.val := by
  rw [sum_paths_eq_sum_refined]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [hw (Quotient.out C) P.val P.property]

/-- Norms are taken after summing all coefficients in the refined class. -/
theorem norm_sum_paths_smul_le {R : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
    (w : Path V d m → ℂ) (f : Path V d m → R)
    (hw : ∀ P Q, RefinedPattern P Q → w P=w Q) :
    ‖∑ P, w P • f P‖ ≤ ∑ C : RefinedClass V d m,
      ‖w (Quotient.out C)‖ *
        ‖∑ P : HaarRefinedVertexFibre.Fibre (Quotient.out C), f P.val‖ := by
  rw [sum_paths_smul_eq_sum_refined w f hw]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_smul])

end Nonadditivity.HaarPathClasses

namespace Nonadditivity.HaarOperatorPathBridge
open HaarPathGraph HaarPathClasses HaarRefinedVertexFibre
open scoped BigOperators

/-- The exact operator contribution partitioned into actual refined classes. -/
theorem pathOperatorSum_eq_refinedSum {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (N : ℕ)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p t : ℕ) :
    pathOperatorSum N A p t = ∑ C : RefinedClass (Fin (N+1)) 2 t,
      ∑ P : HaarRefinedVertexFibre.Fibre (Quotient.out C),
        pathWeight P.val • (A^p) (FreeGroup.mk (List.ofFn P.val.colors)) := by
  exact sum_paths_eq_sum_refined _

/-- The grouped coefficient sum needed by the profile Cauchy--Schwarz estimate. -/
def refinedCoefficientSum {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {V : Type*} [Fintype V] [DecidableEq V]
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p : ℕ)
    {t : ℕ} (P : Path V 2 t) : E →L[ℂ] E :=
  ∑ Q : HaarRefinedVertexFibre.Fibre P, (A^p) (FreeGroup.mk (List.ofFn Q.val.colors))

/-- The only analytic input required to extract the weight is its equality
on the refined relation; the partition itself has already been constructed. -/
theorem pathOperatorSum_eq_weighted_refinedSum {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (N : ℕ)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p t : ℕ)
    (hw : ∀ P Q : Path (Fin (N+1)) 2 t, RefinedPattern P Q → pathWeight P=pathWeight Q) :
    pathOperatorSum N A p t = ∑ C : RefinedClass (Fin (N+1)) 2 t,
      pathWeight (Quotient.out C) • refinedCoefficientSum A p (Quotient.out C) := by
  exact sum_paths_smul_eq_sum_refined pathWeight _ hw

end Nonadditivity.HaarOperatorPathBridge
