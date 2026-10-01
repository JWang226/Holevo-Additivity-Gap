/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductHaagerupWords

/-! # Haagerup's homogeneous inequality with bounded operator coefficients

For the literal regular polynomial supported on reduced words of length `l`,
the operator norm is at most `(l+1)` times the coefficient `ℓ²` norm.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.ProductHaagerupHomogeneous
open scoped BigOperators InnerProductSpace
open FreeCreation (Letter)
open RegularCoefficientEnergy (VectorHilbert liftOperator)
open CollinsYounTensor ProductHaagerupCreation ProductHaagerupWords

abbrev Words (α : Type*) (l : ℕ) := List.Vector (Letter α) l

variable {α E : Type*} [DecidableEq α] [Fintype α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A word splits bijectively into its prefix and suffix. -/
def splitEquiv (l k : ℕ) (hk : k ≤ l) : Words α l ≃ Words α k × Words α (l-k) where
  toFun w := (⟨w.1.take k, by simp [w.2, Nat.min_eq_left hk]⟩,
    ⟨w.1.drop k, by simp [w.2]⟩)
  invFun uv := ⟨uv.1.1 ++ uv.2.1, by simp [uv.1.2, uv.2.2, Nat.add_sub_of_le hk]⟩
  left_inv w := by apply Subtype.ext; exact List.take_append_drop k w.1
  right_inv uv := by
    apply Prod.ext <;> apply Subtype.ext
    · simp [uv.1.2]
    · simp [uv.1.2]

def coefficientEnergy {l : ℕ} (B : Words α l → E →L[ℂ] E) : ℝ :=
  ∑ w, ‖B w‖ ^ 2

omit [DecidableEq α] [CompleteSpace E] in
theorem coefficientEnergy_nonneg {l : ℕ} (B : Words α l → E →L[ℂ] E) :
    0 ≤ coefficientEnergy B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The literal operator-coefficient regular polynomial at a fixed word length. -/
def polynomial {l : ℕ} (B : Words α l → E →L[ℂ] E) :
    WordHilbert α E →L[ℂ] WordHilbert α E :=
  ∑ w, (liftOperator (B w)).comp (leftRegular (FreeGroup.mk w.1))

def polynomialSector {l : ℕ} (B : Words α l → E →L[ℂ] E) (k : ℕ) :
    WordHilbert α E →L[ℂ] WordHilbert α E :=
  ∑ w, (liftOperator (B w)).comp (sector w.1 k)

/-- Each cancellation sector obeys the coefficient `ℓ²` bound. -/
theorem polynomialSector_norm_le {l : ℕ} (B : Words α l → E →L[ℂ] E)
    (k : ℕ) (hk : k ≤ l) :
    ‖polynomialSector B k‖ ≤ Real.sqrt (coefficientEnergy B) := by
  let e := splitEquiv (α := α) l k hk
  let C : Words α k → WordHilbert α E →L[ℂ] WordHilbert α E :=
    fun u => createWord u.1
  let D : Words α (l-k) → WordHilbert α E →L[ℂ] WordHilbert α E :=
    fun v => createWord (FreeGroup.invRev v.1)
  let A : Words α k → Words α (l-k) → WordHilbert α E →L[ℂ] WordHilbert α E := fun u v => liftOperator (G := FreeGroup α) (B (e.symm (u,v)))
  have hc : ∀ u f, ‖C u f‖ ≤ ‖f‖ := fun u f => createWord_contract u.1 f
  have hd : ∀ v f, ‖D v f‖ ≤ ‖f‖ := fun v f => createWord_contract _ f
  have ho : ∀ u v, u ≠ v → ∀ f g, inner ℂ (C u f) (C v g) = 0 := by
    intro u v huv f g
    exact createWord_inner_zero u.1 v.1 (u.2.trans v.2.symm)
      (fun h => huv (Subtype.ext h)) f g
  have hdo : ∀ u v, u ≠ v → ∀ f g, inner ℂ (D u f) (D v g) = 0 := by
    intro u v huv f g
    apply createWord_inner_zero (E := E) _ _ (by simp [u.2, v.2]) _ f g
    exact fun h => huv (Subtype.ext (FreeGroup.invRev_injective h))
  have he : polynomialSector B k = ∑ u, ∑ v, (C u).comp ((A u v).comp (D v).adjoint) := by
    unfold polynomialSector
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [sector_eq_take_drop _ k (by simpa using hk),
      annihilateWord_eq_adjoint, ← ContinuousLinearMap.comp_assoc, lift_createWord_commute,
      ContinuousLinearMap.comp_assoc]
    dsimp [e, splitEquiv, C, D, A]
    simp [u.2]
  rw [he]
  apply (sector_norm_le C D hc ho hd hdo A).trans
  apply Real.sqrt_le_sqrt
  have hn (u : Words α k) (v : Words α (l-k)) : ‖A u v‖ ≤ ‖B (e.symm (u,v))‖ := by
    dsimp only [A]
    apply LinearMap.mkContinuous_norm_le
    exact norm_nonneg _
  have hen : (∑ u : Words α k, ∑ v : Words α (l-k), ‖A u v‖ ^ 2) ≤
      ∑ u : Words α k, ∑ v : Words α (l-k), ‖B (e.symm (u,v))‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact pow_le_pow_left₀ (norm_nonneg (A u v)) (hn u v) 2
  have hee : (∑ u : Words α k, ∑ v : Words α (l-k), ‖B (e.symm (u,v))‖ ^ 2) =
      coefficientEnergy B := by
    calc
      _ = ∑ uv : Words α k × Words α (l-k), ‖B (e.symm uv)‖ ^ 2 :=
        (Fintype.sum_prod_type (fun uv : Words α k × Words α (l-k) =>
          ‖B (e.symm uv)‖ ^ 2)).symm
      _ = coefficientEnergy B := e.symm.sum_comp (fun w : Words α l => ‖B w‖ ^ 2)
  exact hen.trans_eq hee

/-- Exact homogeneous Haagerup estimate, for actual vector-valued convolution.
No analytic norm comparison is assumed. -/
theorem polynomial_norm_le {l : ℕ} (B : Words α l → E →L[ℂ] E)
    (hred : ∀ w, ¬ FreeGroup.IsReduced w.1 → B w = 0) :
    ‖polynomial B‖ ≤ (l+1 : ℕ) * Real.sqrt (coefficientEnergy B) := by
  have he : polynomial B = ∑ k ∈ Finset.range (l+1), polynomialSector B k := by
    unfold polynomial polynomialSector
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : FreeGroup.IsReduced w.1
    · rw [regular_word_decomposition _ hw, ContinuousLinearMap.comp_finset_sum, w.2]
    · have hz : liftOperator (G := FreeGroup α) (B w) = 0 := by
        rw [hred w hw]
        ext f x
        simp
      simp [hz]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range (l+1), ‖polynomialSector B k‖ := norm_sum_le (Finset.range (l+1)) (fun k => polynomialSector B k)
    _ ≤ ∑ k ∈ Finset.range (l+1), Real.sqrt (coefficientEnergy B) :=
      Finset.sum_le_sum (fun k hk => polynomialSector_norm_le B k (by
        have hh := Finset.mem_range.mp hk
        omega))
    _ = _ := by simp

end Nonadditivity.ProductHaagerupHomogeneous
