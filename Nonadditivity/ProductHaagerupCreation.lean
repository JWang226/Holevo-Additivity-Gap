/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.CollinsYounTensor

/-! # Arbitrary reduced-word creation operators

Actual word creation on vector-valued `ℓ²` and the Hilbert-space estimate for
arbitrary cancellation sectors.  Coefficients may themselves be bounded
operators on any complex Hilbert space.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.ProductHaagerupCreation

open scoped BigOperators InnerProductSpace
open FreeCreation (Letter flip letter)
open RegularCoefficientEnergy (VectorHilbert liftOperator)
open CollinsYounTensor

section OrthogonalContractions

variable {I J H : Type*} [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Orthogonal contraction ranges give an annihilation row contraction. -/
theorem adjoint_energy_le (C : I → H →L[ℂ] H)
    (hc : ∀ i x, ‖C i x‖ ≤ ‖x‖)
    (ho : ∀ i j, i ≠ j → ∀ x y, inner ℂ (C i x) (C j y) = 0) (f : H) :
    (∑ i, ‖(C i).adjoint f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  let S : H := ∑ i, C i ((C i).adjoint f)
  let a : ℝ := ∑ i, ‖(C i).adjoint f‖ ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : ‖S‖ ^ 2 ≤ a := by
    dsimp [S, a]
    rw [CollinsYoun.norm_sum_sq_of_inner_zero _ (fun i j hij => ho i j hij _ _)]
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hc i _) 2)
  have hi : (inner ℂ S f).re = a := by
    dsimp [S, a]
    rw [sum_inner, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hb : a ≤ ‖S‖ * ‖f‖ := by rw [← hi]; exact re_inner_le_norm (𝕜 := ℂ) S f
  have hb2 := pow_le_pow_left₀ ha hb 2
  rw [mul_pow] at hb2
  have hs2 := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖f‖)
  nlinarith

/-- One cancellation sector has coefficient `ℓ²` norm as its operator bound.
This uses only orthogonal creation ranges and their proved row contraction. -/
theorem sector_norm_le (C : I → H →L[ℂ] H) (D : J → H →L[ℂ] H)
    (hc : ∀ i x, ‖C i x‖ ≤ ‖x‖)
    (ho : ∀ i j, i ≠ j → ∀ x y, inner ℂ (C i x) (C j y) = 0)
    (hd : ∀ j x, ‖D j x‖ ≤ ‖x‖)
    (hdo : ∀ i j, i ≠ j → ∀ x y, inner ℂ (D i x) (D j y) = 0)
    (B : I → J → H →L[ℂ] H) :
    ‖∑ i, ∑ j, (C i).comp ((B i j).comp (D j).adjoint)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  let row : I → H := fun i => ∑ j, B i j ((D j).adjoint f)
  have he : (∑ i, ∑ j, (C i).comp ((B i j).comp (D j).adjoint)) f =
      ∑ i, C i (row i) := by simp [row, map_sum]
  rw [he]
  have hdenergy := adjoint_energy_le D hd hdo f
  have hrow : ∀ i, ‖row i‖ ^ 2 ≤ (∑ j, ‖B i j‖ ^ 2) * ‖f‖ ^ 2 := by
    intro i
    have hn : ‖row i‖ ≤ ∑ j, ‖B i j‖ * ‖(D j).adjoint f‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun j _ => (B i j).le_opNorm _))
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => ‖B i j‖) (fun j => ‖(D j).adjoint f‖)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    exact (h2.trans hh).trans
      (mul_le_mul_of_nonneg_left hdenergy (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity),
    CollinsYoun.norm_sum_sq_of_inner_zero _ (fun i j hij => ho i j hij _ _), Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ =>
    (pow_le_pow_left₀ (norm_nonneg _) (hc i _) 2).trans (hrow i))

end OrthogonalContractions

section Words

variable {α E : Type*} [DecidableEq α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev WordHilbert (α E : Type*) [NormedAddCommGroup E] := VectorHilbert (FreeGroup α) E

def createWord : List (Letter α) → WordHilbert α E →L[ℂ] WordHilbert α E
  | [] => ContinuousLinearMap.id ℂ _
  | s :: w => (creation s).comp (createWord w)

@[simp] theorem createWord_nil : createWord (E := E) ([] : List (Letter α)) =
    ContinuousLinearMap.id ℂ _ := rfl

@[simp] theorem createWord_cons (s : Letter α) (w : List (Letter α)) :
    createWord (E := E) (s :: w) = (creation s).comp (createWord w) := rfl

theorem createWord_contract (w : List (Letter α)) (f : WordHilbert α E) :
    ‖createWord w f‖ ≤ ‖f‖ := by
  induction w with
  | nil => exact le_rfl
  | cons s w ih => exact (creation_norm_le s (createWord w f)).trans ih

theorem createWord_append (u v : List (Letter α)) :
    createWord (E := E) (u ++ v) = (createWord u).comp (createWord v) := by
  induction u with
  | nil => simp
  | cons s u ih => simp [ih, ContinuousLinearMap.comp_assoc]

/-- A cancellation inside a purported creation word makes it zero. -/
theorem createWord_flip_zero (s : Letter α) (w : List (Letter α)) :
    createWord (E := E) (s :: flip s :: w) = 0 := by
  rw [createWord_cons, createWord_cons, ← ContinuousLinearMap.comp_assoc,
    creation_comp_flip_zero, ContinuousLinearMap.zero_comp]

/-- On a reduced nonempty suffix, the first creator is the full regular shift. -/
theorem createWord_cons_eq_shift {s t : Letter α} (h : flip s ≠ t)
    (w : List (Letter α)) :
    createWord (E := E) (s :: t :: w) =
      (leftRegular (letter s)).comp (createWord (t :: w)) := by
  simp only [createWord_cons]
  rw [← ContinuousLinearMap.comp_assoc, creation_comp_creation_eq_shift h,
    ContinuousLinearMap.comp_assoc]

/-- Arbitrary distinct words of the same length have orthogonal creation
ranges. Unreduced words cause no exception: their creators vanish. -/
theorem createWord_inner_zero (u v : List (Letter α))
    (hlen : u.length = v.length) (hne : u ≠ v) (f g : WordHilbert α E) :
    inner ℂ (createWord u f) (createWord v g) = 0 := by
  induction u generalizing v f g with
  | nil => cases v <;> simp_all
  | cons s u ih =>
    cases v with
    | nil => simp at hlen
    | cons t v =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      by_cases hst : s = t
      · subst t
        have huv : u ≠ v := fun h => hne (by rw [h])
        cases u with
        | nil => cases v <;> simp_all
        | cons a u =>
          cases v with
          | nil => simp at hlen
          | cons b v =>
            by_cases ha : flip s = a
            · subst a; rw [createWord_flip_zero]; simp
            by_cases hb : flip s = b
            · subst b; rw [createWord_flip_zero]; simp
            rw [createWord_cons_eq_shift ha, createWord_cons_eq_shift hb]
            simp only [ContinuousLinearMap.comp_apply]
            rw [leftRegular_inner]
            exact ih _ hlen huv _ _
      · exact creation_inner_zero hst _ _

/-- Bounded coefficient operators commute with arbitrary word creation. -/
theorem lift_createWord_commute [Fintype α] (B : E →L[ℂ] E) (w : List (Letter α)) :
    (liftOperator B).comp (createWord w) = (createWord w).comp (liftOperator B) := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [createWord_cons, ← ContinuousLinearMap.comp_assoc, lift_creation_commute,
      ContinuousLinearMap.comp_assoc, ih, ← ContinuousLinearMap.comp_assoc]

end Words
end Nonadditivity.ProductHaagerupCreation
