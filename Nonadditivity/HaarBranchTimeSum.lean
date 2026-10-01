/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarBranchContractions
import Nonadditivity.HaarPathRuns
import Mathlib.Algebra.BigOperators.Fin

/-! # Exact time-allocation sums for branch contractions

All durations are constructed and counted. The last duration is determined
by the total, giving the essential `L^(r-1)` count. Only marked factors incur
additional time powers.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarNonbacktracking
open scoped BigOperators InnerProduct
open NoncommutativeCS

/-- Positive durations represented by their predecessors, with exact total. -/
abbrev Durations (L r : ℕ) := {t : Fin r → Fin L // ∑ i, ((t i:ℕ)+1) = L}

theorem durations_drop_injective (L r : ℕ) :
    Function.Injective (fun t : Durations L (r+1) => fun i : Fin r => t.val i.succ) := by
  intro t u h
  apply Subtype.ext
  have ht := t.property
  have hu := u.property
  rw [Fin.sum_univ_succ] at ht hu
  have htail : (∑ i : Fin r, ((t.val i.succ:ℕ)+1)) =
      ∑ i : Fin r, ((u.val i.succ:ℕ)+1) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun f : Fin r → Fin L => (f i:ℕ)+1) h
  funext i
  refine Fin.cases ?_ (fun j => congrFun h j) i
  apply Fin.ext
  omega

theorem card_durations_le (L r : ℕ) (hr : 0 < r) :
    Fintype.card (Durations L r) ≤ L^(r-1) := by
  cases r with
  | zero => omega
  | succ r =>
    simpa using Fintype.card_le_of_injective
      (fun t : Durations L (r+1) => fun i : Fin r => t.val i.succ)
      (durations_drop_injective L r)

namespace BranchPlan
variable {G J : Type*} {m n : ℕ}

def blocks {m n : ℕ} : BranchPlan G J m n → ℕ
  | .identity _ => 0
  | .openReg _ _ _ _ _ => 1
  | .closeReg _ _ _ _ _ => 1
  | .middle _ _ _ _ => 1
  | .singleton _ _ _ _ _ => 1
  | .comp Q P => Q.blocks + P.blocks

/-- Change only the positive time assigned to each actual branch factor. -/
def retime {m n : ℕ} : (P : BranchPlan G J m n) →
    (Fin P.blocks → ℕ) → BranchPlan G J m n
  | .identity n, _ => .identity n
  | .openReg p g _ w hw, t => .openReg p g (t ⟨0,by simp [blocks]⟩) w hw
  | .closeReg p g _ w hw, t => .closeReg p g (t ⟨0,by simp [blocks]⟩) w hw
  | .middle n g _ w, t => .middle n g (t ⟨0,by simp [blocks]⟩) w
  | .singleton n g _ w hw, t => .singleton n g (t ⟨0,by simp [blocks]⟩) w hw
  | .comp Q P, t =>
      (Q.retime (fun i => t (Fin.castAdd P.blocks i))).comp
        (P.retime (fun i => t (Fin.natAdd Q.blocks i)))

theorem marked_retime (P : BranchPlan G J m n) (t : Fin P.blocks → ℕ) :
    (P.retime t).marked = P.marked := by
  induction P with
  | identity => rfl
  | openReg => rfl
  | closeReg => rfl
  | middle => rfl
  | singleton => rfl
  | comp Q P hQ hP => simp only [retime, marked, hQ, hP]

theorem singletons_retime (P : BranchPlan G J m n) (t : Fin P.blocks → ℕ) :
    (P.retime t).singletons = P.singletons := by
  induction P with
  | identity => rfl
  | openReg => rfl
  | closeReg => rfl
  | middle => rfl
  | singleton => rfl
  | comp Q P hQ hP => simp only [retime, singletons, hQ, hP]

theorem order_retime (P : BranchPlan G J m n) (t : Fin P.blocks → ℕ) :
    (P.retime t).order = ∑ i, (t i+1) := by
  induction P with
  | identity => simp [retime, order, blocks]
  | openReg => simp [retime, order, blocks]
  | closeReg => simp [retime, order, blocks]
  | middle => simp [retime, order, blocks]
  | singleton => simp [retime, order, blocks]
  | comp Q P hQ hP =>
    simp only [retime, order, hQ, hP]
    exact (Fin.sum_univ_add (fun i : Fin (Q.blocks+P.blocks) => t i+1)).symm

variable {E : Type*} [Group G] [DecidableEq G] [Fintype J] [DecidableEq J]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Literal finite sum of the actual coefficient contractions over all
positive segment durations adding to `L`. -/
def timeSum (A : H G E →L[ℂ] H G E) (P : BranchPlan G J m n)
    (s : Fin n → J) (t : Fin m → J) (L : ℕ) : E →L[ℂ] E :=
  ∑ τ : Durations L P.blocks,
    ((P.retime (fun i => (τ.val i:ℕ))).realize A).pathSum s t

theorem timeSum_norm_le {A : H G E →L[ℂ] H G E} (hA : IsStationary A)
    (P : BranchPlan G J m n) (hP : 0 < P.blocks)
    (s : Fin n → J) (t : Fin m → J) (L : ℕ) :
    ‖timeSum A P s t L‖ ≤ (L:ℝ)^(P.blocks-1+P.marked) * ‖A‖^L *
      (Real.sqrt (Fintype.card J:ℝ))^P.singletons := by
  have hb (τ : Durations L P.blocks) :
      ‖((P.retime (fun i => (τ.val i:ℕ))).realize A).pathSum s t‖ ≤
        (L:ℝ)^P.marked * ‖A‖^L * (Real.sqrt (Fintype.card J:ℝ))^P.singletons := by
    have ho : (P.retime (fun i => (τ.val i:ℕ))).order = L :=
      (order_retime _ _).trans τ.property
    simpa only [marked_retime, singletons_retime, ho] using
      pathSum_norm_le hA (P.retime (fun i => (τ.val i:ℕ))) s t L ho.le
  have hc : (Fintype.card (Durations L P.blocks):ℝ) ≤ (L:ℝ)^(P.blocks-1) := by
    exact_mod_cast card_durations_le L P.blocks hP
  calc
    _ ≤ ∑ τ : Durations L P.blocks,
        ‖((P.retime (fun i => (τ.val i:ℕ))).realize A).pathSum s t‖ := norm_sum_le _ _
    _ ≤ ∑ _τ : Durations L P.blocks,
        (L:ℝ)^P.marked * ‖A‖^L * (Real.sqrt (Fintype.card J:ℝ))^P.singletons :=
      Finset.sum_le_sum (fun τ _ => hb τ)
    _ = (Fintype.card (Durations L P.blocks):ℝ) *
        ((L:ℝ)^P.marked * ‖A‖^L * (Real.sqrt (Fintype.card J:ℝ))^P.singletons) := by simp
    _ ≤ (L:ℝ)^(P.blocks-1) *
        ((L:ℝ)^P.marked * ‖A‖^L * (Real.sqrt (Fintype.card J:ℝ))^P.singletons) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The corrected first/last-visit count supplies the required polynomial
exponent, without using the false intermediate bound on the number of runs. -/
theorem timeSum_norm_le_of_markers {A : H G E →L[ℂ] H G E} (hA : IsStationary A)
    (P : BranchPlan G J m n) (hP : 0 < P.blocks)
    (s : Fin n → J) (t : Fin m → J) (L : ℕ) (hL : 1 ≤ L)
    (flags : List Bool) (e : ℕ) (hhead : flags.head?=some true)
    (hmarks : flags.count true ≤ 2*e)
    (hblocks : P.blocks = HaarPathRuns.blockCount flags)
    (hmarked : P.marked = flags.count true) :
    ‖timeSum A P s t L‖ ≤ (L:ℝ)^(6*e-2) * ‖A‖^L *
      (Real.sqrt (Fintype.card J:ℝ))^P.singletons := by
  have he : P.blocks-1+P.marked ≤ 6*e-2 := by
    rw [hblocks,hmarked]
    exact HaarPathRuns.corrected_exponent_le hhead hmarks
  apply (timeSum_norm_le hA P hP s t L).trans
  have hp : (L:ℝ)^(P.blocks-1+P.marked) ≤ (L:ℝ)^(6*e-2) :=
    pow_le_pow_right₀ (by exact_mod_cast hL) he
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)

/-- A regular-polynomial version with its stationarity premise discharged. -/
theorem regular_timeSum_norm_le {I : Type*} [Fintype I]
    (v : I → G) (a : I → E →L[ℂ] E)
    (P : BranchPlan G J m n) (hP : 0 < P.blocks)
    (s : Fin n → J) (t : Fin m → J) (L : ℕ) :
    ‖timeSum (MatrixRegularRestriction.coefficientPolynomial v a) P s t L‖ ≤
      (L:ℝ)^(P.blocks-1+P.marked) *
        ‖MatrixRegularRestriction.coefficientPolynomial v a‖^L *
          (Real.sqrt (Fintype.card J:ℝ))^P.singletons :=
  timeSum_norm_le (stationary_regularPolynomial v a) P hP s t L

end BranchPlan
end Nonadditivity.HaarNonbacktracking
