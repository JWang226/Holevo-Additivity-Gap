/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductPolynomialReduction
import Mathlib.Data.Nat.Log

/-! # Constructed balanced tensor-coordinate factorization

Residue classes modulo `2^j` form a balanced partition of the coordinates.
Each class splits into two at the next level.  The constructed supports
include both signs and have the manuscript's `1 + 2^(j+1) K^ceil(n/2^j)` bound.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nonadditivity.TensorPartitionReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open PolynomialReduction ProductPolynomialReduction

variable {α : Type} [DecidableEq α] {n K : ℕ} [NeZero K]

/-- Integer ceiling of the number of coordinates per residue class. -/
def width (n j : ℕ) : ℕ := (n + 2^j - 1) / 2^j

theorem quotient_lt_width (i : Fin n) (j : ℕ) : i.val / 2^j < width n j := by
  have hp : 0 < 2^j := by positivity
  unfold width
  have hi := Nat.mul_div_le i.val (2^j)
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le hp).mpr
  have hsub : n + 2^j - 1 + 1 = n + 2^j := Nat.sub_add_cancel (by omega)
  nlinarith [i.isLt]

/-- The positive word on one part of the coordinate partition. -/
def partWord (v : Fin n → Fin K → FreeGroup α) (j : ℕ) (t : Fin (2^j))
    (a : Fin n → Fin K) : GroupWord α n :=
  fun i => if i.val % 2^j = t.val then v i (a i) else 1

/-- An equivalent coding using only `ceil(n/2^j)` local choices. -/
def codedWord (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (c : Fin (2^j) × (Fin (width n j) → Fin K)) : GroupWord α n :=
  fun i => if i.val % 2^j = c.1.val then
    v i (c.2 ⟨i.val / 2^j, quotient_lt_width i j⟩) else 1

/-- Extract local choices from a full coordinate assignment. -/
def restrictChoices (j : ℕ) (t : Fin (2^j)) (a : Fin n → Fin K) :
    Fin (width n j) → Fin K :=
  fun q => if h : t.val + 2^j * q.val < n then a ⟨_,h⟩ else 0

theorem partWord_eq_codedWord (v : Fin n → Fin K → FreeGroup α)
    (j : ℕ) (t : Fin (2^j)) (a : Fin n → Fin K) :
    partWord v j t a = codedWord v j (t, restrictChoices j t a) := by
  funext i
  dsimp only [partWord, codedWord]
  split_ifs with h
  · congr 1
    have hi : t.val + 2^j * (i.val / 2^j) = i.val := by
      simpa only [h] using Nat.mod_add_div i.val (2^j)
    simp only [restrictChoices]
    split_ifs with hh
    · congr 1
      exact Fin.ext hi.symm
    · omega
  · rfl

/-- The actual finite support at partition level `j`. -/
def stageSupport (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    Finset (GroupWord α n) :=
  insert 1 ((Finset.univ.image (codedWord v j)) ∪
    Finset.univ.image (fun c => (codedWord v j c)⁻¹))

@[simp] theorem one_mem_stageSupport (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    (1 : GroupWord α n) ∈ stageSupport v j := by simp [stageSupport]

theorem partWord_mem (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (t : Fin (2^j)) (a : Fin n → Fin K) : partWord v j t a ∈ stageSupport v j := by
  rw [partWord_eq_codedWord]
  simp [stageSupport]

theorem inv_partWord_mem (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (t : Fin (2^j)) (a : Fin n → Fin K) : (partWord v j t a)⁻¹ ∈ stageSupport v j := by
  rw [partWord_eq_codedWord]
  simp [stageSupport]

theorem codedWord_eq_partWord (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (c : Fin (2^j) × (Fin (width n j) → Fin K)) :
    codedWord v j c = partWord v j c.1 (fun i => c.2 ⟨_,quotient_lt_width i j⟩) := rfl

theorem mem_stageSupport_iff (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (w : GroupWord α n) : w ∈ stageSupport v j ↔
    w = 1 ∨ ∃ t : Fin (2^j), ∃ a : Fin n → Fin K,
      w = partWord v j t a ∨ w = (partWord v j t a)⁻¹ := by
  constructor
  · intro hw
    simp only [stageSupport, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hw
    rcases hw with h | ⟨c,h⟩ | ⟨c,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨c.1, _, Or.inl (h.symm.trans (codedWord_eq_partWord v j c))⟩
    · exact Or.inr ⟨c.1, _, Or.inr (h.symm.trans (congrArg Inv.inv (codedWord_eq_partWord v j c)))⟩
  · rintro (rfl | ⟨t,a,rfl | rfl⟩)
    · exact one_mem_stageSupport v j
    · exact partWord_mem v j t a
    · exact inv_partWord_mem v j t a

/-- The exact manuscript cardinal budget, proved for the constructed support. -/
theorem stageSupport_card (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    (stageSupport v j).card ≤ 1 + 2^(j+1) * K^(width n j) := by
  let T := Fin (2^j) × (Fin (width n j) → Fin K)
  have hcard : Fintype.card T = 2^j * K^(width n j) := by simp [T]
  calc
    (stageSupport v j).card ≤
        ((Finset.univ.image (codedWord v j)) ∪
          Finset.univ.image (fun c => (codedWord v j c)⁻¹)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (Finset.univ.image (codedWord v j)).card +
        (Finset.univ.image (fun c => (codedWord v j c)⁻¹)).card + 1 :=
      Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ Fintype.card T + Fintype.card T + 1 := by
      exact Nat.add_le_add_right (Nat.add_le_add Finset.card_image_le Finset.card_image_le) 1
    _ = _ := by rw [hcard, pow_succ]; ring


/-- A parent residue class is the disjoint union of its two children. -/
theorem residue_split (i m t : ℕ) (hm : 0 < m) (ht : t < m) :
    i % m = t ↔ i % (2*m) = t ∨ i % (2*m) = t+m := by
  have hmod : i % (2*m) % m = i % m :=
    Nat.mod_mod_of_dvd i ⟨2, by omega⟩
  have hr := Nat.mod_lt i (show 0 < 2*m by omega)
  rcases lt_or_ge (i % (2*m)) m with h | h
  · rw [Nat.mod_eq_of_lt h] at hmod
    omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show i % (2*m)-m < m by omega)] at hmod
    omega

def leftChild {j : ℕ} (t : Fin (2^j)) : Fin (2^(j+1)) :=
  ⟨t.val, by have := t.isLt; rw [pow_succ]; omega⟩

def rightChild {j : ℕ} (t : Fin (2^j)) : Fin (2^(j+1)) :=
  ⟨t.val+2^j, by have := t.isLt; rw [pow_succ]; omega⟩

/-- Splitting uses only commutation of distinct coordinates, encoded pointwise. -/
theorem partWord_split (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (t : Fin (2^j)) (a : Fin n → Fin K) :
    partWord v j t a =
      partWord v (j+1) (leftChild t) a * partWord v (j+1) (rightChild t) a := by
  funext i
  have hp : 0 < 2^j := by positivity
  have hs := residue_split i.val (2^j) t.val hp t.isLt
  have he : 2^(j+1) = 2*2^j := by rw [pow_succ]; omega
  simp only [partWord, Pi.mul_apply, leftChild, rightChild, he]
  by_cases h₁ : i.val % (2*2^j) = t.val
  · have h₂ : ¬ i.val % (2*2^j) = t.val+2^j := by omega
    simp [h₁, hs.mpr (Or.inl h₁)]
  · by_cases h₂ : i.val % (2*2^j) = t.val+2^j
    · simp [h₂, hs.mpr (Or.inr h₂)]
    · have h₀ : ¬ i.val % 2^j = t.val := by simpa [h₁,h₂] using hs
      simp [h₁,h₂,h₀]

/-- Every word and inverse at one stage is a difference of two words at the next. -/
theorem stage_difference_cover (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    stageSupport v j ⊆ Linearization.differenceSupport (stageSupport v (j+1)) := by
  intro w hw
  rcases (mem_stageSupport_iff v j w).mp hw with rfl | ⟨t,a,rfl | rfl⟩
  · exact Linearization.mem_differenceSupport.mpr
      ⟨1, one_mem_stageSupport v (j+1), 1, one_mem_stageSupport v (j+1), by simp⟩
  · apply Linearization.mem_differenceSupport.mpr
    refine ⟨(partWord v (j+1) (leftChild t) a)⁻¹,
      inv_partWord_mem _ _ _ _, partWord v (j+1) (rightChild t) a,
      partWord_mem _ _ _ _, ?_⟩
    simpa only [inv_inv] using (partWord_split v j t a).symm
  · apply Linearization.mem_differenceSupport.mpr
    refine ⟨partWord v (j+1) (rightChild t) a, partWord_mem _ _ _ _,
      (partWord v (j+1) (leftChild t) a)⁻¹, inv_partWord_mem _ _ _ _, ?_⟩
    rw [partWord_split v j t a, mul_inv_rev]

/-- The original individual tensor words lie in the initial support. -/
theorem initial_support_subset (v : Fin n → Fin K → FreeGroup α) :
    Finset.univ.image (fun a : Fin n → Fin K => fun i => v i (a i)) ⊆
      stageSupport v 0 := by
  intro w hw
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hw
  have he : partWord v 0 (0 : Fin (2^0)) a = (fun i => v i (a i)) := by
    funext i
    change (if i.val % 1 = 0 then v i (a i) else 1) = v i (a i)
    rw [Nat.mod_one]
    rfl
  rw [← he]
  exact partWord_mem v 0 0 a


/-- At the last partition level, each word acts in only one factor. -/
theorem stageSupport_single_factor (v : Fin n → Fin K → FreeGroup α) (j ℓ : ℕ)
    (hn : 1 ≤ n) (hnj : n ≤ 2^j)
    (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ℓ) :
    ∀ w ∈ stageSupport v j, ∃ i : Fin n, ∃ g : FreeGroup α,
      FreeGroup.norm g ≤ ℓ ∧ w = fun k => if k=i then g else 1 := by
  have hpart (t : Fin (2^j)) (a : Fin n → Fin K) :
      ∃ i : Fin n, ∃ g : FreeGroup α, FreeGroup.norm g ≤ ℓ ∧
        partWord v j t a = fun k => if k=i then g else 1 := by
    by_cases ht : t.val < n
    · let i : Fin n := ⟨t.val,ht⟩
      refine ⟨i, v i (a i), hv _ _, ?_⟩
      funext k
      have hk : k.val < 2^j := k.isLt.trans_le hnj
      simp only [partWord, Nat.mod_eq_of_lt hk]
      by_cases hki : k=i
      · subst k
        simp [i]
      · have hne : k.val ≠ t.val := by intro h; exact hki (Fin.ext h)
        simp [hne,hki]
    · refine ⟨⟨0,by omega⟩,1,by simp,?_⟩
      funext k
      have hk : k.val < 2^j := k.isLt.trans_le hnj
      have hne : k.val ≠ t.val := by have := k.isLt; omega
      simp [partWord, Nat.mod_eq_of_lt hk,hne]
  intro w hw
  rcases (mem_stageSupport_iff v j w).mp hw with rfl | ⟨t,a,rfl | rfl⟩
  · refine ⟨⟨0,by omega⟩,1,by simp,?_⟩
    funext k
    simp
  · exact hpart t a
  · obtain ⟨i,g,hg,heq⟩ := hpart t a
    refine ⟨i,g⁻¹,by simpa using hg,?_⟩
    rw [heq]
    funext k
    simp only [Pi.inv_apply]
    split_ifs <;> simp

/-- The actual stage sequence, with freshly constructed coefficient matrices. -/
def reduce (v : Fin n → Fin K → FreeGroup α) (P : Polynomial (GroupWord α n)) :
    ℕ → Polynomial (GroupWord α n)
  | 0 => P
  | j+1 => (reduce v P j).step (stageSupport v (j+1)) (one_mem_stageSupport v (j+1))

/-- Actual enlargement factor accumulated along the constructed sequence. -/
def dimensionCost (v : Fin n → Fin K → FreeGroup α) : ℕ → ℕ
  | 0 => 1
  | j+1 => 2*(stageSupport v (j+1)).card * dimensionCost v j

/-- Actual relative-error factor accumulated along the constructed sequence. -/
def errorCost (v : Fin n → Fin K → FreeGroup α) : ℕ → ℕ
  | 0 => 1
  | j+1 => 6*(stageSupport v (j+1)).card * errorCost v j

theorem dimensionCost_pos (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    0 < dimensionCost v j := by
  induction j with
  | zero => simp [dimensionCost]
  | succ j ih =>
    have hb := Finset.card_pos.mpr ⟨1, one_mem_stageSupport v (j+1)⟩
    exact Nat.mul_pos (Nat.mul_pos (by omega) hb) ih

theorem errorCost_eq (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    errorCost v j = 3^j * dimensionCost v j := by
  induction j with
  | zero => simp [errorCost,dimensionCost]
  | succ j ih => simp only [errorCost,dimensionCost,ih,pow_succ]; ring

theorem errorCost_pos (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    0 < errorCost v j := by
  rw [errorCost_eq]
  exact Nat.mul_pos (by positivity) (dimensionCost_pos v j)

theorem reduce_dimension (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (j : ℕ) :
    Fintype.card (reduce v P j).Index = Fintype.card P.Index * dimensionCost v j := by
  induction j with
  | zero => simp [reduce,dimensionCost]
  | succ j ih =>
    rw [reduce,Polynomial.step_dimension,ih]
    simp only [dimensionCost]
    ring

theorem reduce_support (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (hP : P.support ⊆ stageSupport v 0) (j : ℕ) :
    (reduce v P j).support ⊆ stageSupport v j := by
  cases j with
  | zero => exact hP
  | succ j => exact Finset.Subset.refl _

/-- Every constructed Gram step has its exact regular norm identity. -/
theorem reduce_regular_norm_sq (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (hP : P.support ⊆ stageSupport v 0) (j : ℕ) :
    ‖(reduce v P (j+1)).regularEval‖^2 = ‖(reduce v P j).regularEval‖ +
      (reduce v P j).correction (stageSupport v (j+1)) :=
  Polynomial.step_regular_norm_sq _ _ (one_mem_stageSupport v (j+1))
    ((reduce_support v P hP j).trans (stage_difference_cover v j))

/-- The same constructed coefficients satisfy the finite norm identity. -/
theorem reduce_finite_norm_sq (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (hP : P.support ⊆ stageSupport v 0) (j : ℕ)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : GroupWord α n →* unitary (Matrix ν ν ℂ)) :
    ‖(reduce v P (j+1)).finiteEval π‖^2 = ‖(reduce v P j).finiteEval π‖ +
      (reduce v P j).correction (stageSupport v (j+1)) :=
  Polynomial.step_finite_norm_sq _ _ (one_mem_stageSupport v (j+1))
    ((reduce_support v P hP j).trans (stage_difference_cover v j)) π

/-- The additive constants have the required actual support-cardinality bound. -/
theorem reduce_correction_bounds (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (hP : P.support ⊆ stageSupport v 0) (j : ℕ) :
    0 ≤ (reduce v P j).correction (stageSupport v (j+1)) ∧
    (reduce v P j).correction (stageSupport v (j+1)) ≤
      ((stageSupport v (j+1)).card : ℝ) * ‖(reduce v P j).regularEval‖ :=
  ⟨Polynomial.correction_nonneg _ _,
    Polynomial.correction_le _ _ (one_mem_stageSupport v (j+1))
      ((reduce_support v P hP j).trans (stage_difference_cover v j))⟩


/-- Only the final-polynomial norm comparison is assumed; all intermediate
support covers and all backward error transfers are proved for the construction. -/
theorem reduce_error_transfer (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (hP : P.support ⊆ stageSupport v 0) (j : ℕ)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : GroupWord α n →* unitary (Matrix ν ν ℂ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : ‖(reduce v P j).finiteEval π‖ ≤
      (1+ε/(errorCost v j:ℝ))*‖(reduce v P j).regularEval‖) :
    ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  induction j with
  | zero => simpa only [reduce,errorCost,Nat.cast_one,div_one] using hfinal
  | succ j ih =>
    have hE : (0:ℝ) < errorCost v (j+1) := by exact_mod_cast errorCost_pos v (j+1)
    have hE1 : (1:ℝ) ≤ errorCost v (j+1) := by exact_mod_cast errorCost_pos v (j+1)
    have hδ0 : 0 ≤ ε/(errorCost v (j+1):ℝ) := div_nonneg hε hE.le
    have hδ1 : ε/(errorCost v (j+1):ℝ) ≤ 1 := by
      exact (div_le_iff₀ hE).mpr (by linarith)
    have hs := Polynomial.step_error_transfer (reduce v P j) (stageSupport v (j+1))
      (one_mem_stageSupport v (j+1))
      ((reduce_support v P hP j).trans (stage_difference_cover v j)) π
      (ε/(errorCost v (j+1):ℝ)) hδ0 hδ1 hfinal
    have hB : (0:ℝ) < (stageSupport v (j+1)).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1,one_mem_stageSupport v (j+1)⟩
    have hEprev : (0:ℝ) < errorCost v j := by exact_mod_cast errorCost_pos v j
    have heq : 6*((stageSupport v (j+1)).card:ℝ)*(ε/(errorCost v (j+1):ℝ)) =
        ε/(errorCost v j:ℝ) := by
      simp only [errorCost,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
    apply ih
    simpa only [heq] using hs

theorem dimensionCost_prod (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    dimensionCost v j = ∏ i ∈ Finset.range j, 2*(stageSupport v (i+1)).card := by
  induction j with
  | zero => simp [dimensionCost]
  | succ j ih => rw [dimensionCost,Finset.prod_range_succ,ih,Nat.mul_comm]

theorem errorCost_prod (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    errorCost v j = ∏ i ∈ Finset.range j, 6*(stageSupport v (i+1)).card := by
  induction j with
  | zero => simp [errorCost]
  | succ j ih => rw [errorCost,Finset.prod_range_succ,ih,Nat.mul_comm]

/-- Manuscript product budget for the actual coefficient dimensions. -/
theorem dimensionCost_le_prod (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    dimensionCost v j ≤
      ∏ i ∈ Finset.range j, 2*(1+2^(i+2)*K^(width n (i+1))) := by
  rw [dimensionCost_prod]
  apply Finset.prod_le_prod'
  intro i hi
  exact Nat.mul_le_mul_left 2 (stageSupport_card v (i+1))

/-- Manuscript product budget for the actual backward-error transfer. -/
theorem errorCost_le_prod (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    errorCost v j ≤
      ∏ i ∈ Finset.range j, 6*(1+2^(i+2)*K^(width n (i+1))) := by
  rw [errorCost_prod]
  apply Finset.prod_le_prod'
  intro i hi
  exact Nat.mul_le_mul_left 6 (stageSupport_card v (i+1))

/-- A complete constructed tensor-factor reduction with the manuscript's support
budgets and exactly `ceil(log₂ n)` stages. The output acts on single factors. -/
theorem constructed_tensor_reduction (v : Fin n → Fin K → FreeGroup α)
    (P : Polynomial (GroupWord α n)) (hP : P.support ⊆ stageSupport v 0)
    (ℓ : ℕ) (hn : 1 ≤ n) (hv : ∀ i a, FreeGroup.norm (v i a) ≤ ℓ) :
    ∃ Q : Polynomial (GroupWord α n),
      (∀ w ∈ Q.support, ∃ i : Fin n, ∃ g : FreeGroup α,
        FreeGroup.norm g ≤ ℓ ∧ w = fun k => if k=i then g else 1) ∧
      Fintype.card Q.Index = Fintype.card P.Index * dimensionCost v (Nat.clog 2 n) ∧
      errorCost v (Nat.clog 2 n) = 3^(Nat.clog 2 n) * dimensionCost v (Nat.clog 2 n) ∧
      ∀ {ν : Type} [Fintype ν] [DecidableEq ν] [Nonempty ν]
        (π : GroupWord α n →* unitary (Matrix ν ν ℂ)) (ε : ℝ),
        0 ≤ ε → ε ≤ 1 →
        ‖Q.finiteEval π‖ ≤ (1+ε/(errorCost v (Nat.clog 2 n):ℝ))*‖Q.regularEval‖ →
        ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  refine ⟨reduce v P (Nat.clog 2 n), ?_, reduce_dimension _ _ _, errorCost_eq _ _, ?_⟩
  · intro w hw
    exact stageSupport_single_factor v _ ℓ hn (Nat.le_pow_clog (by omega) n) hv w
      (reduce_support v P hP _ hw)
  · intro ν _ _ _ π ε hε hε1 hfinal
    exact reduce_error_transfer v P hP _ π ε hε hε1 hfinal

end Nonadditivity.TensorPartitionReduction
