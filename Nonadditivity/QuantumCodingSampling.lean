/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Finite independent random codebooks and their exact marginal averages -/

noncomputable section
namespace Nonadditivity.QuantumCoding.Sampling
open scoped BigOperators

variable {α J : Type*} [Fintype α] [Fintype J] [DecidableEq J]

def weight (p : α → ℝ) (c : J → α) : ℝ := ∏ i, p (c i)

def expect (p : α → ℝ) (f : (J → α) → ℝ) : ℝ := ∑ c, weight p c * f c

omit [Fintype α] [DecidableEq J] in
theorem weight_nonneg (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (c : J → α) :
    0 ≤ weight p c := Finset.prod_nonneg (fun i _ => hp (c i))

theorem weight_sum (p : α → ℝ) (hsum : ∑x, p x = 1) :
    ∑ c : J → α, weight p c = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp only [hsum, Finset.prod_const_one]

theorem expect_const (p : α → ℝ) (hsum : ∑x, p x = 1) (r : ℝ) :
    expect p (fun _ : J → α => r) = r := by
  rw [expect, ← Finset.sum_mul, weight_sum p hsum, one_mul]

theorem expect_add (p : α → ℝ) (f g : (J → α) → ℝ) :
    expect p (fun c => f c + g c) = expect p f + expect p g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sum {K : Type*} [Fintype K] (p : α → ℝ)
    (f : K → (J → α) → ℝ) : expect p (fun c => ∑ k, f k c) = ∑ k, expect p (f k) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_finset_sum {K : Type*} (p : α → ℝ) (s : Finset K)
    (f : K → (J → α) → ℝ) :
    expect p (fun c => ∑ k ∈ s, f k c) = ∑ k ∈ s, expect p (f k) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_mul_const (p : α → ℝ) (f : (J → α) → ℝ) (a : ℝ) :
    expect p (fun c => a * f c) = a * expect p f := by
  simp only [expect, Finset.mul_sum]
  congr 1
  funext c
  ring

theorem expect_mono (p : α → ℝ) (hp : ∀x, 0 ≤ p x)
    {f g : (J → α) → ℝ} (h : ∀c, f c ≤ g c) : expect p f ≤ expect p g :=
  Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (h c) (weight_nonneg p hp c))

theorem expect_product (p : α → ℝ) (f : J → α → ℝ) :
    expect p (fun c => ∏ i, f i (c i)) = ∏ i, ∑x, p x * f i x := by
  simp only [expect, weight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => p x * f i x)).symm

theorem expect_one (p : α → ℝ) (hsum : ∑x, p x = 1) (i : J) (f : α → ℝ) :
    expect p (fun c => f (c i)) = ∑x, p x * f x := by
  have h := expect_product p (fun j x => if j = i then f x else 1)
  simpa only [Fintype.prod_ite_eq', mul_ite, mul_one,
    Finset.sum_ite_irrel, hsum] using h

theorem expect_two_product (p : α → ℝ) (hsum : ∑x, p x = 1)
    {i j : J} (hij : i ≠ j) (f g : α → ℝ) :
    expect p (fun c => f (c i) * g (c j)) =
      (∑x, p x * f x) * (∑y, p y * g y) := by
  have h := expect_product p
    (fun k x => (if k = i then f x else 1) * (if k = j then g x else 1))
  have hprod (c : J → α) :
      (∏ k, (if k = i then f (c k) else 1) * (if k = j then g (c k) else 1)) =
        f (c i) * g (c j) := by
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  have hsum' (k : J) :
      (∑x, p x * ((if k = i then f x else 1) * (if k = j then g x else 1))) =
        (if k = i then ∑x, p x * f x else 1) *
        (if k = j then ∑x, p x * g x else 1) := by
    by_cases hi : k=i
    · subst k
      simp only [ite_true, if_neg hij, mul_one]
    · by_cases hj : k=j
      · subst k
        simp only [if_neg hi, ite_true, one_mul]
      · simp only [if_neg hi, if_neg hj, mul_one, hsum]
  simp_rw [hprod, hsum'] at h
  simpa only [Finset.prod_mul_distrib, Fintype.prod_ite_eq'] using h

theorem expect_two (p : α → ℝ) (hsum : ∑x, p x = 1)
    {i j : J} (hij : i ≠ j) (f : α → α → ℝ) :
    expect p (fun c => f (c i) (c j)) = ∑x, ∑y, p x * p y * f x y := by
  classical
  have hexp (c : J → α) : f (c i) (c j) =
      ∑x, ∑y, f x y * ((if c i = x then 1 else 0) * (if c j = y then 1 else 0)) := by
    simp
  simp_rw [hexp]
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [expect_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [expect_mul_const, expect_two_product p hsum hij
    (fun z => if z=x then 1 else 0) (fun z => if z=y then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- A finite probability average has at least one outcome no larger than it. -/
theorem exists_le_expect (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    (f : (J → α) → ℝ) : ∃c, f c ≤ expect p f := by
  classical
  by_contra h
  push_neg at h
  have hnonempty : Nonempty (J → α) := by
    have hs := weight_sum (J := J) p hsum
    by_contra hne
    letI : IsEmpty (J → α) := not_nonempty_iff.mp hne
    simp at hs
  letI := hnonempty
  obtain ⟨c, hcmem, hc⟩ := Finset.exists_lt_of_sum_lt
    (show (∑ _c : J → α, (0 : ℝ)) < ∑ c : J → α, weight p c by
      rw [weight_sum p hsum]; simp)
  have hs : expect p f < expect p f := by
    calc
      expect p f = ∑ c : J → α, weight p c * expect p f := by
        rw [← Finset.sum_mul, weight_sum p hsum, one_mul]
      _ < ∑ c, weight p c * f c := by
        apply Finset.sum_lt_sum
        · intro a _
          exact mul_le_mul_of_nonneg_left (h a).le (weight_nonneg p hp a)
        · exact ⟨c, hcmem, mul_lt_mul_of_pos_left (h c) hc⟩
      _ = expect p f := rfl
  exact (lt_irrefl _) hs

/-- The explicit three-term cost of an independently sampled finite codebook. -/
def codebookCost {M : ℕ} (f g : α → ℝ) (cross : α → α → ℝ) (c : Fin M → α) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, (9*f (c i) + 8*g (c i) +
    4*∑ j ∈ Finset.univ.erase i, cross (c i) (c j))

theorem expect_codebookCost_le (p : α → ℝ) (hsum : ∑x, p x = 1)
    {M : ℕ} (hM : 0 < M) (f g : α → ℝ) (cross : α → α → ℝ)
    {εf εg β : ℝ} (hf : ∑x, p x * f x ≤ εf) (hg : ∑x, p x * g x ≤ εg)
    (hc : ∑x, ∑y, p x * p y * cross x y ≤ β) :
    expect p (codebookCost (M := M) f g cross) ≤ 9*εf+8*εg+4*(M-1:ℕ)*β := by
  have hlocal (i : Fin M) :
      expect p (fun c : Fin M → α => 9*f (c i)+8*g (c i)+
        4*∑ j ∈ Finset.univ.erase i, cross (c i) (c j)) ≤ 9*εf+8*εg+4*(M-1:ℕ)*β := by
    rw [expect_add, expect_add, expect_mul_const, expect_mul_const, expect_mul_const,
      expect_one p hsum, expect_one p hsum, expect_finset_sum]
    have hcross : (∑ j ∈ Finset.univ.erase i,
        expect p (fun c : Fin M → α => cross (c i) (c j))) ≤ (M-1:ℕ)*β := by
      calc
        _ ≤ ∑ j ∈ Finset.univ.erase i, β := by
          apply Finset.sum_le_sum
          intro j hj
          rw [expect_two p hsum (Ne.symm (Finset.mem_erase.mp hj).1) cross]
          exact hc
        _ = (M-1:ℕ)*β := by simp
    linarith
  unfold codebookCost
  rw [expect_mul_const, expect_sum]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  calc
    _ ≤ (M : ℝ)⁻¹ * ∑ _i : Fin M, (9*εf+8*εg+4*(M-1:ℕ)*β) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

theorem exists_codebook_cost_le (p : α → ℝ) (hp : ∀x, 0 ≤ p x) (hsum : ∑x, p x = 1)
    {M : ℕ} (hM : 0 < M) (f g : α → ℝ) (cross : α → α → ℝ)
    {εf εg β : ℝ} (hf : ∑x, p x * f x ≤ εf) (hg : ∑x, p x * g x ≤ εg)
    (hc : ∑x, ∑y, p x * p y * cross x y ≤ β) :
    ∃c : Fin M → α, codebookCost f g cross c ≤ 9*εf+8*εg+4*(M-1:ℕ)*β := by
  obtain ⟨c, hc⟩ := exists_le_expect p hp hsum (codebookCost (M := M) f g cross)
  exact ⟨c, hc.trans (expect_codebookCost_le p hsum hM f g cross hf hg ‹_›)⟩

end Nonadditivity.QuantumCoding.Sampling
