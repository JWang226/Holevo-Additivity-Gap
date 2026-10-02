/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingTypicality

/-! # Conditional entropy typicality for finite classical-quantum alphabets

The estimate is an actual average over input words and conditional eigenvalue
words. It follows from independent sampling on their joint alphabet, with no
full-support or assumed concentration estimate.
-/
noncomputable section
namespace Nonadditivity.QuantumCodingConditionalTypicality
open QuantumCodingTypicality
open scoped BigOperators
variable {α ι : Type*} [Fintype α] [Fintype ι]

def conditionalWord (lam : α → ι → ℝ) (n : ℕ) (x : Fin n → α) (z : Fin n → ι) : ℝ :=
  ∏ j, lam (x j) (z j)

def jointDistribution (p : α → ℝ) (lam : α → ι → ℝ) (y : α × ι) : ℝ := p y.1 * lam y.1 y.2

def conditionalInformation (lam : α → ι → ℝ) (y : α × ι) : ℝ := information (lam y.1) y.2

def conditionalEntropy (p : α → ℝ) (lam : α → ι → ℝ) : ℝ := ∑ a, p a * entropy (lam a)

def conditionalVariance (p : α → ℝ) (lam : α → ι → ℝ) : ℝ :=
  letterVariance (jointDistribution p lam) (conditionalInformation lam)

omit [Fintype α] [Fintype ι] in
theorem conditionalWord_nonneg (lam : α → ι → ℝ) (hlam : ∀ a i, 0 ≤ lam a i)
    (n : ℕ) (x : Fin n → α) (z : Fin n → ι) : 0 ≤ conditionalWord lam n x z :=
  Finset.prod_nonneg (fun j _ => hlam (x j) (z j))

omit [Fintype α] in
theorem conditionalWord_sum (lam : α → ι → ℝ) (hlam : ∀ a, ∑ i, lam a i = 1)
    (n : ℕ) (x : Fin n → α) : ∑ z, conditionalWord lam n x z = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ι))
    (fun j i => lam (x j) i)
  simpa [conditionalWord, hlam] using h.symm

theorem jointDistribution_sum (p : α → ℝ) (lam : α → ι → ℝ)
    (hp : ∑ a, p a = 1) (hlam : ∀ a, ∑ i, lam a i = 1) :
    ∑ y, jointDistribution p lam y = 1 := by
  simp only [jointDistribution, Fintype.sum_prod_type, ←Finset.mul_sum, hlam, mul_one, hp]

theorem joint_mean (p : α → ℝ) (lam : α → ι → ℝ) :
    letterMean (jointDistribution p lam) (conditionalInformation lam) = conditionalEntropy p lam := by
  simp only [letterMean, jointDistribution, conditionalInformation, Fintype.sum_prod_type,
    mul_assoc, ←Finset.mul_sum, information_mean, conditionalEntropy]

def wordPairEquiv (n : ℕ) : (Fin n → α) × (Fin n → ι) ≃ (Fin n → α × ι) where
  toFun x := fun j => (x.1 j,x.2 j)
  invFun y := (fun j => (y j).1, fun j => (y j).2)
  left_inv x := by cases x; rfl
  right_inv y := by funext j; rfl

theorem sum_paired_words (n : ℕ) (F : (Fin n → α × ι) → ℝ) :
    ∑ y, F y = ∑ x : Fin n → α, ∑ z : Fin n → ι, F (fun j => (x j,z j)) := by
  rw [←(wordPairEquiv (α := α) (ι := ι) n).sum_comp F]
  simp only [Fintype.sum_prod_type, wordPairEquiv, Equiv.coe_fn_mk]

omit [Fintype α] [Fintype ι] in
theorem joint_word_factorization (p : α → ℝ) (lam : α → ι → ℝ)
    (n : ℕ) (y : Fin n → α × ι) :
    wordProbability (jointDistribution p lam) n y =
      wordProbability p n (fun j => (y j).1) *
        conditionalWord lam n (fun j => (y j).1) (fun j => (y j).2) := by
  simp only [wordProbability, conditionalWord, jointDistribution, Finset.prod_mul_distrib]

/-- Exact reindexing of the joint product law into input words and conditional
eigenvalue words, including a literal event on the two words. -/
theorem joint_event_mass (p : α → ℝ) (lam : α → ι → ℝ) (n : ℕ)
    (B : (Fin n → α) → (Fin n → ι) → Prop) [DecidablePred (fun y : Fin n → α × ι =>
      B (fun j => (y j).1) (fun j => (y j).2))] [∀ x, DecidablePred (B x)] :
    (∑ y ∈ Finset.univ.filter (fun y : Fin n → α × ι =>
      B (fun j => (y j).1) (fun j => (y j).2)), wordProbability (jointDistribution p lam) n y) =
      ∑ x : Fin n → α, wordProbability p n x *
        ∑ z ∈ Finset.univ.filter (B x), conditionalWord lam n x z := by
  classical
  simp only [Finset.sum_filter]
  rw [sum_paired_words]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [joint_word_factorization]
  split_ifs <;> simp

omit [Fintype α] [Fintype ι] in
theorem log_conditionalWord (lam : α → ι → ℝ) (n : ℕ) (y : Fin n → α × ι)
    (hy : conditionalWord lam n (fun j => (y j).1) (fun j => (y j).2) ≠ 0) :
    Real.log (conditionalWord lam n (fun j => (y j).1) (fun j => (y j).2)) =
      -wordSum (conditionalInformation lam) n y := by
  have hc : ∀ j ∈ (Finset.univ : Finset (Fin n)), lam (y j).1 (y j).2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hy
  rw [conditionalWord, Real.log_prod hc]
  simp only [wordSum, conditionalInformation, information, Finset.sum_neg_distrib, neg_neg]

/-- Positive joint mass and conditional information typicality imply the
actual conditional eigenvalue lies in the required exponential band. -/
theorem conditional_band_of_typical (p : α → ℝ) (lam : α → ι → ℝ)
    (hlam : ∀ a i, 0 ≤ lam a i) (n : ℕ) (δ : ℝ) (y : Fin n → α × ι)
    (hy : wordProbability (jointDistribution p lam) n y ≠ 0)
    (ht : |wordSum (conditionalInformation lam) n y-n*conditionalEntropy p lam| < n*δ) :
    Real.exp (-(n*conditionalEntropy p lam)-n*δ) ≤
        conditionalWord lam n (fun j => (y j).1) (fun j => (y j).2) ∧
      conditionalWord lam n (fun j => (y j).1) (fun j => (y j).2) ≤
        Real.exp (-(n*conditionalEntropy p lam)+n*δ) := by
  have hc : conditionalWord lam n (fun j => (y j).1) (fun j => (y j).2) ≠ 0 := by
    intro hz
    rw [joint_word_factorization, hz, mul_zero] at hy
    exact hy rfl
  have hpos := lt_of_le_of_ne (conditionalWord_nonneg lam hlam n _ _) (Ne.symm hc)
  have hl := log_conditionalWord lam n y hc
  have hd := abs_lt.mp ht
  constructor
  · rw [←Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [←Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)

/-- Conditional typicality with an explicit vanishing error. The right-hand
side is the actual averaged acceptance probability of the conditional
spectral windows. All zero probabilities are included without restriction. -/
theorem average_conditional_band_mass_ge (p : α → ℝ) (lam : α → ι → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (hlam : ∀ a i, 0 ≤ lam a i) (hlams : ∀ a, ∑ i, lam a i = 1)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    1-conditionalVariance p lam/(n*δ^2) ≤
      ∑ x : Fin n → α, wordProbability p n x *
        ∑ z ∈ Finset.univ.filter (fun z : Fin n → ι =>
          Real.exp (-(n*conditionalEntropy p lam)-n*δ) ≤ conditionalWord lam n x z ∧
          conditionalWord lam n x z ≤ Real.exp (-(n*conditionalEntropy p lam)+n*δ)),
          conditionalWord lam n x z := by
  classical
  have hq : ∀ y, 0 ≤ jointDistribution p lam y := fun y => mul_nonneg (hp y.1) (hlam y.1 y.2)
  have ht := wordSum_concentration (jointDistribution p lam) (conditionalInformation lam)
    hq (jointDistribution_sum p lam hs hlams) n hn δ hδ
  rw [joint_mean] at ht
  apply ht.trans
  rw [←joint_event_mass]
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro y _
  by_cases htyp : |wordSum (conditionalInformation lam) n y-n*conditionalEntropy p lam| < n*δ
  · by_cases hz : wordProbability (jointDistribution p lam) n y = 0
    · simp [hz]
    · have hb := conditional_band_of_typical p lam hlam n δ y hz htyp
      simp [htyp,hb]
  · simp only [if_neg htyp]
    split_ifs
    · exact wordProbability_nonneg _ hq n y
    · rfl

end Nonadditivity.QuantumCodingConditionalTypicality
