/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductPolynomialReduction
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Log

/-! Actual balls of reduced words in one tensor factor and their Gram reductions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.WordBallReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open PolynomialReduction
open Linearization

abbrev F₂ := FreeGroup (Fin 2)
abbrev G (n : ℕ) := Fin n → F₂

def letter (a : Letter) : Fin 2 × Bool := ![(0,true),(1,true),(1,false),(0,false)] a

def code (a : Fin 2 × Bool) : Letter :=
  if a.1=0 then (if a.2 then 0 else 3) else (if a.2 then 1 else 2)

@[simp] theorem letter_code (a : Fin 2 × Bool) : letter (code a) = a := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> cases b <;> decide

@[simp] theorem code_letter (a : Letter) : code (letter a) = a := by fin_cases a <;> decide

theorem legal_iff (a b : Letter) :
    b ≠ inverseLetter a ↔ ((letter a).1 = (letter b).1 → (letter a).2 = (letter b).2) := by
  fin_cases a <;> fin_cases b <;> decide

def tailLetters (a : Letter) : (t : ℕ) → ReducedTail a t → List (Fin 2 × Bool)
  | 0, _ => []
  | t+1, ⟨b,w⟩ => letter b.val :: tailLetters b.val t w

theorem length_tailLetters (a : Letter) (t : ℕ) (w : ReducedTail a t) :
    (tailLetters a t w).length = t := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih => rcases w with ⟨b,w⟩; simp [tailLetters, ih]

def wordLetters {t : ℕ} (w : ReducedWord t) : List (Fin 2 × Bool) :=
  letter w.1 :: tailLetters w.1 t w.2

@[simp] theorem length_wordLetters {t : ℕ} (w : ReducedWord t) :
    (wordLetters w).length = t+1 := by simp [wordLetters, length_tailLetters]

theorem exists_tail (l : List (Fin 2 × Bool)) (a : Letter)
    (hl : FreeGroup.IsReduced (letter a :: l)) :
    ∃ w : ReducedTail a l.length, tailLetters a l.length w = l := by
  induction l generalizing a with
  | nil => exact ⟨(),rfl⟩
  | cons b l ih =>
    have hb := (FreeGroup.isReduced_cons_cons.mp hl).1
    have hr := (FreeGroup.isReduced_cons_cons.mp hl).2
    have hlegal : code b ≠ inverseLetter a := (legal_iff a (code b)).mpr (by simpa using hb)
    obtain ⟨w,hw⟩ := ih (code b) (by simpa using hr)
    exact ⟨⟨⟨code b,hlegal⟩,w⟩, by simp [tailLetters, hw]⟩

theorem exists_word (l : List (Fin 2 × Bool)) (hl : FreeGroup.IsReduced l)
    (hlen : l.length = t+1) : ∃ w : ReducedWord t, wordLetters w = l := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    have heq : l.length = t := by simpa using hlen
    subst t
    obtain ⟨w,hw⟩ := exists_tail l (code a) (by simpa using hl)
    exact ⟨⟨code a,w⟩,by simp [wordLetters,hw]⟩

abbrev WordIndex (r : ℕ) := Σ t : Fin r, ReducedWord t.val

def wordValue {r : ℕ} (w : WordIndex r) : F₂ := FreeGroup.mk (wordLetters w.2)

theorem wordValue_norm_le {r : ℕ} (w : WordIndex r) : FreeGroup.norm (wordValue w) ≤ r := by
  exact FreeGroup.norm_mk_le.trans (by simp)

def single {n : ℕ} (j : Fin n) (v : F₂) : G n := fun k => if k=j then v else 1

@[simp] theorem single_one {n : ℕ} (j : Fin n) : single j 1 = 1 := by ext k; simp [single]
@[simp] theorem single_inv {n : ℕ} (j : Fin n) (v : F₂) : single j v⁻¹ = (single j v)⁻¹ := by
  ext k; by_cases h:k=j <;> simp [single,h]
@[simp] theorem single_mul {n : ℕ} (j : Fin n) (v w : F₂) :
    single j (v*w) = single j v * single j w := by
  ext k; by_cases h:k=j <;> simp [single,h]

def wordBall (n r : ℕ) : Finset (G n) :=
  insert 1 (Finset.univ.image (fun x : Fin n × WordIndex r => single x.1 (wordValue x.2)))

@[simp] theorem one_mem_wordBall (n r : ℕ) : (1:G n) ∈ wordBall n r := by simp [wordBall]

def SingleFactorBound {n : ℕ} (r : ℕ) (w : G n) : Prop :=
  ∃ j : Fin n, ∃ v : F₂, FreeGroup.norm v ≤ r ∧ w = single j v

theorem mem_wordBall_of_bound {n r : ℕ} {w : G n} (hw : SingleFactorBound r w) :
    w ∈ wordBall n r := by
  rcases hw with ⟨j,v,hv,rfl⟩
  by_cases h:v=1
  · simp [h]
  · have hpos : 0 < v.toWord.length := by
      by_contra hh
      have he : v.toWord=[] := List.length_eq_zero_iff.mp (by omega)
      exact h (FreeGroup.toWord_eq_nil_iff.mp he)
    obtain ⟨u,hu⟩ := exists_word v.toWord FreeGroup.isReduced_toWord
      (show v.toWord.length = (v.toWord.length-1)+1 by omega)
    have ht : v.toWord.length-1 < r := by change v.toWord.length ≤ r at hv; omega
    have he : wordValue (⟨⟨v.toWord.length-1,ht⟩,u⟩ : WordIndex r) = v := by
      simp [wordValue,hu,FreeGroup.mk_toWord]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨⟨j,⟨⟨_,ht⟩,u⟩⟩,Finset.mem_univ _,by simp only [he]⟩

theorem bound_of_mem_wordBall {n r : ℕ} (hn : 1≤n) {w : G n} (hw : w ∈ wordBall n r) :
    SingleFactorBound r w := by
  simp only [wordBall,Finset.mem_insert,Finset.mem_image] at hw
  rcases hw with rfl | ⟨⟨j,u⟩,_,rfl⟩
  · exact ⟨⟨0,by omega⟩,1,by simp,by simp⟩
  · exact ⟨j,wordValue u,wordValue_norm_le u,rfl⟩

theorem card_wordBall_le (n r : ℕ) (hn : 1≤n) : (wordBall n r).card ≤ 2*n*3^r := by
  have hcard : Fintype.card (WordIndex r) = ∑ t ∈ Finset.range r,4*3^t := by
    rw [Fintype.card_sigma]
    simp only [card_reducedWord]
    exact Fin.sum_univ_eq_sum_range (fun t => 4*3^t) r
  calc
    (wordBall n r).card ≤ (Finset.univ.image
        (fun x : Fin n × WordIndex r => single x.1 (wordValue x.2))).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ Fintype.card (Fin n × WordIndex r) + 1 := Nat.add_le_add_right
      (Finset.card_image_le.trans (by simp)) 1
    _ = 1+n*(∑ t ∈ Finset.range r,4*3^t) := by simp [hcard]; omega
    _ ≤ 2*n*3^r := short_word_count_bound n r hn

theorem bound_split {n r : ℕ} {w : G n} (hw : SingleFactorBound (2*r) w) :
    w ∈ Linearization.differenceSupport (wordBall n r) := by
  rcases hw with ⟨j,v,hv,rfl⟩
  apply Linearization.mem_differenceSupport.mpr
  refine ⟨single j (firstHalf r v)⁻¹,?_,single j (suffix r v),?_,?_⟩
  · apply mem_wordBall_of_bound
    exact ⟨j,(firstHalf r v)⁻¹,by simpa using norm_firstHalf_le r v,rfl⟩
  · exact mem_wordBall_of_bound ⟨j,suffix r v,norm_suffix_le r v hv,rfl⟩
  · simp only [single_inv,inv_inv,←single_mul,firstHalf_mul_suffix]

/-- The manuscript's ceiling of the word length divided by a power of two. -/
def radius (ell i : ℕ) : ℕ := ell ⌈/⌉ (2^i)

@[simp] theorem radius_zero (ell : ℕ) : radius ell 0 = ell := by simp [radius]

theorem radius_halve (ell i : ℕ) : radius ell i ≤ 2 * radius ell (i+1) := by
  unfold radius
  apply (ceilDiv_le_iff_le_mul (show 0 < (2:ℕ)^i by positivity)).mpr
  have h := le_smul_ceilDiv (b := ell) (show 0 < (2:ℕ)^(i+1) by positivity)
  simpa [smul_eq_mul,pow_succ,mul_assoc] using h

theorem radius_le_one (ell i : ℕ) (h : ell ≤ 2^i) : radius ell i ≤ 1 := by
  exact (ceilDiv_le_iff_le_mul (show 0 < (2:ℕ)^i by positivity)).mpr (by simpa using h)

theorem SingleFactorBound.mono {n r s : ℕ} {w : G n}
    (hw : SingleFactorBound r w) (hrs : r≤s) : SingleFactorBound s w := by
  rcases hw with ⟨j,v,hv,heq⟩
  exact ⟨j,v,hv.trans hrs,heq⟩

/-- Every shortening step uses the entire actual one-factor reduced-word ball. -/
def stage {n : ℕ} (P : Polynomial (G n)) (ell : ℕ) : ℕ → Polynomial (G n)
  | 0 => P
  | i+1 => (stage P ell i).step (wordBall n (radius ell (i+1))) (one_mem_wordBall _ _)

def dimensionCost (n ell : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => dimensionCost n ell i * (2 * (wordBall n (radius ell (i+1))).card)

def errorCost (n ell : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => errorCost n ell i * (6 * (wordBall n (radius ell (i+1))).card)

theorem dimensionCost_pos (n ell i : ℕ) : 0 < dimensionCost n ell i := by
  induction i with
  | zero => simp [dimensionCost]
  | succ i ih =>
    exact Nat.mul_pos ih (Nat.mul_pos (by omega)
      (Finset.card_pos.mpr ⟨1,one_mem_wordBall _ _⟩))

theorem errorCost_eq (n ell i : ℕ) : errorCost n ell i = 3^i * dimensionCost n ell i := by
  induction i with
  | zero => simp [errorCost,dimensionCost]
  | succ i ih => simp only [errorCost,dimensionCost,ih,pow_succ]; ring

theorem errorCost_pos (n ell i : ℕ) : 0 < errorCost n ell i := by
  rw [errorCost_eq]
  exact Nat.mul_pos (by positivity) (dimensionCost_pos n ell i)

theorem dimensionCost_product (n ell i : ℕ) : dimensionCost n ell i =
    ∏ j ∈ Finset.range i, 2 * (wordBall n (radius ell (j+1))).card := by
  induction i with
  | zero => simp [dimensionCost]
  | succ i ih => simp [dimensionCost,Finset.prod_range_succ,ih]

theorem errorCost_product (n ell i : ℕ) : errorCost n ell i =
    ∏ j ∈ Finset.range i, 6 * (wordBall n (radius ell (j+1))).card := by
  induction i with
  | zero => simp [errorCost]
  | succ i ih => simp [errorCost,Finset.prod_range_succ,ih]

theorem dimensionCost_le (n ell i : ℕ) (hn : 1≤n) : dimensionCost n ell i ≤
    ∏ j ∈ Finset.range i, 4*n*3^(radius ell (j+1)) := by
  rw [dimensionCost_product]
  apply Finset.prod_le_prod'
  intro j _
  have h := Nat.mul_le_mul_left 2 (card_wordBall_le n (radius ell (j+1)) hn)
  nlinarith

theorem errorCost_le (n ell i : ℕ) (hn : 1≤n) : errorCost n ell i ≤
    ∏ j ∈ Finset.range i, 12*n*3^(radius ell (j+1)) := by
  rw [errorCost_product]
  apply Finset.prod_le_prod'
  intro j _
  have h := Nat.mul_le_mul_left 6 (card_wordBall_le n (radius ell (j+1)) hn)
  nlinarith

theorem stage_dimension {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) :
    Fintype.card (stage P ell i).Index = Fintype.card P.Index * dimensionCost n ell i := by
  induction i with
  | zero => simp [stage,dimensionCost]
  | succ i ih =>
    rw [stage,Polynomial.step_dimension,ih]
    simp only [dimensionCost]
    ring

theorem stage_bound {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w) :
    ∀ w ∈ (stage P ell i).support, SingleFactorBound (radius ell i) w := by
  cases i with
  | zero => simpa only [stage,radius_zero] using hP
  | succ i => exact fun w hw => bound_of_mem_wordBall hn hw

theorem stage_cover {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w) :
    (stage P ell i).support ⊆ Linearization.differenceSupport (wordBall n (radius ell (i+1))) := by
  intro w hw
  exact bound_split ((stage_bound P ell i hn hP w hw).mono (radius_halve ell i))

theorem stage_finite_norm_sq {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G n →* unitary (Matrix ν ν ℂ)) :
    ‖(stage P ell (i+1)).finiteEval π‖^2 = ‖(stage P ell i).finiteEval π‖ +
      (stage P ell i).correction (wordBall n (radius ell (i+1))) :=
  Polynomial.step_finite_norm_sq _ _ _ (stage_cover P ell i hn hP) π

theorem stage_regular_norm_sq {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w) :
    ‖(stage P ell (i+1)).regularEval‖^2 = ‖(stage P ell i).regularEval‖ +
      (stage P ell i).correction (wordBall n (radius ell (i+1))) :=
  Polynomial.step_regular_norm_sq _ _ _ (stage_cover P ell i hn hP)

theorem stage_correction_le {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w) :
    (stage P ell i).correction (wordBall n (radius ell (i+1))) ≤
      ((wordBall n (radius ell (i+1))).card : ℝ) * ‖(stage P ell i).regularEval‖ :=
  Polynomial.correction_le _ _ (one_mem_wordBall _ _) (stage_cover P ell i hn hP)

theorem stage_error_transfer {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : G n →* unitary (Matrix ν ν ℂ)) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (hfinal : ‖(stage P ell i).finiteEval π‖ ≤
      (1+ε/(errorCost n ell i:ℝ))*‖(stage P ell i).regularEval‖) :
    ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  induction i with
  | zero => simpa only [stage,errorCost,Nat.cast_one,div_one] using hfinal
  | succ i ih =>
    let B := (wordBall n (radius ell (i+1))).card
    have hB : 0 < B := Finset.card_pos.mpr ⟨1,one_mem_wordBall _ _⟩
    have hE : 0 < errorCost n ell (i+1) := errorCost_pos n ell (i+1)
    have hEreal : (1:ℝ) ≤ errorCost n ell (i+1) := by exact_mod_cast hE
    have hδ0 : 0 ≤ ε/(errorCost n ell (i+1):ℝ) := div_nonneg hε (by positivity)
    have hδ1 : ε/(errorCost n ell (i+1):ℝ) ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    have hstep := Polynomial.step_error_transfer (stage P ell i)
      (wordBall n (radius ell (i+1))) (one_mem_wordBall _ _)
      (stage_cover P ell i hn hP) π (ε/(errorCost n ell (i+1):ℝ)) hδ0 hδ1 hfinal
    apply ih
    have hBreal : (B:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
    have heq : 6*(B:ℝ)*(ε/(errorCost n ell (i+1):ℝ)) = ε/(errorCost n ell i:ℝ) := by
      simp only [errorCost,Nat.cast_mul,Nat.cast_ofNat]
      change 6*(B:ℝ)*(ε/((errorCost n ell i:ℝ)*(6*(B:ℝ)))) = _
      field_simp
    simpa only [heq,B] using hstep

theorem degree_single {n : ℕ} (j : Fin n) (v : F₂) :
    ProductPolynomialReduction.degree (single j v) = FreeGroup.norm v := by
  simp [ProductPolynomialReduction.degree,single,apply_ite FreeGroup.norm]

theorem final_linear {n : ℕ} (P : Polynomial (G n)) (ell i : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w) (hell : ell ≤ 2^i) :
    ∀ w ∈ (stage P ell i).support, w=1 ∨ ∃ x : Fin n × Fin 2,
      w=ProductPolynomialReduction.generator x ∨ w=(ProductPolynomialReduction.generator x)⁻¹ := by
  intro w hw
  apply ProductPolynomialReduction.degree_le_one_letters
  rcases stage_bound P ell i hn hP w hw with ⟨j,v,hv,rfl⟩
  rw [degree_single]
  exact hv.trans (radius_le_one ell i hell)

/-- The number of word-shortening steps specified in the manuscript suffices. -/
theorem stage_clog_linear {n : ℕ} (P : Polynomial (G n)) (ell : ℕ) (hn : 1≤n)
    (hP : ∀ w ∈ P.support, SingleFactorBound ell w) :
    ∀ w ∈ (stage P ell (Nat.clog 2 ell)).support, w=1 ∨ ∃ x : Fin n × Fin 2,
      w=ProductPolynomialReduction.generator x ∨ w=(ProductPolynomialReduction.generator x)⁻¹ :=
  final_linear P ell _ hn hP (Nat.le_pow_clog (by omega) ell)

end Nonadditivity.WordBallReduction
