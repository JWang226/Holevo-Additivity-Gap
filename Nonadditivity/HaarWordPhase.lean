/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMixedMoments
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! # Phase selection for traces of arbitrary Haar words

Independent scalar phases annihilate every word whose signed number of
occurrences of some generator is nonzero. These are actual word evaluations
and actual integrals in every finite dimension; the degree is unrestricted.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Nonadditivity.HaarWordPhase
open MeasureTheory HaarModel HaarFourthMoments
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}

/-- Independent normalized Haar matrices, one for each generator. -/
def wordMeasure (α : Type*) [Fintype α] (N : ℕ) :
    Measure (α → LocalUnitary N) := Measure.pi (fun _ => haar N)

instance : IsProbabilityMeasure (wordMeasure α N) := by
  unfold wordMeasure
  infer_instance

instance : (wordMeasure α N).IsMulLeftInvariant := by
  unfold wordMeasure
  infer_instance

/-- Scalar multiplication by a complex number on the unit circle. -/
def scalarPhase (z : ℂ) (hz : star z*z=1) : LocalUnitary N :=
  ⟨Matrix.diagonal (fun _ => z), by
    change (starRingEnd ℂ) z*z=1 at hz
    rw [Unitary.mem_iff]
    constructor <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal] <;>
      ext r s <;> by_cases h : r=s <;> simp [h,hz,mul_comm z,Matrix.one_apply]⟩

@[simp] theorem scalarPhase_mul (z : ℂ) (hz : star z*z=1) (U : LocalUnitary N) :
    ((scalarPhase (N := N) z hz * U : LocalUnitary N) : Mat N) = z • (U : Mat N) := by
  ext r s
  change (Matrix.diagonal (fun _ : Fin (N+1) => z) * (U : Mat N)) r s = _
  simp [Matrix.diagonal_mul]

/-- Change the phase of one chosen generator, leaving the others fixed. -/
def coordinatePhase (a : α) (z : ℂ) (hz : star z*z=1) : α → LocalUnitary N :=
  fun b => if b=a then scalarPhase z hz else 1

omit [Fintype α] in
@[simp] theorem coordinatePhase_mul (a b : α) (z : ℂ) (hz : star z*z=1)
    (U : α → LocalUnitary N) :
    (((coordinatePhase (N := N) a z hz * U) b : LocalUnitary N) : Mat N) =
      (if b=a then z else 1) • (U b : Mat N) := by
  change (((if b=a then scalarPhase (N := N) z hz else 1) * U b : LocalUnitary N) : Mat N)=_
  split_ifs with h
  · exact scalarPhase_mul z hz (U b)
  · simp

/-- Positive occurrences in a literal word. -/
def positiveCount (a : α) (l : List (α × Bool)) : ℕ := l.count (a,true)
/-- Negative occurrences in a literal word. -/
def negativeCount (a : α) (l : List (α × Bool)) : ℕ := l.count (a,false)

omit [Fintype α] [DecidableEq α] in
lemma eval_cons (U : α → LocalUnitary N) (a : α) (b : Bool)
    (l : List (α × Bool)) :
    ((FreeGroup.lift U (FreeGroup.mk ((a,b)::l)) : LocalUnitary N) : Mat N) =
      (if b then (U a : Mat N) else (U a : Mat N)ᴴ) *
        ((FreeGroup.lift U (FreeGroup.mk l) : LocalUnitary N) : Mat N) := by
  cases b <;> simp [FreeGroup.lift_mk,Matrix.star_eq_conjTranspose]

omit [Fintype α] in
/-- Arbitrary words acquire exactly their signed phase multiplicities. -/
theorem eval_coordinatePhase_mk (a : α) (z : ℂ) (hz : star z*z=1)
    (U : α → LocalUnitary N) (l : List (α × Bool)) :
    ((FreeGroup.lift (coordinatePhase (N := N) a z hz * U) (FreeGroup.mk l) : LocalUnitary N) : Mat N) =
      (z^(positiveCount a l) * (star z)^(negativeCount a l)) •
        ((FreeGroup.lift U (FreeGroup.mk l) : LocalUnitary N) : Mat N) := by
  induction l with
  | nil => simp [positiveCount,negativeCount,FreeGroup.lift_mk]
  | cons x l ih =>
    rcases x with ⟨b,t⟩
    rw [eval_cons,eval_cons,ih,coordinatePhase_mul]
    cases t <;> by_cases h : b=a <;>
      simp [positiveCount,negativeCount,h,
        Matrix.conjTranspose_smul,smul_smul,pow_succ] <;>
      congr 1 <;> ring

/-- Normalized trace of an actual Haar word. -/
def normalizedWordTrace (w : FreeGroup α) (U : α → LocalUnitary N) : ℂ :=
  ((FreeGroup.lift U w : LocalUnitary N) : Mat N).trace / (N+1 : ℂ)

omit [Fintype α] in
lemma normalizedWordTrace_coordinatePhase (a : α) (z : ℂ) (hz : star z*z=1)
    (w : FreeGroup α) (U : α → LocalUnitary N) :
    normalizedWordTrace w (coordinatePhase (N := N) a z hz * U) =
      (z^(positiveCount a w.toWord) * (star z)^(negativeCount a w.toWord)) *
        normalizedWordTrace w U := by
  unfold normalizedWordTrace
  have h := eval_coordinatePhase_mk a z hz U w.toWord
  rw [FreeGroup.mk_toWord] at h
  rw [h,Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- A nonzero signed occurrence count forces the actual expected trace to vanish. -/
theorem integral_normalizedWordTrace_eq_zero_of_unbalanced
    (w : FreeGroup α) (a : α)
    (ha : positiveCount a w.toWord ≠ negativeCount a w.toWord) :
    (∫ U, normalizedWordTrace w U ∂wordMeasure α N)=0 := by
  let p := positiveCount a w.toWord
  let q := negativeCount a w.toWord
  let m := p+q+1
  have hm : m ≠ 0 := by dsimp [m]; omega
  let z := Complex.exp (2 * Real.pi * Complex.I / m)
  have hzprim : IsPrimitiveRoot z m := Complex.isPrimitiveRoot_exp m hm
  have hznorm : ‖z‖=1 := hzprim.norm'_eq_one hm
  have hz : star z*z=1 := by
    rw [Complex.star_def,←Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq,hznorm]
    norm_num
  have hne : z^p ≠ z^q := fun h => ha (hzprim.pow_inj (by dsimp [m]; omega)
    (by dsimp [m]; omega) h)
  have h := integral_mul_left_eq_self (μ := wordMeasure α N)
    (normalizedWordTrace w) (coordinatePhase a z hz)
  simp_rw [normalizedWordTrace_coordinatePhase,integral_const_mul] at h
  have hzq : (star z)^q*z^q=1 := by rw [←mul_pow,hz,one_pow]
  have he : z^p*(∫ U, normalizedWordTrace w U ∂wordMeasure α N)=
      z^q*(∫ U, normalizedWordTrace w U ∂wordMeasure α N) := by
    calc
      _ = z^p*(((star z)^q*z^q)*(∫ U, normalizedWordTrace w U ∂wordMeasure α N)) := by
        rw [hzq,one_mul]
      _ = z^q*((z^p*(star z)^q)*(∫ U, normalizedWordTrace w U ∂wordMeasure α N)) := by ring
      _ = _ := by rw [h]
  exact (mul_eq_mul_right_iff.mp he).resolve_left hne

omit [Fintype α] in
/-- Evaluation of a fixed word is continuous in all its unitary arguments. -/
theorem continuous_wordEval (w : FreeGroup α) :
    Continuous (fun U : α → LocalUnitary N => FreeGroup.lift U w) := by
  have hl : ∀ l : List (α × Bool), Continuous
      (fun U : α → LocalUnitary N => FreeGroup.lift U (FreeGroup.mk l)) := by
    intro l
    induction l with
    | nil => simpa using
        (continuous_const : Continuous (fun _ : α → LocalUnitary N => (1 : LocalUnitary N)))
    | cons x l ih =>
      simp only [FreeGroup.lift_mk,List.map_cons,List.prod_cons] at ih ⊢
      apply Continuous.mul _ ih
      cases hx : x.2
      · exact (continuous_apply x.1).inv
      · exact continuous_apply x.1
  simpa only [FreeGroup.mk_toWord] using hl w.toWord

omit [Fintype α] in
/-- Every normalized word trace is a continuous scalar random variable. -/
theorem continuous_normalizedWordTrace (w : FreeGroup α) :
    Continuous (normalizedWordTrace (N := N) w) := by
  have hc := continuous_subtype_val.comp (continuous_wordEval (N := N) w)
  apply Continuous.div_const
  exact continuous_finset_sum _ (fun i _ => hc.matrix_elem i i)

/-- Compactness supplies the integrability used in finite word expansions. -/
theorem integrable_normalizedWordTrace (w : FreeGroup α) :
    Integrable (normalizedWordTrace w) (wordMeasure α N) :=
  (continuous_normalizedWordTrace w).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Signed multiplicity of a generator in the reduced word. -/
def exponentSum (a : α) (w : FreeGroup α) : ℤ :=
  (positiveCount a w.toWord : ℤ) - (negativeCount a w.toWord : ℤ)

/-- The Haar trace vanishes whenever a generator has nonzero exponent sum. -/
theorem integral_normalizedWordTrace_eq_zero_of_exponentSum_ne_zero
    (w : FreeGroup α) (a : α) (ha : exponentSum a w ≠ 0) :
    (∫ U, normalizedWordTrace w U ∂wordMeasure α N)=0 := by
  apply integral_normalizedWordTrace_eq_zero_of_unbalanced w a
  intro he
  exact ha (by simp [exponentSum,he])

lemma sum_counts (l : List (α × Bool)) :
    (∑ a, (positiveCount a l + negativeCount a l))=l.length := by
  have h := Multiset.sum_count_eq_card (s := Finset.univ)
    (m := (l : Multiset (α × Bool))) (fun _ _ => Finset.mem_univ _)
  simpa [positiveCount,negativeCount,Fintype.sum_prod_type,add_comm, List.count_eq_countP, Bool.beq_eq_decide_eq] using h

/-- A word balanced in every generator necessarily has even length. -/
lemma even_length_of_balanced (l : List (α × Bool))
    (h : ∀ a, positiveCount a l=negativeCount a l) : Even l.length := by
  have hs := sum_counts l
  simp_rw [← h] at hs
  rw [Finset.sum_add_distrib] at hs
  exact ⟨∑ a, positiveCount a l,hs.symm⟩

/-- Odd reduced-word lengths contribute exactly zero at every matrix size. -/
theorem integral_normalizedWordTrace_eq_zero_of_odd
    (w : FreeGroup α) (hw : Odd (FreeGroup.norm w)) :
    (∫ U, normalizedWordTrace w U ∂wordMeasure α N)=0 := by
  have hex : ∃ a, positiveCount a w.toWord ≠ negativeCount a w.toWord := by
    by_contra! h
    obtain ⟨j,hj⟩ := even_length_of_balanced w.toWord h
    obtain ⟨k,hk⟩ := hw
    change w.toWord.length = 2*k+1 at hk
    omega
  obtain ⟨a,ha⟩ := hex
  exact integral_normalizedWordTrace_eq_zero_of_unbalanced w a ha

end Nonadditivity.HaarWordPhase
