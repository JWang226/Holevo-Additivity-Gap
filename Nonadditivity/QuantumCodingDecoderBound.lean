/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingTraceUnion
import Nonadditivity.QuantumCodingSequential

/-! # Deterministic error bound for actual sequential decoding

An initial common spectral filter and the individual codeword tests are
controlled by literal trace probabilities on the codeword density matrix.
-/
noncomputable section
namespace Nonadditivity.QuantumCoding
open Entropy Operational
open scoped BigOperators InnerProductSpace Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem reject_norm_le (P : Projection E) (x : E) : ‖x-P.map x‖≤‖x‖ := by
  have hp := P.pythagoras x
  have hn := sq_nonneg ‖P.map x‖
  nlinarith [norm_nonneg (x-P.map x), norm_nonneg x]

/-- The loss of a second projection after filtering is bounded on the
original vector; both terms have the sharp elementary factor two. -/
theorem filtered_reject_norm_sq (G Q : Projection E) (x : E) :
    ‖G.map x-Q.map (G.map x)‖^2 ≤
      2*‖x-Q.map x‖^2+2*‖x-G.map x‖^2 := by
  have hi : G.map x-Q.map (G.map x) =
      (x-Q.map x)-((x-G.map x)-Q.map (x-G.map x)) := by
    rw [map_sub]
    abel
  have hnorm : ‖G.map x-Q.map (G.map x)‖ ≤ ‖x-Q.map x‖+‖x-G.map x‖ := by
    rw [hi]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (Q.reject_norm_le _))
  nlinarith [sq_nonneg (‖x-Q.map x‖-‖x-G.map x‖), norm_nonneg (G.map x-Q.map (G.map x)),
    norm_nonneg (x-Q.map x), norm_nonneg (x-G.map x)]
end Projection

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Two projection failures on an amplitude control the filtered failure. -/
theorem filtered_reject_trace_amplitude (G Q : ProjectiveTest ι) (X : Matrix ι κ ℂ) :
    ((1-Q.matrix)*(G.matrix*(X*X.conjTranspose)*G.matrix)).trace.re ≤
      2*((1-Q.matrix)*(X*X.conjTranspose)).trace.re+
        2*((1-G.matrix)*(X*X.conjTranspose)).trace.re := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Projection.filtered_reject_norm_sq
      (Projection.ofMatrix G.matrix G.hermitian G.idempotent)
      (Projection.ofMatrix Q.matrix Q.hermitian Q.idempotent) (amplitudeColumn X j))
  change (∑ j, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G.matrix (amplitudeColumn X j)-
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) Q.matrix
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G.matrix (amplitudeColumn X j))‖^2) ≤ _ at h
  have hf (j : κ) :
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G.matrix (amplitudeColumn X j)-
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) Q.matrix
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) G.matrix (amplitudeColumn X j)) =
      amplitudeColumn ((1-Q.matrix)*(G.matrix*X)) j := by
    simpa only [amplitudeColumn_mul] using
      (amplitudeColumn_sub_mul Q.matrix (G.matrix*X) j).symm
  have hq (j : κ) : amplitudeColumn X j -
      (Projection.ofMatrix Q.matrix Q.hermitian Q.idempotent).map (amplitudeColumn X j) =
      amplitudeColumn ((1-Q.matrix)*X) j :=
    (amplitudeColumn_sub_mul Q.matrix X j).symm
  have hg (j : κ) : amplitudeColumn X j -
      (Projection.ofMatrix G.matrix G.hermitian G.idempotent).map (amplitudeColumn X j) =
      amplitudeColumn ((1-G.matrix)*X) j :=
    (amplitudeColumn_sub_mul G.matrix X j).symm
  simp_rw [hf,hq,hg] at h
  rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum] at h
  simp_rw [←trace_gram_eq_sum_column_norm_sq,
    rejected_gram_trace Q.matrix Q.hermitian Q.idempotent,
    rejected_gram_trace G.matrix G.hermitian G.idempotent] at h
  simpa only [Matrix.conjTranspose_mul, G.hermitian.eq, Matrix.mul_assoc] using h

/-- Filtering cannot spoil a later projective acceptance by more than twice
either original failure probability. -/
theorem filtered_reject_trace (G Q : ProjectiveTest ι)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    ((1-Q.matrix)*(G.matrix*ρ*G.matrix)).trace.re ≤
      2*((1-Q.matrix)*ρ).trace.re+2*((1-G.matrix)*ρ).trace.re := by
  have hroot : CFC.sqrt ρ * (CFC.sqrt ρ).conjTranspose = ρ := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  simpa only [hroot] using filtered_reject_trace_amplitude G Q (CFC.sqrt ρ)

namespace ProjectiveTest

/-- The raw success effect has a trace error controlled by the original
failure of the target test and false acceptance of earlier tests. -/
theorem raw_error_bound (P : ℕ → ProjectiveTest ι)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (n : ℕ) :
    ρ.trace.re - (ρ * effect P n).trace.re ≤
      4 * (((1-(P n).matrix)*ρ).trace.re +
        ∑ i ∈ Finset.range n, ((P i).matrix*ρ).trace.re) := by
  let A : ℕ → Matrix ι ι ℂ := fun i =>
    if i=n then (P n).matrix else (P i).complement.matrix
  have hA (i : ℕ) : (A i).IsHermitian := by
    dsimp [A]
    split_ifs
    · exact (P n).hermitian
    · exact (P i).complement.hermitian
  have hAA (i : ℕ) : A i*A i=A i := by
    dsimp [A]
    split_ifs
    · exact (P n).idempotent
    · exact (P i).complement.idempotent
  have hprod (k : ℕ) (hk : k≤n) : actualProduct A k=rejectProduct P k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [actualProduct, rejectProduct, ih (by omega)]
      have hkn : k≠n := by omega
      simp [A,hkn,complement]
  have hlast : actualProduct A (n+1)=(P n).matrix*rejectProduct P n := by
    rw [actualProduct, hprod n le_rfl]
    simp [A]
  have hs : (∑ i ∈ Finset.range (n+1), ((1-A i)*ρ).trace.re) =
      (((1-(P n).matrix)*ρ).trace.re +
        ∑ i ∈ Finset.range n, ((P i).matrix*ρ).trace.re) := by
    rw [Finset.sum_range_succ, add_comm]
    congr 1
    · simp [A]
    · apply Finset.sum_congr rfl
      intro i hi
      have hin : i≠n := by have := Finset.mem_range.mp hi; omega
      simp [A,hin,complement]
  have he : (((P n).matrix*rejectProduct P n)*ρ*
      ((P n).matrix*rejectProduct P n).conjTranspose).trace =
      (ρ*effect P n).trace := by
    rw [Matrix.conjTranspose_mul, (P n).hermitian.eq]
    calc
      _ = ((P n).matrix * (rejectProduct P n*ρ*(rejectProduct P n).conjTranspose) *
          (P n).matrix).trace := by simp only [Matrix.mul_assoc]
      _ = (((P n).matrix*(P n).matrix)*
          (rejectProduct P n*ρ*(rejectProduct P n).conjTranspose)).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = ((P n).matrix*(rejectProduct P n*ρ*(rejectProduct P n).conjTranspose)).trace := by
        rw [(P n).idempotent]
      _ = (ρ*effect P n).trace := by
        unfold effect
        rw [Matrix.trace_mul_comm (P n).matrix]
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (rejectProduct P n)]
        simp only [Matrix.mul_assoc]
  have h := trace_union_bound A hA hAA ρ hρ (n+1)
  rwa [hlast,hs,he] at h

/-- The filtered raw decoder has an explicit error estimate on every positive
input. The constants arise from Gao's factor four and one filter triangle bound. -/
theorem filtered_raw_error_bound (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (n : ℕ) :
    ρ.trace.re - (ρ * filteredEffect G P n).trace.re ≤
      9*((1-G.matrix)*ρ).trace.re + 8*((1-(P n).matrix)*ρ).trace.re +
        4*∑ i ∈ Finset.range n, ((P i).matrix*(G.matrix*ρ*G.matrix)).trace.re := by
  have hσ : (G.matrix*ρ*G.matrix).PosSemidef := by
    simpa only [G.hermitian.eq] using hρ.conjTranspose_mul_mul_same G.matrix
  have hraw := raw_error_bound P (G.matrix*ρ*G.matrix) hσ n
  have hf := filtered_reject_trace G (P n) ρ hρ
  have ht : (G.matrix*ρ*G.matrix).trace.re =
      ρ.trace.re-((1-G.matrix)*ρ).trace.re := by
    rw [Matrix.trace_mul_cycle, G.idempotent, Matrix.sub_mul, Matrix.one_mul,
      Matrix.trace_sub, Complex.sub_re]
    ring
  have hs : ((G.matrix*ρ*G.matrix)*effect P n).trace =
      (ρ*filteredEffect G P n).trace := by
    unfold filteredEffect
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm G.matrix]
    simp only [Matrix.mul_assoc]
  rw [ht,hs] at hraw
  linarith

/-- The completed physical POVM obeys the same deterministic error bound on
each normalized input state. -/
theorem filteredDecoder_error_bound (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι)
    (N : ℕ) (hN : 0<N) (ρ : DensityMatrix ι) (i : Fin N) :
    1-(filteredDecoder G P N hN).probability ρ i ≤
      9*((1-G.matrix)*ρ.matrix).trace.re + 8*((1-(P i.val).matrix)*ρ.matrix).trace.re +
        4*∑ j ∈ Finset.range i.val,
          ((P j).matrix*(G.matrix*ρ.matrix*G.matrix)).trace.re := by
  have hb := filtered_raw_error_bound G P ρ.matrix ρ.positive i.val
  have hp := filteredDecoder_probability_ge G P N hN ρ i
  rw [ρ.normalized, Complex.one_re] at hb
  linarith

/-- Extend a finite family of message tests to the index type used by the
sequential product. The fallback is never queried by the finite decoder. -/
def finiteTests {M : ℕ} (Q : Fin M → ProjectiveTest ι) (fallback : ProjectiveTest ι)
    (t : ℕ) : ProjectiveTest ι := if h : t<M then Q ⟨t,h⟩ else fallback

@[simp] theorem finiteTests_apply {M : ℕ} (Q : Fin M → ProjectiveTest ι)
    (fallback : ProjectiveTest ι) (i : Fin M) : finiteTests Q fallback i.val=Q i := by
  simp [finiteTests,i.isLt]

private theorem prefix_sum_le_erase_sum {M : ℕ} (f : Fin M → ℝ)
    (hf : ∀j, 0≤f j) (i : Fin M) :
    (∑ j : Fin i.val, f ⟨j.val,j.isLt.trans i.isLt⟩) ≤
      ∑ j ∈ Finset.univ.erase i, f j := by
  let e : Fin i.val → Fin M := fun j => ⟨j.val,j.isLt.trans i.isLt⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin M => z.val) hab)
  have hs : Finset.univ.image e ⊆ Finset.univ.erase i := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨a,ha,rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hai
    have hva := congrArg Fin.val hai
    change a.val=i.val at hva
    exact (Nat.ne_of_lt a.isLt) hva
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => hf j)
  rw [Finset.sum_image (fun a _ b _ hab => he hab)] at hb
  exact hb

/-- The physical filtered decoder is controlled by the interference from all
other messages. This symmetric form is suitable for random-codebook averaging. -/
theorem finite_filteredDecoder_error_bound {M : ℕ} (hM : 0<M)
    (G : ProjectiveTest ι) (Q : Fin M → ProjectiveTest ι)
    (ρ : DensityMatrix ι) (i : Fin M) :
    1-(filteredDecoder G (finiteTests Q G) M hM).probability ρ i ≤
      9*((1-G.matrix)*ρ.matrix).trace.re + 8*((1-(Q i).matrix)*ρ.matrix).trace.re +
        4*∑ j ∈ Finset.univ.erase i,
          ((Q j).matrix*(G.matrix*ρ.matrix*G.matrix)).trace.re := by
  have hb := filteredDecoder_error_bound G (finiteTests Q G) M hM ρ i
  simp only [finiteTests_apply] at hb
  let f : Fin M → ℝ := fun j => ((Q j).matrix*(G.matrix*ρ.matrix*G.matrix)).trace.re
  have hσ : (G.matrix*ρ.matrix*G.matrix).PosSemidef := by
    simpa only [G.hermitian.eq] using ρ.positive.conjTranspose_mul_mul_same G.matrix
  have hf (j : Fin M) : 0≤f j :=
    (RCLike.nonneg_iff.mp (AdjointPurity.trace_mul_nonneg (Q j).positive hσ)).1
  have hs := prefix_sum_le_erase_sum f hf i
  have he : (∑ j ∈ Finset.range i.val,
      ((finiteTests Q G j).matrix*(G.matrix*ρ.matrix*G.matrix)).trace.re) =
      ∑ j : Fin i.val, f ⟨j.val,j.isLt.trans i.isLt⟩ := by
    rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, finiteTests, j.isLt.trans i.isLt]
  rw [he] at hb
  change _ ≤ _+_+4*∑j∈Finset.univ.erase i, f j
  linarith

end ProjectiveTest
end Nonadditivity.QuantumCoding
