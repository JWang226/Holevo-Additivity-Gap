/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalConverse

/-! # Actual sequential projective decoders

The decoder tests a list of orthogonal projectors in order. Its effects
are the literal products of the preceding rejection operators. All effects
are positive, and the remaining failure effect completes a genuine POVM.
-/
noncomputable section
namespace Nonadditivity.QuantumCoding
open Entropy Operational
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure ProjectiveTest (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Matrix ι ι ℂ
  hermitian : matrix.IsHermitian
  idempotent : matrix*matrix=matrix

namespace ProjectiveTest

theorem positive (P : ProjectiveTest ι) : P.matrix.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P.matrix
  simpa only [P.hermitian.eq, P.idempotent] using h

def complement (P : ProjectiveTest ι) : ProjectiveTest ι where
  matrix := 1-P.matrix
  hermitian := by
    change (1-P.matrix).conjTranspose=1-P.matrix
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, P.hermitian.eq]
  idempotent := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      P.idempotent]
    abel

/-- All preceding tests have returned their rejection outcome. -/
def rejectProduct (P : ℕ → ProjectiveTest ι) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | n+1 => (1-(P n).matrix)*rejectProduct P n

def effect (P : ℕ → ProjectiveTest ι) (i : ℕ) : Matrix ι ι ℂ :=
  (rejectProduct P i).conjTranspose*(P i).matrix*rejectProduct P i

def failure (P : ℕ → ProjectiveTest ι) (n : ℕ) : Matrix ι ι ℂ :=
  (rejectProduct P n).conjTranspose*rejectProduct P n

theorem effect_positive (P : ℕ → ProjectiveTest ι) (i : ℕ) :
    (effect P i).PosSemidef :=
  (P i).positive.conjTranspose_mul_mul_same _

theorem failure_positive (P : ℕ → ProjectiveTest ι) (n : ℕ) :
    (failure P n).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _

theorem step_complete (P : ℕ → ProjectiveTest ι) (n : ℕ) :
    effect P n+failure P (n+1)=failure P n := by
  have hQ := (P n).complement.idempotent
  change (1-(P n).matrix)*(1-(P n).matrix)=1-(P n).matrix at hQ
  have hf : failure P (n+1) =
      (rejectProduct P n).conjTranspose*(1-(P n).matrix)*rejectProduct P n := by
    unfold failure
    rw [rejectProduct, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, (P n).hermitian.eq]
    calc
      _ = (rejectProduct P n).conjTranspose*
          ((1-(P n).matrix)*(1-(P n).matrix))*rejectProduct P n := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]
  rw [hf]
  unfold effect failure
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  simp

/-- Exact telescoping completeness, including the no-success outcome. -/
theorem complete (P : ℕ → ProjectiveTest ι) (n : ℕ) :
    (∑ i ∈ Finset.range n, effect P i)+failure P n=1 := by
  induction n with
  | zero => simp [failure,rejectProduct]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, step_complete]
    exact ih

/-- Assign the residual failure outcome to a fixed message. This is a
normalized POVM on precisely the original message alphabet. -/
def decoder (P : ℕ → ProjectiveTest ι) (n : ℕ) (hn : 0<n) : POVM ι (Fin n) where
  effect := fun i => effect P i.val + if i.val=0 then failure P n else 0
  positive := fun i => (effect_positive P i.val).add (by
    split_ifs
    · exact failure_positive P n
    · exact Matrix.PosSemidef.zero)
  complete := by
    simp only [Finset.sum_add_distrib]
    have hf : (∑ i : Fin n, if i.val=0 then failure P n else 0) = failure P n := by
      have hi (i : Fin n) : i.val=0 ↔ i=⟨0,hn⟩ := by
        constructor
        · exact fun h => Fin.ext h
        · intro h; exact congrArg Fin.val h
      simp_rw [hi]
      simp
    rw [hf, Fin.sum_univ_eq_sum_range]
    exact complete P n

/-- Completing the POVM can only improve the selected message's success. -/
theorem decoder_probability_ge (P : ℕ → ProjectiveTest ι) (n : ℕ) (hn : 0<n)
    (ρ : DensityMatrix ι) (i : Fin n) :
    (ρ.matrix*effect P i.val).trace.re ≤ (decoder P n hn).probability ρ i := by
  unfold POVM.probability decoder
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have h : 0≤(ρ.matrix*(if i.val=0 then failure P n else 0)).trace.re := by
    split_ifs
    · exact (RCLike.nonneg_iff.mp
        (AdjointPurity.trace_mul_nonneg ρ.positive (failure_positive P n))).1
    · simp
  linarith

def filteredEffect (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι) (i : ℕ) :
    Matrix ι ι ℂ := G.matrix*effect P i*G.matrix

def filteredFailure (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι) (n : ℕ) :
    Matrix ι ι ℂ := 1-G.matrix+G.matrix*failure P n*G.matrix

theorem filteredEffect_positive (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι)
    (i : ℕ) : (filteredEffect G P i).PosSemidef := by
  simpa only [G.hermitian.eq] using
    (effect_positive P i).conjTranspose_mul_mul_same G.matrix

theorem filteredFailure_positive (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι)
    (n : ℕ) : (filteredFailure G P n).PosSemidef :=
  G.complement.positive.add (by
    simpa only [G.hermitian.eq] using
      (failure_positive P n).conjTranspose_mul_mul_same G.matrix)

theorem filtered_complete (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι) (n : ℕ) :
    (∑ i ∈ Finset.range n, filteredEffect G P i)+filteredFailure G P n=1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => G.matrix*A*G.matrix) (complete P n)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_one, G.idempotent] at h
  unfold filteredEffect filteredFailure
  calc
    _ = 1-G.matrix + ((∑ i ∈ Finset.range n, G.matrix*effect P i*G.matrix)+
        G.matrix*failure P n*G.matrix) := by abel
    _ = 1 := by rw [h]; abel

/-- A complete physical decoder: first filter by `G`, then run the tests.
Both initial rejection and final undecided outcomes are assigned to message zero. -/
def filteredDecoder (G : ProjectiveTest ι) (P : ℕ → ProjectiveTest ι)
    (n : ℕ) (hn : 0<n) : POVM ι (Fin n) where
  effect := fun i => filteredEffect G P i.val + if i.val=0 then filteredFailure G P n else 0
  positive := fun i => (filteredEffect_positive G P i.val).add (by
    split_ifs
    · exact filteredFailure_positive G P n
    · exact Matrix.PosSemidef.zero)
  complete := by
    simp only [Finset.sum_add_distrib]
    have hf : (∑ i : Fin n, if i.val=0 then filteredFailure G P n else 0) =
        filteredFailure G P n := by
      have hi (i : Fin n) : i.val=0 ↔ i=⟨0,hn⟩ := by
        constructor
        · exact fun h => Fin.ext h
        · intro h; exact congrArg Fin.val h
      simp_rw [hi]
      simp
    rw [hf, Fin.sum_univ_eq_sum_range]
    exact filtered_complete G P n

theorem filteredDecoder_probability_ge (G : ProjectiveTest ι)
    (P : ℕ → ProjectiveTest ι) (n : ℕ) (hn : 0<n)
    (ρ : DensityMatrix ι) (i : Fin n) :
    (ρ.matrix*filteredEffect G P i.val).trace.re ≤
      (filteredDecoder G P n hn).probability ρ i := by
  unfold POVM.probability filteredDecoder
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have h : 0≤(ρ.matrix*(if i.val=0 then filteredFailure G P n else 0)).trace.re := by
    split_ifs
    · exact (RCLike.nonneg_iff.mp
        (AdjointPurity.trace_mul_nonneg ρ.positive (filteredFailure_positive G P n))).1
    · simp
  linarith

end ProjectiveTest
end Nonadditivity.QuantumCoding
