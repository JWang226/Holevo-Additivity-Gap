/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.BlockConstruction
import Mathlib.Tactic.Ring

/-!
# The actual complementary adjoint polynomial

This proves the manuscript's Gram channel and polynomial formula from the
actual Kraus implementation. The indices can be arbitrary finite types,
including the tensor-word index set used for blocks.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity.Entropy
open scoped Matrix BigOperators ComplexConjugate

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [Fintype κ]

/-- Complementary adjoints are Gram-polynomial evaluations in the Kraus
operators. This is a matrix identity, including rectangular Kraus families. -/
theorem complementary_adjointMap_eq_gram (T : KrausChannel ι ο κ)
    (A : Matrix κ κ ℂ) :
    T.complementary.adjointMap A =
      ∑ a, ∑ b, A a b • ((T.kraus a).conjTranspose * T.kraus b) := by
  ext i j
  simp only [adjointMap, complementary, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ o, ∑ b, ∑ a, star (T.kraus a o i) * A a b * T.kraus b o j) =
        ∑ o, ∑ a, ∑ b, A a b * (star (T.kraus a o i) * T.kraus b o j) := by
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ b, ∑ o, A a b * (star (T.kraus a o i) * T.kraus b o j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

variable [Nonempty κ]

private theorem sqrt_weight_product (p : ℝ) (hp : 0 ≤ p) :
    star (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hp]

/-- The Gram entries of a uniform unitary family carry exactly the factor
`1 / card κ`, proved from the positive square-root Kraus weights. -/
theorem uniformUnitary_kraus_gram (U : κ → unitary (Matrix ι ι ℂ)) (a b : κ) :
    ((uniformUnitary U).kraus a).conjTranspose * (uniformUnitary U).kraus b =
      (1 / (Fintype.card κ : ℂ)) •
        ((U a : Matrix ι ι ℂ).conjTranspose * (U b : Matrix ι ι ℂ)) := by
  simp only [uniformUnitary, randomUnitary, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ)]
  rw [sqrt_weight_product _ (by positivity : 0 ≤ 1 / (Fintype.card κ : ℝ))]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]

/-- The exact polynomial `Γ_N(A)` of the manuscript, with the normalization
and word orientation established from the concrete complementary channel. -/
theorem uniform_complementary_adjoint_eq_polynomial
    (U : κ → unitary (Matrix ι ι ℂ)) (A : Matrix κ κ ℂ) :
    (uniformUnitary U).complementary.adjointMap A =
      (1 / (Fintype.card κ : ℂ)) •
        ∑ a, ∑ b, A a b •
          ((U a : Matrix ι ι ℂ).conjTranspose * (U b : Matrix ι ι ℂ)) := by
  rw [complementary_adjointMap_eq_gram]
  simp_rw [uniformUnitary_kraus_gram]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm (A a b)]

/-- The actual complementary Gram-channel entries are the specified input
overlaps, with the correct order `U_bᴴ U_a`. -/
theorem uniform_complementary_map_entry
    (U : κ → unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) (a b : κ) :
    ((uniformUnitary U).complementary.map X) a b =
      (1 / (Fintype.card κ : ℂ)) *
        (X * (U b : Matrix ι ι ℂ).conjTranspose * (U a : Matrix ι ι ℂ)).trace := by
  rw [complementary_map_entry]
  simp only [uniformUnitary, randomUnitary, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul]
  rw [sqrt_weight_product _ (by positivity : 0 ≤ 1 / (Fintype.card κ : ℝ))]
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast, Matrix.mul_assoc]

/-- The same formula for the output of an actual density matrix. -/
theorem uniform_complementary_output_entry [DecidableEq κ]
    (U : κ → unitary (Matrix ι ι ℂ)) (ρ : DensityMatrix ι) (a b : κ) :
    ((uniformUnitary U).complementary.output ρ).matrix a b =
      (1 / (Fintype.card κ : ℂ)) *
        (ρ.matrix * (U b : Matrix ι ι ℂ).conjTranspose * (U a : Matrix ι ι ℂ)).trace :=
  uniform_complementary_map_entry U ρ.matrix a b

open Nonadditivity.Entropy
open scoped Kronecker

omit [Nonempty κ] in
/-- Complementing a concrete tensor block gives the tensor block of the
complementary channels, as actual Kraus-channel data. -/
theorem tensorChain_complementary [DecidableEq ο] [DecidableEq κ]
    (T : ℕ → KrausChannel ι ο κ) (n : ℕ) :
    (tensorChain T n).complementary = tensorChain (fun j => (T j).complementary) n := by
  induction n with
  | zero =>
    apply KrausChannel.ext
    funext k
    ext a b
    simp [tensorChain, emptyTensorChannel, complementary]
  | succ n ih =>
    change ((tensorChain T n).tensor (T n)).complementary =
      (tensorChain (fun j => (T j).complementary) n).tensor (T n).complementary
    have hswap : ((tensorChain T n).tensor (T n)).complementary =
        (tensorChain T n).complementary.tensor (T n).complementary := by
      apply KrausChannel.ext
      rfl
    rw [hswap, ih]

/-- Tensor words in the actual block Hilbert space, retaining the ordered
recursively nested branch indices. -/
def tensorWord [DecidableEq κ] (U : ℕ → κ → unitary (Matrix ι ι ℂ)) :
    (n : ℕ) → TensorChainIndex κ n →
      Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ
  | 0, _ => 1
  | n + 1, a => tensorWord U n a.1 ⊗ₖ (U n a.2 : Matrix ι ι ℂ)

/-- The actual tensor-unitary Kraus operators are exactly the tensor words
times the product of their normalized square-root branch weights. -/
theorem tensorChain_uniform_kraus [DecidableEq κ]
    (U : ℕ → κ → unitary (Matrix ι ι ℂ)) (n : ℕ) (a : TensorChainIndex κ n) :
    (tensorChain (fun j => uniformUnitary (U j)) n).kraus a =
      (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) ^ n • tensorWord U n a := by
  induction n with
  | zero =>
    ext i j
    cases i
    cases j
    simp [tensorChain, emptyTensorChannel, tensorWord]
    rfl
  | succ n ih =>
    rcases a with ⟨a,b⟩
    change (tensorChain (fun j => uniformUnitary (U j)) n).kraus a ⊗ₖ
      (uniformUnitary (U n)).kraus b = _
    rw [ih]
    simp only [uniformUnitary, randomUnitary, tensorWord, Matrix.smul_kronecker,
      Matrix.kronecker_smul, smul_smul, pow_succ]
    rw [mul_comm]
    rfl

/-- The precise normalized polynomial for the actual complementary tensor
block, before standardizing its output labels. -/
theorem blockComplementary_adjoint_eq_tensor_polynomial [DecidableEq κ]
    (U : ℕ → κ → unitary (Matrix ι ι ℂ)) (n : ℕ)
    (A : Matrix (TensorChainIndex κ n) (TensorChainIndex κ n) ℂ) :
    (Nonadditivity.BlockBell.blockComplementary U n).adjointMap A =
      (1 / (Fintype.card κ : ℂ)) ^ n •
        ∑ a, ∑ b, A a b •
          ((tensorWord U n a).conjTranspose * tensorWord U n b) := by
  change (tensorChain (fun j => (uniformUnitary (U j)).complementary) n).adjointMap A = _
  rw [← tensorChain_complementary, complementary_adjointMap_eq_gram]
  simp_rw [tensorChain_uniform_kraus]
  have hweight :
      (Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) ^ n *
        star ((Real.sqrt (1 / (Fintype.card κ : ℝ)) : ℂ) ^ n) =
      (1 / (Fintype.card κ : ℂ)) ^ n := by
    rw [star_pow, ← mul_pow, mul_comm]
    rw [sqrt_weight_product _ (by positivity : 0 ≤ 1 / (Fintype.card κ : ℝ))]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hweight, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm (A a b)]

omit [Nonempty κ] in
/-- Changing only the output labels pulls the observable back by that
same equivalence. This is proved from the Kraus adjoint formula. -/
theorem reindex_output_adjointMap {ν : Type*} [Fintype ν]
    (T : KrausChannel ι ο κ) (e : ο ≃ ν) (A : Matrix ν ν ℂ) :
    (T.reindex (Equiv.refl ι) e).adjointMap A =
      T.adjointMap (A.submatrix e e) := by
  have hA : (A.submatrix e e).submatrix e.symm e.symm = A := by
    ext i j
    simp
  conv_lhs => rw [← hA]
  simp only [adjointMap, reindex, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  rfl

/-- The exact normalized tensor-word polynomial of the manuscript, now for
the actual `blockChannel` with its explicitly standardized output basis. -/
theorem blockChannel_adjoint_eq_tensor_polynomial {K : ℕ} [NeZero K]
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) (n : ℕ)
    (A : Matrix (ZMod (K ^ n)) (ZMod (K ^ n)) ℂ) :
    (Nonadditivity.BlockConstruction.blockChannel U n).adjointMap A =
      (1 / ((K : ℂ) ^ n)) •
        ∑ a, ∑ b,
          A (Nonadditivity.BlockConstruction.blockOutputEquiv K n a)
            (Nonadditivity.BlockConstruction.blockOutputEquiv K n b) •
          ((tensorWord U n a).conjTranspose * tensorWord U n b) := by
  unfold Nonadditivity.BlockConstruction.blockChannel
  rw [reindex_output_adjointMap, blockComplementary_adjoint_eq_tensor_polynomial]
  simp only [Fintype.card_fin, one_div, inv_pow, Matrix.submatrix_apply]

end Nonadditivity.Channels.KrausChannel
