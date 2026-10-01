/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.GeneralBell
import Nonadditivity.PositiveHolevo
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Positive Holevo information for channels with a small environment

A channel with equally sized input and Kraus-label spaces, and at least two
output coordinates, has a pure input whose output is singular. This gives
a positive Holevo denominator after the switch/Weyl conversion.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.SmallEnvironment

open Entropy Channels Channels.KrausChannel
open scoped BigOperators Matrix ComplexOrder

theorem shannon_le_log_card_sub_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (j : ι) (hj : p j = 0) (hd : 2 ≤ Fintype.card ι) :
    shannon p ≤ Real.log (Fintype.card ι - 1 : ℕ) := by
  let J := {i : ι // i ≠ j}
  have hc : Fintype.card J = Fintype.card ι - 1 := by
    simp [J, Fintype.card_subtype_compl]
  letI : Nonempty J := Fintype.card_pos_iff.mp (by rw [hc]; omega)
  have hsum : ∑ i : J, p i.val = 1 := by
    have h := Fintype.sum_eq_add_sum_subtype_ne p j
    rw [hs, hj, zero_add] at h
    exact h.symm
  have he : shannon p = shannon (fun i : J => p i.val) := by
    unfold shannon
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun i => p i * Real.log (p i)) j]
    simp only [hj, zero_mul, zero_add]
    rfl
  rw [he, ← hc]
  exact shannon_le_log_card _ (fun i => hp i.val) hsum

theorem entropy_le_of_singular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (hd : 2 ≤ Fintype.card ι) (hdet : ρ.matrix.det = 0) :
    ρ.vonNeumann ≤ Real.log (Fintype.card ι - 1 : ℕ) := by
  rw [ρ.positive.isHermitian.det_eq_prod_eigenvalues] at hdet
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hdet
  apply shannon_le_log_card_sub_one ρ.weights ρ.weights_nonneg ρ.weights_sum j _ hd
  change (ρ.weights j : ℂ) = 0 at hj
  exact Complex.ofReal_eq_zero.mp hj

section Square
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
lemma normalized_kernel (M : Matrix ι ι ℂ) (hd : M.det = 0) :
    ∃ v : ι → ℂ, (∑ i, Complex.normSq (v i)) = 1 ∧ M *ᵥ v = 0 := by
  obtain ⟨x, hx, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hx
  have hS : 0 < ∑ i, Complex.normSq (x i) := by
    apply Finset.sum_pos'
    · intro i _; exact Complex.normSq_nonneg _
    · exact ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  let r : ℝ := Real.sqrt (∑ i, Complex.normSq (x i))
  have hr : 0 < r := Real.sqrt_pos.mpr hS
  refine ⟨Complex.ofReal (r⁻¹) • x, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, ← Finset.mul_sum]
    have hs : r * r = ∑ i, Complex.normSq (x i) := Real.mul_self_sqrt hS.le
    rw [← hs]
    field_simp
  · rw [Matrix.mulVec_smul, he, smul_zero]

lemma square_pair_dependent (A B : Matrix ι ι ℂ) :
    ∃ v : ι → ℂ, (∑ i, Complex.normSq (v i)) = 1 ∧
      (B *ᵥ v = 0 ∨ ∃ z : ℂ, A *ᵥ v = z • (B *ᵥ v)) := by
  by_cases hB : B.det = 0
  · obtain ⟨v,hv,he⟩ := normalized_kernel B hB
    exact ⟨v,hv,Or.inl he⟩
  · obtain ⟨z,v,hv,he⟩ := PositiveHolevo.exists_normalized_eigenvector (B⁻¹ * A)
    refine ⟨v,hv,Or.inr ⟨z,?_⟩⟩
    have h := congrArg (fun w => B *ᵥ w) he
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), Matrix.one_mul,
      Matrix.mulVec_smul] using h

variable {ο : Type*} [Fintype ο] [DecidableEq ο]

def environmentMatrix (T : KrausChannel ι ο ι) (a : ο) : Matrix ι ι ℂ :=
  fun e i => T.kraus e a i

omit [Nonempty ι] in
lemma output_entry (T : KrausChannel ι ο ι) (v : ι → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) (a b : ο) :
    (T.output (pureState v hv)).matrix a b =
      ∑ e, ((environmentMatrix T a) *ᵥ v) e * star (((environmentMatrix T b) *ᵥ v) e) := by
  simp only [KrausChannel.output_matrix, KrausChannel.map, pureState,
    BellOutput.conjugation_vecMulVec, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply]
  rfl

/-- The matrix-pencil argument constructs a pure input with dependent
environment vectors in two output coordinates. -/
theorem exists_singular_output (T : KrausChannel ι ο ι) (a b : ο) (hab : a ≠ b) :
    ∃ ρ : DensityMatrix ι, (T.output ρ).matrix.det = 0 := by
  obtain ⟨v,hv,hdep⟩ := square_pair_dependent (environmentMatrix T a) (environmentMatrix T b)
  refine ⟨pureState v hv, Matrix.exists_vecMul_eq_zero_iff.mp ?_⟩
  rcases hdep with hb | ⟨z,hz⟩
  · refine ⟨Pi.single b 1, ?_, ?_⟩
    · intro h
      have := congrFun h b
      simp at this
    · ext c
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
      simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [output_entry, hb]
      simp
  · refine ⟨(Pi.single a (1:ℂ) : ο → ℂ) - z • (Pi.single b (1:ℂ) : ο → ℂ), ?_, ?_⟩
    · intro h
      have := congrFun h a
      simp [hab] at this
    · ext c
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
      simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [output_entry, output_entry, hz]
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem exists_output_entropy_lt (T : KrausChannel ι ο ι)
    (hd : 2 ≤ Fintype.card ο) :
    ∃ ρ : DensityMatrix ι, (T.output ρ).vonNeumann < Real.log (Fintype.card ο : ℝ) := by
  obtain ⟨a,b,_,_,hab⟩ := Finset.one_lt_card_iff.mp
    (show 1 < (Finset.univ : Finset ο).card by simpa using hd)
  obtain ⟨ρ,hρ⟩ := exists_singular_output T a b hab
  refine ⟨ρ, (entropy_le_of_singular _ hd hρ).trans_lt ?_⟩
  apply Real.log_lt_log
  · exact_mod_cast (show 0 < Fintype.card ο - 1 by omega)
  · exact_mod_cast (show Fintype.card ο - 1 < Fintype.card ο by omega)

theorem converted_holevo_pos {K : ℕ} [NeZero K] (hK : 2 ≤ K)
    (T : KrausChannel ι (ZMod K) ι) : 0 < (Conversion.converted T).holevo := by
  obtain ⟨ρ,hρ⟩ := exists_output_entropy_lt T (by simpa using hK)
  have hmin : T.minimumEntropy ≤ (T.output ρ).vonNeumann :=
    StateEnsembles.minimumEntropy_le (outputs := T.outputs) ⟨ρ,rfl⟩
  rw [Conversion.converted_holevo]
  simp only [ZMod.card] at hρ
  linarith

end Square
end Nonadditivity.SmallEnvironment
