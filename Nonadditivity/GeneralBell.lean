/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.BellOutput
import Nonadditivity.AdjointPurity
import Nonadditivity.Conversion

/-! # Bell witnesses for arbitrary Kraus channels

This extends the Bell entropy argument beyond random-unitary complements.
All norms use the Euclidean operator norm, and all states are actual matrices.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.GeneralBell

open Entropy Channels BellOutput
open scoped BigOperators ComplexOrder Matrix Kronecker Matrix.Norms.L2Operator

lemma mul_log_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log q + p - q ≤ p * Real.log p := by
  by_cases hz : p = 0
  · simp only [hz, zero_mul, add_zero, zero_sub]
    exact neg_nonpos.mpr hq.le
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq hp')) hp
  rw [Real.log_div hq.ne' hz] at h
  have he : p * (q / p - 1) = q - p := by field_simp
  rw [he] at h
  nlinarith

/-- A large atom in a distribution on `K²` points forces the required
Bell entropy deficit. The comparison weights need not be normalized. -/
theorem shannon_le_of_large_atom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (K : ℕ) (hK : 1 ≤ K) (hd : Fintype.card ι = K ^ 2)
    (j : ι) (hj : 1 / (K : ℝ) ≤ p j) :
    shannon p ≤ 2 * Real.log (K : ℝ) - (Real.log (K : ℝ) - 1) / K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hl : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
  let q : ι → ℝ := fun i => if i = j then 1 / K else 1 / (K : ℝ)^2
  have hq (i : ι) : 0 < q i := by dsimp [q]; split <;> positivity
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mul_log_lower (hp i) (hq i))
  have hlog (i : ι) : p i * Real.log (q i) =
      -2 * p i * Real.log (K : ℝ) + (if i = j then p i * Real.log (K : ℝ) else 0) := by
    by_cases h : i = j
    · simp [q, h, Real.log_inv]; ring
    · simp [q, h, Real.log_inv, Real.log_pow]; ring
  have hqsplit (i : ι) : q i = 1 / (K : ℝ)^2 +
      (if i = j then 1 / (K : ℝ) - 1 / (K : ℝ)^2 else 0) := by
    dsimp [q]; split <;> ring
  have hql : ∑ i, p i * Real.log (q i) =
      -2 * Real.log (K : ℝ) + p j * Real.log (K : ℝ) := by
    simp_rw [hlog]
    simp [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hs]
  have hqs : ∑ i, q i = 1 + 1 / (K : ℝ) - 1 / (K : ℝ)^2 := by
    simp_rw [hqsplit]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hd, Nat.cast_pow, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hs, hql, hqs] at hb
  have hlarge := mul_le_mul_of_nonneg_right hj hl
  unfold shannon
  have hnn : 0 ≤ 1 / (K : ℝ)^2 := by positivity
  have he : (Real.log (K : ℝ) - 1) / K =
      1 / (K : ℝ) * Real.log (K : ℝ) - 1 / K := by ring
  rw [he]
  linarith

/-- A positive density matrix has an eigenvalue equal to its operator norm. -/
theorem exists_weight_eq_norm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ρ : DensityMatrix ι) : ∃ i, ρ.weights i = ‖ρ.matrix‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  let f : ι → ℂ := fun i => (ρ.weights i : ℂ)
  have hn : ‖ρ.matrix‖ = ‖f‖ := by
    conv_lhs => rw [ρ.positive.isHermitian.spectral_theorem]
    rw [StarAlgEquiv.norm_map, Matrix.l2_opNorm_diagonal]
    rfl
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖f i‖)
    Finset.univ_nonempty
  have hm : ‖f‖ = ‖f i‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ _)))
    (norm_le_pi_norm f i)
  refine ⟨i, ?_⟩
  rw [hn, hm]
  simp [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ρ.weights_nonneg i)]

/-- A Bell-sized overlap already implies a logarithmic entropy deficit. -/
theorem entropy_le_of_overlap {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ρ σ : DensityMatrix ι) (K : ℕ) (hK : 1 ≤ K)
    (hd : Fintype.card ι = K ^ 2)
    (hoverlap : 1 / (K : ℝ) ≤ (σ.matrix * ρ.matrix).trace.re) :
    ρ.vonNeumann ≤ 2 * Real.log (K : ℝ) - (Real.log (K : ℝ) - 1) / K := by
  obtain ⟨i, hi⟩ := exists_weight_eq_norm ρ
  apply shannon_le_of_large_atom ρ.weights ρ.weights_nonneg ρ.weights_sum K hK hd i
  rw [hi]
  exact hoverlap.trans (AdjointPurity.state_expectation_re_le_opNorm σ ρ.matrix
    ρ.positive.isHermitian)

section BellOverlap

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

omit [DecidableEq ι] [Nonempty ι] [Fintype ο] [DecidableEq ο] [Nonempty ο]
  [Fintype κ] in
lemma pure_overlap (v w : ι → ℂ) :
    (Matrix.vecMulVec v (star v) * Matrix.vecMulVec w (star w)).trace =
      (Complex.normSq (star v ⬝ᵥ w) : ℂ) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul]
  have hc : v ⬝ᵥ star w = star (star v ⬝ᵥ w) := by
    simp [dotProduct]
  rw [hc]
  exact Complex.mul_conj _

omit [Fintype κ] [Nonempty ι] [Fintype ο] [DecidableEq ο] [Nonempty ο] in
lemma tensor_mul_bell (A B : Matrix ο ι ℂ) (a b : ο) :
    ((A ⊗ₖ B.map star) *ᵥ normalizedBellVector) (a,b) =
      (Real.sqrt (1 / (Fintype.card ι : ℝ)) : ℂ) *
        ∑ i, A a i * star (B b i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.map_apply, normalizedBellVector, bellVector, Finset.mul_sum,
    mul_comm, mul_left_comm]

omit [Fintype κ] [Nonempty ι] [Nonempty ο] in
lemma bell_amplitude (A B : Matrix ο ι ℂ) :
    star (normalizedBellVector (ι := ο)) ⬝ᵥ
      ((A ⊗ₖ B.map star) *ᵥ normalizedBellVector) =
    ((Real.sqrt (1 / (Fintype.card ο : ℝ)) : ℂ) *
      (Real.sqrt (1 / (Fintype.card ι : ℝ)) : ℂ)) *
        ∑ a, ∑ i, A a i * star (B a i) := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, tensor_mul_bell]
  simp [normalizedBellVector, bellVector, Finset.mul_sum, mul_assoc, apply_ite]

omit [Fintype κ] in
lemma bell_term_overlap (A B : Matrix ο ι ℂ) :
    ((bellState (ι := ο)).matrix *
      ((A ⊗ₖ B.map star) * (bellState (ι := ι)).matrix *
        (A ⊗ₖ B.map star).conjTranspose)).trace.re =
      1 / ((Fintype.card ο : ℝ) * Fintype.card ι) *
        Complex.normSq (∑ a, ∑ i, A a i * star (B a i)) := by
  rw [bellState_matrix, bellState_matrix, conjugation_vecMulVec, pure_overlap,
    Complex.ofReal_re, bell_amplitude, Complex.normSq_mul,
    Complex.normSq_mul]
  simp only [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity :
    0 ≤ 1 / (Fintype.card ο : ℝ)), Real.mul_self_sqrt (by positivity :
    0 ≤ 1 / (Fintype.card ι : ℝ))]
  ring

/-- Exact Bell overlap for any rectangular Kraus family. -/
theorem paired_bell_overlap (T : KrausChannel ι ο κ) :
    ((bellState (ι := ο)).matrix *
      ((T.tensor T.conjugate).output (bellState (ι := ι))).matrix).trace.re =
      1 / ((Fintype.card ο : ℝ) * Fintype.card ι) *
        ∑ k, ∑ l, Complex.normSq (∑ a, ∑ i, T.kraus k a i * star (T.kraus l a i)) := by
  simp only [KrausChannel.output_matrix, KrausChannel.map, KrausChannel.tensor,
    KrausChannel.conjugate, Matrix.mul_sum, Matrix.trace_sum,
    Complex.re_sum, Fintype.sum_prod_type]
  simp_rw [bell_term_overlap]
  simp only [Finset.mul_sum]

def krausMass (T : KrausChannel ι ο κ) (k : κ) : ℝ :=
  ∑ a, ∑ i, Complex.normSq (T.kraus k a i)

omit [Nonempty ι] [DecidableEq ο] [Nonempty ο] in
theorem krausMass_sum (T : KrausChannel ι ο κ) :
    ∑ k, krausMass T k = Fintype.card ι := by
  have he (k : κ) : ((T.kraus k).conjTranspose * T.kraus k).trace.re = krausMass T k := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.star_def]
    simp_rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    rw [Finset.sum_comm]
    rfl
  have h := congrArg (fun M : Matrix ι ι ℂ => M.trace.re) T.complete
  simpa only [Matrix.trace_sum, Complex.re_sum, he, Matrix.trace_one,
    Complex.natCast_re] using h

omit [Nonempty ι] [DecidableEq ο] [Nonempty ο] in
theorem diagonal_kraus_inner (T : KrausChannel ι ο κ) (k : κ) :
    Complex.normSq (∑ a, ∑ i, T.kraus k a i * star (T.kraus k a i)) =
      krausMass T k ^ 2 := by
  simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum,
    Complex.normSq_ofReal, krausMass, pow_two]

/-- The output Bell overlap is at least input dimension divided by
output dimension times the number of Kraus operators. -/
theorem paired_bell_overlap_lower [DecidableEq κ] [Nonempty κ]
    (T : KrausChannel ι ο κ) :
    (Fintype.card ι : ℝ) / ((Fintype.card ο : ℝ) * Fintype.card κ) ≤
    ((bellState (ι := ο)).matrix *
      ((T.tensor T.conjugate).output (bellState (ι := ι))).matrix).trace.re := by
  have hi : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have ho : (0 : ℝ) < Fintype.card ο := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hdiag : ∑ k, krausMass T k ^ 2 ≤
      ∑ k, ∑ l, Complex.normSq (∑ a, ∑ i, T.kraus k a i * star (T.kraus l a i)) := by
    apply Finset.sum_le_sum
    intro k _
    rw [← diagonal_kraus_inner T k]
    exact Finset.single_le_sum (f := fun l =>
      Complex.normSq (∑ a, ∑ i, T.kraus k a i * star (T.kraus l a i)))
      (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (krausMass T) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    krausMass_sum] at hcs
  have hmass : (Fintype.card ι : ℝ)^2 / Fintype.card κ ≤ ∑ k, krausMass T k ^ 2 :=
    (div_le_iff₀ hk).mpr (by simpa only [mul_one] using hcs)
  rw [paired_bell_overlap]
  calc
    _ = (1 / ((Fintype.card ο : ℝ) * Fintype.card ι)) *
        ((Fintype.card ι : ℝ)^2 / Fintype.card κ) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmass.trans hdiag) (by positivity)

/-- General conjugate-channel Bell entropy bound when the environment is
no larger than the input. This includes normalized Gaussian isometries. -/
theorem paired_bell_entropy_le [DecidableEq κ] [Nonempty κ]
    (T : KrausChannel ι ο κ) (hd : Fintype.card κ ≤ Fintype.card ι) :
    ((T.tensor T.conjugate).output (bellState (ι := ι))).vonNeumann ≤
      2 * Real.log (Fintype.card ο : ℝ) -
        (Real.log (Fintype.card ο : ℝ) - 1) / Fintype.card ο := by
  apply entropy_le_of_overlap _ (bellState (ι := ο)) (Fintype.card ο)
    Fintype.card_pos (by simp [pow_two])
  have hk : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have ho : (0 : ℝ) < Fintype.card ο := by exact_mod_cast Fintype.card_pos
  have hdim : (Fintype.card κ : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  apply le_trans _ (paired_bell_overlap_lower T)
  apply (div_le_div_iff₀ ho (mul_pos ho hk)).mpr
  nlinarith

end BellOverlap

theorem converted_bounds {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] {K : ℕ} [NeZero K]
    (T : KrausChannel ι (ZMod K) κ) (hd : Fintype.card κ ≤ Fintype.card ι)
    {t : ℝ} (ht : 0 ≤ t)
    (hcert : ∀ A : Matrix (ZMod K) (ZMod K) ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ t * AdjointPurity.hsLength A) :
    (Conversion.converted T).holevo ≤ Real.log (1 + (K : ℝ) * t^2) ∧
    (Real.log (K : ℝ) - 1) / K ≤
      ((Conversion.converted T).tensor (Conversion.converted T)).holevo ∧
    (Real.log (K : ℝ) - 1) / K - 2 * Real.log (1 + (K : ℝ) * t^2) ≤
      ((Conversion.converted T).tensor (Conversion.converted T)).holevo -
        2 * (Conversion.converted T).holevo := by
  have h := Conversion.converted_bounds_of_certificate T ht hcert
    (bellState (ι := ι)) (paired_bell_entropy_le T hd)
  simp only [ZMod.card] at h
  rcases h with ⟨h₁,h₂,h₃⟩
  exact ⟨h₁, by linarith, by linarith⟩

end Nonadditivity.GeneralBell
