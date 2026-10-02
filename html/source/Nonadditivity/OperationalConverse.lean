/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumHolevo

/-! # Actual finite quantum codes and their dimension converse

Messages are encoded into density matrices and decoded by positive operator
valued measures. The error probability is the actual Born probability. The
dimension bound below applies to every code and every Kraus channel, with
no coding or entropy inequalities assumed.
-/

noncomputable section

namespace Nonadditivity.Operational

open Entropy Channels AdjointPurity
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

variable {ι ο κ μ : Type*}

/-- A finite positive operator valued measure, including arbitrary effects
of any rank. -/
structure POVM (ο μ : Type*) [Fintype ο] [DecidableEq ο] [Fintype μ] where
  effect : μ → Matrix ο ο ℂ
  positive : ∀ m, (effect m).PosSemidef
  complete : ∑ m, effect m = 1

namespace POVM

variable [Fintype ο] [DecidableEq ο] [Fintype μ]

/-- The actual Born measurement probability. -/
def probability (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) : ℝ :=
  (ρ.matrix * P.effect m).trace.re

theorem probability_nonneg (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    0 ≤ P.probability ρ m :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg ρ.positive (P.positive m))).1

@[simp] theorem probability_sum (P : POVM ο μ) (ρ : DensityMatrix ο) :
    ∑ m, P.probability ρ m = 1 := by
  simp only [probability, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum,
    P.complete, Matrix.mul_one, ρ.normalized, Complex.one_re]

theorem probability_le_one (P : POVM ο μ) (ρ : DensityMatrix ο) (m : μ) :
    P.probability ρ m ≤ 1 := by
  rw [← P.probability_sum ρ]
  exact Finset.single_le_sum (fun i _ => P.probability_nonneg ρ i) (Finset.mem_univ m)

end POVM

variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]

namespace POVM

variable [Fintype μ]

/-- Pull a decoder through the channel using the actual Kraus adjoint. -/
def pullback (P : POVM ο μ) (T : KrausChannel ι ο κ) : POVM ι μ where
  effect := fun m => T.adjointMap (P.effect m)
  positive := fun m => T.adjointMap_posSemidef _ (P.positive m)
  complete := by
    change ∑ m, T.adjointLinearMap (P.effect m) = 1
    rw [← map_sum, P.complete]
    exact T.adjointMap_one

@[simp] theorem probability_pullback (P : POVM ο μ) (T : KrausChannel ι ο κ)
    (ρ : DensityMatrix ι) (m : μ) :
    (P.pullback T).probability ρ m = P.probability (T.output ρ) m := by
  exact congrArg Complex.re (T.trace_duality ρ.matrix (P.effect m)).symm

end POVM

/-- An unassisted finite code for a specified actual quantum channel.
Uniform messages are used in the average success and error probabilities. -/
structure Code (T : KrausChannel ι ο κ) (M : ℕ) where
  encode : Fin M → DensityMatrix ι
  decode : POVM ο (Fin M)

namespace DensityMatrix

theorem weights_le_one (ρ : DensityMatrix ο) (i : ο) : ρ.weights i ≤ 1 := by
  rw [← ρ.weights_sum]
  exact Finset.single_le_sum (fun j _ => ρ.weights_nonneg j) (Finset.mem_univ i)

/-- A normalized positive matrix is bounded above by the identity. -/
theorem one_sub_posSemidef (ρ : DensityMatrix ο) : (1 - ρ.matrix).PosSemidef := by
  let U := ρ.positive.isHermitian.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (ρ.weights i : ℂ))
  have hs : ρ.matrix = Unitary.conjStarAlgAut ℂ _ U D :=
    ρ.positive.isHermitian.spectral_theorem
  have hd : (1 - D).PosSemidef := by
    have he : 1 - D = Matrix.diagonal (fun i => ((1 - ρ.weights i : ℝ) : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst j; simp [D]
      · simp [D, h]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ ((1 - ρ.weights i : ℝ) : ℂ)
      exact_mod_cast (sub_nonneg.mpr (weights_le_one ρ i)))
  have hh := hd.mul_mul_conjTranspose_same (U : Matrix ο ο ℂ)
  rw [← Matrix.star_eq_conjTranspose] at hh
  rw [hs]
  simpa only [Unitary.conjStarAlgAut_apply, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, ← Unitary.coe_star, Unitary.coe_mul_star_self] using hh

/-- Every positive effect has expectation at most its trace. -/
theorem expectation_le_trace (ρ : DensityMatrix ο) (E : Matrix ο ο ℂ)
    (hE : E.PosSemidef) : (ρ.matrix * E).trace.re ≤ E.trace.re := by
  have h : 0 ≤ ((1 - ρ.matrix) * E).trace.re := (RCLike.nonneg_iff.mp
    (trace_mul_nonneg (one_sub_posSemidef ρ) hE)).1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h
  linarith

end DensityMatrix

namespace Code

variable {T : KrausChannel ι ο κ} {M : ℕ}

/-- Average correct decoding probability for uniform messages. -/
def success (C : Code T M) : ℝ :=
  (∑ m, C.decode.probability (T.output (C.encode m)) m) / (M : ℝ)

/-- Average decoding error probability for uniform messages. -/
def error (C : Code T M) : ℝ := 1 - C.success

theorem success_nonneg (C : Code T M) : 0 ≤ C.success := by
  exact div_nonneg (Finset.sum_nonneg fun m _ => C.decode.probability_nonneg _ m)
    (Nat.cast_nonneg M)

theorem success_le_one (C : Code T M) : C.success ≤ 1 := by
  by_cases hM : M = 0
  · simp [success, hM]
  · have hp : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
    apply (div_le_iff₀ hp).mpr
    simpa using Finset.sum_le_sum
      (fun m (_ : m ∈ Finset.univ) => C.decode.probability_le_one (T.output (C.encode m)) m)

theorem error_nonneg (C : Code T M) : 0 ≤ C.error :=
  sub_nonneg.mpr C.success_le_one

theorem error_le_one (C : Code T M) : C.error ≤ 1 := by
  unfold error
  linarith [C.success_nonneg]

/-- The finite dimensional packing converse for actual quantum codes.
It holds for mixed inputs and arbitrary non-projective POVM decoders. -/
theorem success_le_dimension_div_messages (C : Code T M) :
    C.success ≤ (Fintype.card ο : ℝ) / M := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  calc
    ∑ m, C.decode.probability (T.output (C.encode m)) m ≤
        ∑ m, (C.decode.effect m).trace.re := by
      exact Finset.sum_le_sum fun m _ => DensityMatrix.expectation_le_trace
        (T.output (C.encode m)) (C.decode.effect m) (C.decode.positive m)
    _ = (Fintype.card ο : ℝ) := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, C.decode.complete, Matrix.trace_one]
      simp

/-- Any channel code is an identity-channel code with its POVM pulled back
to the input. This is an exact identity of Born probabilities. -/
def pulledBack (C : Code T M) :
    Code (KrausChannel.identity : KrausChannel ι ι Unit) M where
  encode := C.encode
  decode := C.decode.pullback T

@[simp] theorem pulledBack_success (C : Code T M) : C.pulledBack.success = C.success := by
  have hidentity (ρ : DensityMatrix ι) :
      (KrausChannel.identity : KrausChannel ι ι Unit).output ρ = ρ := by
    apply Entropy.DensityMatrix.ext
    exact KrausChannel.identity_map ρ.matrix
  simp only [success, pulledBack, hidentity, POVM.probability_pullback]

/-- The input dimension gives an independent converse, even when the output
space is larger than the input space. -/
theorem success_le_input_dimension_div_messages (C : Code T M) :
    C.success ≤ (Fintype.card ι : ℝ) / M := by
  simpa only [pulledBack_success] using C.pulledBack.success_le_dimension_div_messages

theorem success_le_min_dimension_div_messages (C : Code T M) :
    C.success ≤ min (Fintype.card ι : ℝ) (Fintype.card ο : ℝ) / M := by
  by_cases h : Fintype.card ι ≤ Fintype.card ο
  · rw [min_eq_left (by exact_mod_cast h)]
    exact C.success_le_input_dimension_div_messages
  · rw [min_eq_right (by exact_mod_cast Nat.le_of_not_ge h)]
    exact C.success_le_dimension_div_messages

/-- At error at most `ε < 1`, no more than `dim(output)/(1-ε)`
messages can be sent. -/
theorem messages_mul_one_sub_error_le_dimension (C : Code T M) :
    (M : ℝ) * (1 - C.error) ≤ Fintype.card ο := by
  by_cases hM : M = 0
  · simp [hM]
  · have hp : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
    have h := (le_div_iff₀ hp).mp C.success_le_dimension_div_messages
    simpa only [error, sub_sub_cancel, mul_comm] using h

theorem messages_le_dimension_div_one_sub_error (C : Code T M) {ε : ℝ}
    (hε : ε < 1) (herror : C.error ≤ ε) :
    (M : ℝ) ≤ (Fintype.card ο : ℝ) / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε)).mpr
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left herror 1) (Nat.cast_nonneg M)).trans
    C.messages_mul_one_sub_error_le_dimension

end Code

end Nonadditivity.Operational
