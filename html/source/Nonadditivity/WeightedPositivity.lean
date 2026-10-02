/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.DampedPositivity
import Nonadditivity.WeightedBell
import Nonadditivity.WeightedBlock

/-! # Strict positivity from nonuniform diagonal output weights

A diagonal entry different from the uniform value witnesses a nonuniform
output. Such a witness survives every invertible input damping filter.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.WeightedPositivity

open Entropy Channels Channels.KrausChannel DampedChannel
open scoped BigOperators Matrix ComplexOrder

theorem state_ne_maximallyMixed_of_diagonal {ο : Type*} [Fintype ο]
    [DecidableEq ο] [Nonempty ο] (ρ : DensityMatrix ο) (a : ο) (r : ℝ)
    (hdiag : ρ.matrix a a = (r : ℂ))
    (hr : r ≠ 1 / (Fintype.card ο : ℝ)) : ρ ≠ maximallyMixed ο := by
  intro he
  have hh := congrArg (fun σ : DensityMatrix ο => σ.matrix a a) he
  dsimp only at hh
  rw [hdiag] at hh
  apply hr
  apply Complex.ofReal_injective
  simpa only [maximallyMixed, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] using hh

theorem pow_ne_uniform {K n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r)
    (hne : r ≠ 1 / (K : ℝ)) : r^n ≠ 1 / ((K^n : ℕ) : ℝ) := by
  intro hh
  apply hne
  apply (pow_left_inj₀ hr (by positivity : 0 ≤ 1 / (K : ℝ)) (by omega : n ≠ 0)).mp
  simpa only [Nat.cast_pow, div_pow, one_pow] using hh

/-- The constant word in the recursively associated tensor basis. -/
def repeatedIndex {ο : Type*} (a : ο) : (n : ℕ) → TensorChainIndex ο n
  | 0 => PUnit.unit
  | n+1 => (repeatedIndex a n, a)

/-- Equal local diagonal values multiply to the corresponding power. -/
theorem tensorChain_repeated_diagonal {ο : Type*} [Fintype ο] [DecidableEq ο]
    (ρ : ℕ → DensityMatrix ο) (a : ο) (r : ℝ)
    (hdiag : ∀ j, (ρ j).matrix a a = (r : ℂ)) (n : ℕ) :
    (DensityMatrix.tensorChain ρ n).matrix (repeatedIndex a n) (repeatedIndex a n) =
      (r^n : ℝ) := by
  induction n with
  | zero => simp [DensityMatrix.tensorChain, emptyTensorState, repeatedIndex]
  | succ n ih =>
    change (DensityMatrix.tensorChain ρ n).matrix (repeatedIndex a n) (repeatedIndex a n) *
      (ρ n).matrix a a = ((r^(n+1) : ℝ) : ℂ)
    rw [ih, hdiag n, ← Complex.ofReal_mul, pow_succ]

theorem converted_damped_holevoBits_pos_of_diagonal
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    {d : ℕ} [NeZero d] (T : KrausChannel ι (ZMod d) κ)
    (F G : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) (hGF : G*F=1)
    (ρ : DensityMatrix ι) (a : ZMod d) (r : ℝ)
    (hdiag : (T.output ρ).matrix a a = (r : ℂ)) (hr : r ≠ 1 / (d : ℝ)) :
    0 < (Conversion.converted (damped T F hF hres)).holevoBits := by
  apply DampedPositivity.converted_damped_holevoBits_pos T F G hF hres hGF
  refine ⟨ρ, state_ne_maximallyMixed_of_diagonal (T.output ρ) a r hdiag ?_⟩
  simpa only [ZMod.card] using hr

section WeightedBlock

open BlockConstruction WeightedBlock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {K : ℕ} [NeZero K]

/-- Product inputs exhibit the exact product of the local branch probabilities. -/
theorem weightedComplementary_product_output_diagonal
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1)
    (ρ : ℕ → DensityMatrix ι) (a : Fin K) (n : ℕ) :
    ((weightedComplementary U p hp hsum n).output (DensityMatrix.tensorChain ρ n)).matrix
      (repeatedIndex a n) (repeatedIndex a n) = ((p a)^n : ℝ) := by
  change ((tensorChain (fun j => (randomUnitary p hp hsum (U j)).complementary) n).output
    (DensityMatrix.tensorChain ρ n)).matrix _ _ = _
  rw [tensorChain_output]
  exact tensorChain_repeated_diagonal _ a (p a)
    (fun j => WeightedBell.complementary_output_diagonal p hp hsum (U j) (ρ j) a) n

/-- The same diagonal witness in the standardized block output coordinates. -/
theorem weightedBlock_product_output_diagonal
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1)
    (ρ : ℕ → DensityMatrix ι) (a : Fin K) (n : ℕ) :
    ((weightedBlock U p hp hsum n).output (DensityMatrix.tensorChain ρ n)).matrix
      (blockOutputEquiv K n (repeatedIndex a n))
      (blockOutputEquiv K n (repeatedIndex a n)) = ((p a)^n : ℝ) := by
  have he := reindex_output_eq (weightedComplementary U p hp hsum n)
    (Equiv.refl _) (blockOutputEquiv K n) (DensityMatrix.tensorChain ρ n)
  rw [DensityMatrix.reindex_refl] at he
  change (((weightedComplementary U p hp hsum n).reindex (Equiv.refl _)
    (blockOutputEquiv K n)).output (DensityMatrix.tensorChain ρ n)).matrix _ _ = _
  rw [he]
  simpa only [DensityMatrix.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using
    weightedComplementary_product_output_diagonal U p hp hsum ρ a n

/-- Every product input has a nonuniform output when the branch weights are nonuniform. -/
theorem weightedBlock_product_output_ne_maximallyMixed
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1)
    (ρ : ℕ → DensityMatrix ι) {n : ℕ} (hn : 1 ≤ n)
    (hne : ∃ a, p a ≠ 1 / (K : ℝ)) :
    (weightedBlock U p hp hsum n).output (DensityMatrix.tensorChain ρ n) ≠
      maximallyMixed (ZMod (K^n)) := by
  obtain ⟨a, ha⟩ := hne
  apply state_ne_maximallyMixed_of_diagonal _
    (blockOutputEquiv K n (repeatedIndex a n)) ((p a)^n)
    (weightedBlock_product_output_diagonal U p hp hsum ρ a n)
  simpa only [ZMod.card] using pow_ne_uniform hn (hp a) ha

theorem weightedBlock_exists_output_ne_maximallyMixed
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1)
    {n : ℕ} (hn : 1 ≤ n) (hne : ∃ a, p a ≠ 1 / (K : ℝ)) :
    ∃ ρ, (weightedBlock U p hp hsum n).output ρ ≠ maximallyMixed (ZMod (K^n)) := by
  exact ⟨DensityMatrix.tensorChain (fun _ => maximallyMixed ι) n,
    weightedBlock_product_output_ne_maximallyMixed U p hp hsum _ hn hne⟩

/-- Nonuniform weighted blocks retain a positive Holevo denominator after any
invertible damping and the actual switch/Weyl conversion. -/
theorem converted_damped_weightedBlock_holevoBits_pos
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (p : Fin K → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1)
    {n : ℕ} (hn : 1 ≤ n) (hne : ∃ a, p a ≠ 1 / (K : ℝ))
    (F G : Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (hGF : G*F=1) :
    0 < (Conversion.converted (damped (weightedBlock U p hp hsum n) F hF hres)).holevoBits :=
  DampedPositivity.converted_damped_holevoBits_pos _ F G hF hres hGF
    (weightedBlock_exists_output_ne_maximallyMixed U p hp hsum hn hne)

end WeightedBlock

end Nonadditivity.WeightedPositivity
