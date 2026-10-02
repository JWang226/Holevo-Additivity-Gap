/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Channels
import Nonadditivity.StateEnsembles

/-!
# Measured input registers

The control register is measured and discarded. These are concrete Kraus
channels, not postulated transformations of entropy bounds.
-/

noncomputable section

namespace Nonadditivity.Channels

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι ο κ ζ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype ζ] [DecidableEq ζ]

/-- Select a classical block of the input matrix. -/
def selector (z : ζ) : Matrix ι (ζ × ι) ℂ :=
  fun i w => if w = (z, i) then 1 else 0

theorem selector_mul_adjoint (z w : ζ) :
    selector (ι := ι) z * (selector (ι := ι) w).conjTranspose =
      if z = w then 1 else 0 := by
  ext i j
  by_cases h : z = w <;> by_cases hij : i = j <;>
    simp [Matrix.mul_apply, selector, Matrix.conjTranspose_apply,
      Prod.mk.injEq, Matrix.one_apply,
      h, hij, eq_comm]

theorem selector_complete :
    ∑ z : ζ, (selector (ι := ι) z).conjTranspose * selector z = 1 := by
  ext a b
  rcases a with ⟨z, i⟩
  rcases b with ⟨w, j⟩
  by_cases h : z = w <;> by_cases hij : i = j <;>
    simp [Matrix.sum_apply, Matrix.mul_apply, selector, Matrix.conjTranspose_apply,
      Prod.mk.injEq, Matrix.one_apply, ite_and, h, hij]

/-- A fixed input control value, with its trace and positivity proved. -/
def labelledState (z : ζ) (ρ : DensityMatrix ι) : DensityMatrix (ζ × ι) where
  matrix := (selector z).conjTranspose * ρ.matrix * selector z
  positive := ρ.positive.conjTranspose_mul_mul_same _
  normalized := by
    rw [Matrix.trace_mul_cycle, selector_mul_adjoint]
    simp [ρ.normalized]

theorem select_labelledState (z w : ζ) (ρ : DensityMatrix ι) :
    selector z * (labelledState w ρ).matrix * (selector z).conjTranspose =
      if z = w then ρ.matrix else 0 := by
  change selector z * ((selector w).conjTranspose * ρ.matrix * selector w) *
    (selector z).conjTranspose = _
  have hmat : selector z * ((selector w).conjTranspose * ρ.matrix * selector w) *
      (selector z).conjTranspose =
      (selector z * (selector w).conjTranspose) * ρ.matrix *
      (selector w * (selector z).conjTranspose) := by simp only [Matrix.mul_assoc]
  rw [hmat]
  rw [selector_mul_adjoint, selector_mul_adjoint]
  by_cases h : z = w
  · subst w
    simp
  · simp [h, Ne.symm h]

namespace KrausChannel

/-- Measure the control, apply its selected channel, and discard the label. -/
def controlled (T : ζ → KrausChannel ι ο κ) : KrausChannel (ζ × ι) ο (ζ × κ) where
  kraus := fun zk => (T zk.1).kraus zk.2 * selector zk.1
  complete := by
    simp only [Matrix.conjTranspose_mul, Fintype.sum_prod_type]
    calc
      (∑ z, ∑ k, (selector z).conjTranspose * ((T z).kraus k).conjTranspose *
          ((T z).kraus k * selector z)) =
          ∑ z, (selector z).conjTranspose *
            (∑ k, ((T z).kraus k).conjTranspose * (T z).kraus k) * selector z := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by simp only [KrausChannel.complete, Matrix.mul_one]; exact selector_complete

omit [DecidableEq ο] in
theorem controlled_map (T : ζ → KrausChannel ι ο κ)
    (X : Matrix (ζ × ι) (ζ × ι) ℂ) :
    (controlled T).map X = ∑ z, (T z).map (selector z * X * (selector z).conjTranspose) := by
  simp only [map, controlled, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

@[simp] theorem controlled_output_labelled (T : ζ → KrausChannel ι ο κ)
    (z : ζ) (ρ : DensityMatrix ι) :
    (controlled T).output (labelledState z ρ) = (T z).output ρ := by
  apply DensityMatrix.ext
  simp only [output_matrix, controlled_map, select_labelledState]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Conjugate every output of a channel by a fixed unitary. -/
def outputUnitary (T : KrausChannel ι ο κ) (U : unitary (Matrix ο ο ℂ)) :
    KrausChannel ι ο κ where
  kraus := fun k => (U : Matrix ο ο ℂ) * T.kraus k
  complete := by
    have hU : (U : Matrix ο ο ℂ).conjTranspose * (U : Matrix ο ο ℂ) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      (∑ k, ((U : Matrix ο ο ℂ) * T.kraus k).conjTranspose *
          ((U : Matrix ο ο ℂ) * T.kraus k)) =
          ∑ k, (T.kraus k).conjTranspose *
            ((U : Matrix ο ο ℂ).conjTranspose * (U : Matrix ο ο ℂ)) * T.kraus k := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by simp only [hU, Matrix.mul_one, T.complete]

theorem outputUnitary_map (T : KrausChannel ι ο κ) (U : unitary (Matrix ο ο ℂ))
    (X : Matrix ι ι ℂ) :
    (T.outputUnitary U).map X = (U : Matrix ο ο ℂ) * T.map X *
      (U : Matrix ο ο ℂ).conjTranspose := by
  simp only [map, outputUnitary, Matrix.conjTranspose_mul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.mul_assoc]

/-- The actual channel extension associated with a finite family of output unitaries. -/
def covariantExtension (T : KrausChannel ι ο κ)
    (U : ζ → unitary (Matrix ο ο ℂ)) : KrausChannel (ζ × ι) ο (ζ × κ) :=
  controlled (fun z => T.outputUnitary (U z))

end KrausChannel

end Nonadditivity.Channels
