/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarFiniteFaithfulness
import Nonadditivity.HaarTensorReplacement

/-! # Finite Hermitian evaluations imply regular self-adjointness

One finite regular-character model already detects all coefficients of a
bounded product-free-group polynomial. Applying it to the difference with
the adjoint proves the required regular symmetry from the manuscript's
finite-representation hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarFiniteSymmetry
open HaarWordExpansion HaarTensorReplacement HaarFiniteFaithfulness
open scoped Matrix Matrix.Norms.L2Operator BigOperators Kronecker

variable {G ι ν : Type} [Group G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

theorem finiteEval_adjointPolynomial (ρ : G →* unitary (Matrix ν ν ℂ))
    (f : MatrixPolynomial G ι) :
    finiteEval (representationMatrix ρ) (adjointPolynomial f) =
      (finiteEval (representationMatrix ρ) f).conjTranspose := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk =>
      change finiteEval (representationMatrix ρ) (adjointPolynomial
        ((f : MatrixPolynomial G ι) + (k : MatrixPolynomial G ι))) = _
      rw [adjointPolynomial_add, map_add, hf, hk, map_add, Matrix.conjTranspose_add]
  | single g A =>
      simp only [adjointPolynomial_single, finiteEval_single, Matrix.conjTranspose_kronecker]
      congr 1
      change (ρ g⁻¹ : Matrix ν ν ℂ) = (ρ g : Matrix ν ν ℂ).conjTranspose
      rw [map_inv]
      rfl

theorem bounded_product_selfAdjoint_of_finite {K n R : ℕ}
    (f : MatrixPolynomial (Fin n → FreeGroup (Fin K)) ι)
    (hlen : ∀ g ∈ f.support, ∀ j, FreeGroup.norm (g j) ≤ R)
    (hf : ∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
      (ρ : (Fin n → FreeGroup (Fin K)) →* unitary (Matrix ν ν ℂ)),
      (finiteEval (representationMatrix ρ) f).IsHermitian) :
    IsSelfAdjoint (regularEval f) := by
  rw [regularEval_selfAdjoint_iff]
  apply sub_eq_zero.mp
  apply bounded_product_eq_zero_of_finiteEval_eq_zero
    (R := R) (K := K) (n := n) (adjointPolynomial f - f)
  · intro g hg j
    have hu := Finsupp.support_sub hg
    rcases Finset.mem_union.mp hu with hs | hs
    · have hn : f g⁻¹ ≠ 0 := by
        intro hz
        have hne := Finsupp.mem_support_iff.mp hs
        apply hne
        rw [adjointPolynomial_apply, hz, Matrix.conjTranspose_zero]
      have h := hlen g⁻¹ (Finsupp.mem_support_iff.mpr hn) j
      simpa only [Pi.inv_apply, FreeGroup.norm_inv_eq] using h
    · exact hlen g hs j
  · let ρ := FiniteBlockModel.tensorRepresentation
      (fun _ => FiniteBlockModel.localRepresentation K (2*R)) n
    have hsymm := hf _ ρ
    change finiteEval (representationMatrix ρ) (adjointPolynomial f - f) = 0
    rw [map_sub, finiteEval_adjointPolynomial, hsymm.eq, sub_self]

/-- The old polynomial interface inherits the same implication whenever its
displayed finite support lies in a product word ball. -/
theorem polynomial_regular_selfAdjoint_of_finite {K n R : ℕ}
    (P : PolynomialReduction.Polynomial (Fin n → FreeGroup (Fin K)))
    (hlen : ∀ g ∈ P.support, ∀ j, FreeGroup.norm (g j) ≤ R)
    (hf : ∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
      (ρ : (Fin n → FreeGroup (Fin K)) →* unitary (Matrix ν ν ℂ)),
      (P.finiteEval ρ).IsHermitian) :
    IsSelfAdjoint P.regularEval := by
  rw [← regularEval_ofPolynomial]
  apply bounded_product_selfAdjoint_of_finite (R := R)
  · intro g hg j
    have hs : g ∈ P.support := by
      by_contra hn
      have hz : ofPolynomial P g = 0 := by
        unfold ofPolynomial
        have heval {I : Type} (s : Finset I) (f : I → MatrixPolynomial _ P.Index) :
            (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
          classical
          induction s using Finset.induction_on with
          | empty => simp
          | insert i s hi ih => simp [hi, MonoidAlgebra.coe_add, ih]
        rw [heval]
        apply Finset.sum_eq_zero
        intro w hw
        have he : w ≠ g := fun h => hn (h ▸ hw)
        simp [he]
      exact (Finsupp.mem_support_iff.mp hg) hz
    exact hlen g hs j
  · intro ν _ _ _ ρ
    simpa only [finiteEval_ofPolynomial] using hf ν ρ

end Nonadditivity.HaarFiniteSymmetry
