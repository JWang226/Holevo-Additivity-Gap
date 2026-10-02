/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarOperatorPolynomial
import Nonadditivity.HaarTensorReplacement
import Nonadditivity.RegularFubini
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # The operator coefficients of a mixed free-group polynomial

Currying a product-group polynomial and evaluating its second coordinate
regularly gives actual bounded operator coefficients. The Fubini isometry
intertwines the two regular evaluations, so their operator norms agree exactly.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarOperatorCurry
open HaarWordExpansion RegularCoefficientEnergy
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {G H ι : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι]

def operatorCurry : MatrixPolynomial (G × H) ι →+*
    HaarOperatorPolynomial.Polynomial G (Hilbert H ι) :=
  (MonoidAlgebra.mapRangeRingHom G (regularEval (G := H) (ι := ι))).comp
    MonoidAlgebra.curryRingEquiv.toRingHom

omit [DecidableEq G] in
@[simp] theorem operatorCurry_single (g : G) (h : H) (A : Matrix ι ι ℂ) :
    operatorCurry (MonoidAlgebra.single (g,h) A) =
      MonoidAlgebra.single g (RegularFactorization.term A h) := by
  change MonoidAlgebra.mapRangeRingHom G regularEval
    (MonoidAlgebra.curryRingEquiv (MonoidAlgebra.single (g,h) A)) = _
  rw [MonoidAlgebra.curryRingEquiv_single, MonoidAlgebra.mapRangeRingHom_single,
    regularEval_single]

omit [DecidableEq G] in
theorem operatorCurry_apply (f : MatrixPolynomial (G × H) ι) (g : G) :
    operatorCurry f g = regularEval (MonoidAlgebra.curryRingEquiv f g) := by
  simp [operatorCurry, MonoidAlgebra.mapRangeRingHom_apply]

/-- Exact intertwining on the actual product-group square-summable space. -/
theorem curry_regularEval (f : MatrixPolynomial (G × H) ι) (x : Hilbert (G × H) ι) :
    RegularFubini.curry (regularEval f x) =
      HaarOperatorPolynomial.regular (operatorCurry f) (RegularFubini.curry x) := by
  induction f using Finsupp.induction_linear with
  | zero => ext a b i; simp [RegularFubini.curry_apply]
  | add f k hf hk =>
      change RegularFubini.curry (regularEval ((f : MatrixPolynomial (G × H) ι)+k) x) = _
      rw [map_add, map_add, map_add]
      ext a b i
      have h₁ := congrArg (fun z => z a b i) hf
      have h₂ := congrArg (fun z => z a b i) hk
      simpa only [ContinuousLinearMap.add_apply, RegularFubini.curry_apply,
        lp.coeFn_add, Pi.add_apply] using congrArg₂ (· + ·) h₁ h₂
  | single w A =>
      obtain ⟨g,h⟩ := w
      rw [operatorCurry_single, regularEval_single, HaarOperatorPolynomial.regular_single]
      ext a b i
      rfl

/-- The coefficient-algebra regular norm is precisely the original product
regular norm, with no finite-dimensional approximation. -/
theorem operatorCurry_norm (f : MatrixPolynomial (G × H) ι) :
    ‖HaarOperatorPolynomial.regular (operatorCurry f)‖ = ‖regularEval f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    obtain ⟨y,rfl⟩ :=
      (RegularFubini.curryIsometry (F := G) (G := H) (E := CoefficientSpace ι)).surjective x
    change ‖HaarOperatorPolynomial.regular (operatorCurry f) (RegularFubini.curry y)‖ ≤
      ‖regularEval f‖ * ‖RegularFubini.curry y‖
    rw [← curry_regularEval, RegularFubini.curry_norm, RegularFubini.curry_norm]
    exact (regularEval f).le_opNorm y
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← RegularFubini.curry_norm, curry_regularEval]
    exact ((HaarOperatorPolynomial.regular (operatorCurry f)).le_opNorm _).trans_eq
      (by rw [RegularFubini.curry_norm])

end Nonadditivity.HaarOperatorCurry
