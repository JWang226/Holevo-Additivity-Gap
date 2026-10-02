/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarRefinedPaletteFibre
import Nonadditivity.HaarPathClassSums

/-! # Literal grouped coefficients in independent profile coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.HaarOperatorPathBridge
open scoped BigOperators
open HaarPathGraph HaarPathClasses HaarProfileCoefficient HaarPathVertexFibre
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The actual refined coefficient sum is the independent profile sum times
its exact number of vertex injections. -/
theorem refinedCoefficientSum_eq_palette
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p : ℕ)
    (P : Path V 2 m) :
    refinedCoefficientSum A p P = Fintype.card (VertexLabels P) •
      ∑ σ : P.ChainPalette,
        (A^p) (FreeGroup.mk (List.ofFn (P.paletteColoring σ).path.colors)) := by
  exact P.sum_refined_fibre_eq_palettes
    (fun c => (A^p) (FreeGroup.mk (List.ofFn c)))

/-- Along the actual core decomposition, the independent coefficient is the
power coefficient at the literal product of its independently chosen words. -/
theorem refinedCoefficientSum_eq_chain_palette
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p : ℕ)
    (P : Path V 2 m) (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList) :
    refinedCoefficientSum A p P = Fintype.card (VertexLabels P) •
      ∑ σ : P.ChainPalette,
        (A^p) ((cs.map (fun c => word (P.paletteWord σ c))).prod) := by
  rw [refinedCoefficientSum_eq_palette]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [←(P.paletteColoring σ).assignedWords_prod cs hcs]
  rfl

/-- The only vertex-label loss is the power of the actual graph vertex count. -/
theorem norm_refinedCoefficientSum_le_palette
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p : ℕ)
    (P : Path V 2 m) (hm : 0 < m) :
    ‖refinedCoefficientSum A p P‖ ≤
      (Fintype.card V : ℝ)^P.vertices.card *
        ‖∑ σ : P.ChainPalette,
          (A^p) (FreeGroup.mk (List.ofFn (P.paletteColoring σ).path.colors))‖ := by
  rw [refinedCoefficientSum_eq_palette,RCLike.norm_nsmul (K := ℂ),nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact_mod_cast HaarRefinedVertexFibre.card_vertexLabels_le P hm

end Nonadditivity.HaarOperatorPathBridge
