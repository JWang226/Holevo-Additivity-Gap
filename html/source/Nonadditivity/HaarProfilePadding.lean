/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileCoefficient

/-! # Padding different profile palettes into one finite register alphabet

Extending a coefficient family by zero through an injection preserves its sum
and both Gram factors exactly. Hence arbitrary finite profile palettes can use
the same register type without changing any of the coefficient budgets.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarProfilePadding

open scoped BigOperators
open NoncommutativeCS HaarProfileCoefficient HaarOperatorPolynomial HaarPathProfiles

variable {I J R S : Type*} [Fintype I] [Fintype J] [Zero R] [AddCommMonoid S]

/-- Exact finite sum preservation under zero padding, including nonlinear
functions such as the two Gram summands. -/
theorem sum_map_extend_zero (e : I → J) (he : Function.Injective e)
    (A : I → R) (F : R → S) (hF : F 0 = 0) :
    ∑ j, F (Function.extend e A 0 j) = ∑ i, F (A i) := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image e, F (Function.extend e A 0 j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hjnot
      have hr : j ∉ Set.range e := by
        rintro ⟨i,rfl⟩
        exact hjnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      rw [Function.extend_apply' _ _ _ hr]
      exact hF
    _ = _ := by
      rw [Finset.sum_image he.injOn]
      simp only [he.extend_apply]

theorem sum_extend_zero (e : I → J) (he : Function.Injective e) (A : I → S) :
    ∑ j, Function.extend e A 0 j = ∑ i, A i :=
  sum_map_extend_zero e he A id rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Column Gram factors are unchanged, even when unused register values exist. -/
theorem columnGram_extend_zero (e : I → J) (he : Function.Injective e)
    (A : I → E →L[ℂ] E) : columnGram (Function.extend e A 0) = columnGram A := by
  exact sum_map_extend_zero e he A (fun B => B.adjoint ∘L B) (by simp)

/-- Row Gram factors are unchanged as well. -/
theorem rowGram_extend_zero (e : I → J) (he : Function.Injective e)
    (A : I → E →L[ℂ] E) : rowGram (Function.extend e A 0) = rowGram A := by
  exact sum_map_extend_zero e he A (fun B => B ∘L B.adjoint) (by simp)

/-- Pointwise power bounds are also preserved by zero padding. -/
theorem norm_extend_zero_le (e : I → J) (he : Function.Injective e)
    (A : I → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (j : J) :
    ‖Function.extend e A 0 j‖ ≤ C := by
  classical
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i,rfl⟩ := hj
    rw [he.extend_apply]
    exact hA i
  · rw [Function.extend_apply' _ _ _ hj]
    simpa using hC

/-- A common finite alphabet for every signed word of length at most `m`. -/
abbrev Palette (d m : ℕ) := Σ k : Fin (m + 1), Fin k.val → Color d

/-- Every actual fixed-length reduced profile family injects into that common palette. -/
def embedWords {d k m : ℕ} {p : Profile (Color d)} (hk : k ≤ m) :
    Words d k p → Palette d m := fun w => ⟨⟨k, by omega⟩, w.val⟩

theorem embedWords_injective {d k m : ℕ} {p : Profile (Color d)} (hk : k ≤ m) :
    Function.Injective (embedWords (p := p) hk) := by
  intro a b h
  exact Subtype.ext (Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq)

/-- Common-register endpoint factors retain the same sharp bound. -/
theorem padded_endpoint_bounds {d k m : ℕ} (p : Profile (Color d)) (hk : k ≤ m)
    (A : Polynomial (FreeGroup (Fin d)) E)
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1) (n : ℕ) :
    Real.sqrt ‖columnGram (Function.extend (embedWords hk)
        (returningCoefficients (k := k) A n p) 0)‖ ≤
      (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) ∧
    Real.sqrt ‖rowGram (Function.extend (embedWords hk)
        (returningCoefficients (k := k) A n p) 0)‖ ≤
      (n + 1 : ℕ) * ‖regular A‖ ^ (n + 1) := by
  rw [columnGram_extend_zero _ (embedWords_injective hk),
    rowGram_extend_zero _ (embedWords_injective hk)]
  exact returning_endpoint_bounds A hA n p

/-- Common-register singleton factors retain the original small palette count. -/
theorem padded_singleton_bound {d k m : ℕ} (p : Profile (Color d)) (hk : k ≤ m)
    (A : Polynomial (FreeGroup (Fin d)) E)
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1) (n : ℕ) :
    ‖∑ j : Palette d m, Function.extend (embedWords hk)
      (returningCoefficients (k := k) A n p) 0 j‖ ≤
      Real.sqrt (((2 * d) ^ k : ℕ) : ℝ) *
        ((n + 1 : ℕ) * ‖regular A‖ ^ (n + 1)) := by
  rw [sum_extend_zero _ (embedWords_injective hk)]
  exact returning_singleton_bound A hA n p

end Nonadditivity.HaarProfilePadding
