/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfilePatternBound

/-! # Remove padded assignments and sum over the actual dependent palettes

Every introduced label has a zero-padded endpoint. An invalid profile choice
therefore makes the full ordered coefficient product zero. Consequently the
uniform-register sum equals the literal sum over the different profile-word
palettes attached to each edge label.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarProfileAssignmentBound
open scoped BigOperators
open HaarOperatorPolynomial HaarProfileBlockCoefficients HaarProfilePadding
  HaarProfileCoefficient HaarPathProfiles NoncommutativeCS HaarProfilePatternBound

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d M : ℕ}

def embedAssignment (size : I → ℕ) (profile : I → Profile (Color d))
    (hsize : ∀ i, size i ≤ M) (σ : ∀ i, Words d (size i) (profile i)) : I → Palette d M :=
  fun i => embedWords (hsize i) (σ i)

theorem embedAssignment_injective (size : I → ℕ) (profile : I → Profile (Color d))
    (hsize : ∀ i, size i ≤ M) : Function.Injective (embedAssignment size profile hsize) := by
  intro σ τ h
  funext i
  exact embedWords_injective (hsize i) (congrFun h i)

theorem exists_invalid_of_not_mem_range (size : I → ℕ) (profile : I → Profile (Color d))
    (hsize : ∀ i, size i ≤ M) (σ : I → Palette d M)
    (hσ : σ ∉ Set.range (embedAssignment size profile hsize)) :
    ∃ i, σ i ∉ Set.range (embedWords (p := profile i) (hsize i)) := by
  classical
  by_cases h : ∀ i, σ i ∈ Set.range (embedWords (p := profile i) (hsize i))
  · let τ : ∀ i, Words d (size i) (profile i) := fun i => Classical.choose (h i)
    have he : embedAssignment size profile hsize τ = σ := by
      funext i
      exact Classical.choose_spec (h i)
    exact (hσ ⟨τ, he⟩).elim
  · exact not_forall.mp h

/-- Any invalid label value kills its actual first/singleton coefficient,
and hence the full ordered product. -/
theorem block_product_zero_of_invalid {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (σ : I → Palette d M) {i : I} (hi : i ∈ P.profileLabels)
    (hbad : σ i ∉ Set.range (embedWords (p := profile i) (hsize i))) (k : ℕ) :
    (P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k σ).prod = 0 := by
  induction P generalizing k with
  | done => simpa [NoncommutativeCS.EndpointSkeleton.profileLabels] using hi
  | first j P ih =>
      rcases List.mem_cons.mp hi with he | hi
      · subst i
        simp [NoncommutativeCS.EndpointSkeleton.blockFactors, blockFactor, paddedFamily,
          Function.extend_apply' _ _ _ hbad]
      · simpa [NoncommutativeCS.EndpointSkeleton.blockFactors, List.prod_append,
          ih hi (k + 1)]
  | last p P ih =>
      simpa [NoncommutativeCS.EndpointSkeleton.blockFactors, List.prod_append,
        ih hi (k + 1)]
  | middle v P ih =>
      simpa [NoncommutativeCS.EndpointSkeleton.blockFactors, List.prod_append,
        ih hi (k + 1)]
  | singleton j P ih =>
      rcases List.mem_cons.mp hi with he | hi
      · subst i
        simp [NoncommutativeCS.EndpointSkeleton.blockFactors, blockFactor, paddedFamily,
          Function.extend_apply' _ _ _ hbad]
      · simpa [NoncommutativeCS.EndpointSkeleton.blockFactors, List.prod_append,
          ih hi (k + 1)]

/-- Exact equality of the uniform-register and dependent-profile sums. -/
theorem sum_uniform_eq_dependent [Fintype I]
    {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (hc : ∀ i : I, i ∈ P.profileLabels)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d)) (k : ℕ) :
    (∑ σ : I → Palette d M,
      (P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k σ).prod) =
    ∑ σ : ∀ i, Words d (size i) (profile i),
      (P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k
        (embedAssignment size profile hsize σ)).prod := by
  classical
  let F : (I → Palette d M) → E →L[ℂ] E := fun σ =>
    (P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k σ).prod
  let e := embedAssignment size profile hsize
  have he := embedAssignment_injective size profile hsize
  have hF : F = Function.extend e (fun σ => F (e σ)) 0 := by
    funext σ
    by_cases hσ : σ ∈ Set.range e
    · obtain ⟨τ, rfl⟩ := hσ
      rw [he.extend_apply]
    · rw [Function.extend_apply' _ _ _ hσ]
      obtain ⟨i, hi⟩ := exists_invalid_of_not_mem_range size profile hsize σ hσ
      exact block_product_zero_of_invalid P B size profile hsize ordinary duration forward decode
        σ (hc i) hi k
  change (∑ σ, F σ) = ∑ σ, F (e σ)
  exact (congrArg (fun f : (I → Palette d M) → E →L[ℂ] E => ∑ σ, f σ) hF).trans
    (sum_extend_zero e he (fun σ => F (e σ)))

/-- The fixed-pattern bound now sums over the actual independent profile
families, including their different lengths and letter-count constraints. -/
theorem dependent_profile_sum_norm_le [Fintype I]
    (P : NoncommutativeCS.EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (hduration : ∀ k, 1 ≤ duration k) (k : ℕ) :
    ‖∑ σ : ∀ i, Words d (size i) (profile i),
      (P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k
        (embedAssignment size profile hsize σ)).prod‖ ≤
      P.singletonWeight size d * (HaarMarkedCompositions.markedProduct P.markedFlags (P.times duration k) : ℝ) *
        ‖regular B‖ ^ (P.times duration k).sum := by
  rw [← sum_uniform_eq_dependent P hc B size profile hsize ordinary duration forward decode k]
  exact P.profile_sum_norm_le hn hc B hB size profile hsize ordinary duration forward decode hduration k

end Nonadditivity.HaarProfileAssignmentBound
