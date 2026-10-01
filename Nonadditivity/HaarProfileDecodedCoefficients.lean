/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileAssignmentBound

/-! # Eliminate profile padding on valid decoded assignments

On the actual dependent profile palettes the block factory is exactly the
ordinary/non-returning coefficient at the decoded whole group word. The only
decoder condition is its defining value on a singleton segment.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarProfileDecodedCoefficients
open scoped BigOperators
open HaarOperatorPolynomial HaarProfileBlockCoefficients HaarProfilePadding
  HaarProfileCoefficient HaarPathProfiles NoncommutativeCS HaarProfilePatternBound
  HaarProfileAssignmentBound

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d M : ℕ}

/-- Zero padding disappears on every valid profile assignment. -/
theorem blockFactor_valid
    (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (σ : ∀ i, Words d (size i) (profile i)) (k : ℕ)
    (hdecode : ∀ i, decode k [i] [embedAssignment size profile hsize σ i] =
      orientedWord (forward k i) (σ i)) (labels : List I) :
    blockFactor B size profile hsize ordinary duration forward decode k labels
        (labels.map (embedAssignment size profile hsize σ)) =
      blockPolynomial B (ordinary k) (duration k)
        (decode k labels (labels.map (embedAssignment size profile hsize σ))) := by
  cases labels with
  | nil => rfl
  | cons i l =>
      cases l with
      | nil =>
          simp only [List.map_cons, List.map_nil, blockFactor, paddedFamily, embedAssignment]
          rw [(embedWords_injective (p := profile i) (hsize i)).extend_apply]
          exact congrArg (blockPolynomial B (ordinary k) (duration k)) (hdecode i).symm
      | cons j l => rfl

/-- Factor-list congruence only needs equality at the actual named assignment,
not equality of the coefficient factories on malformed profile lists. -/
theorem blockFactors_congr_on_assignment {J : Type*} {m n : ℕ}
    {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b)
    (A C : ℕ → List I → List J → E →L[ℂ] E) (σ : I → J)
    (h : ∀ k labels, A k labels (labels.map σ) = C k labels (labels.map σ)) (k : ℕ) :
    P.blockFactors A k σ = P.blockFactors C k σ := by
  induction P generalizing k with
  | done => rfl
  | first i P ih =>
      simpa [EndpointSkeleton.blockFactors, ih] using
        congrArg (fun X => P.blockFactors C (k + 1) σ ++ [X]) (h k [i])
  | @last m n a b p P ih =>
      simpa [EndpointSkeleton.blockFactors, ih] using
        congrArg (fun X => P.blockFactors C (k + 1) σ ++ [X]) (h k [a p])
  | @middle m n a b v P ih =>
      simpa [EndpointSkeleton.blockFactors, ih, List.map_map] using
        congrArg (fun X => P.blockFactors C (k + 1) σ ++ [X]) (h k (v.map a))
  | singleton i P ih =>
      simpa [EndpointSkeleton.blockFactors, ih] using
        congrArg (fun X => P.blockFactors C (k + 1) σ ++ [X]) (h k [i])

/-- The entire literal ordered product is the corresponding product of
actual whole-word coefficients after decoding the valid profile assignment. -/
theorem blockFactors_valid {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (σ : ∀ i, Words d (size i) (profile i))
    (hdecode : ∀ k i, decode k [i] [embedAssignment size profile hsize σ i] =
      orientedWord (forward k i) (σ i)) (k : ℕ) :
    P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k
      (embedAssignment size profile hsize σ) =
    P.blockFactors (fun k labels choices =>
      blockPolynomial B (ordinary k) (duration k) (decode k labels choices)) k
      (embedAssignment size profile hsize σ) := by
  apply blockFactors_congr_on_assignment
  intro s labels
  exact blockFactor_valid B size profile hsize ordinary duration forward decode σ s (hdecode s) labels

end Nonadditivity.HaarProfileDecodedCoefficients
