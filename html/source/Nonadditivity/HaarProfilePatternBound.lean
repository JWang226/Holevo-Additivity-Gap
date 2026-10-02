/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileBlockCoefficients
import Nonadditivity.NoncommutativeCSSkeletonDecoration
import Nonadditivity.HaarMarkedCompositions

/-! # Actual profile coefficients on a fixed compressed occurrence pattern

Endpoint factors are actual padded profile coefficients. A middle block is
one actual ordinary or killed-return coefficient at its full decoded word.
All local norm estimates are discharged by the proved polynomial bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarProfilePatternBound
open scoped BigOperators
open HaarOperatorPolynomial HaarProfileBlockCoefficients HaarProfilePadding
  HaarPathProfiles NoncommutativeCS HaarMarkedCompositions

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d M : ℕ}

/-- A literal whole-block coefficient, with the singleton-list case exposing
the zero-padded family needed at an endpoint. -/
def blockFactor (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (k : ℕ) (labels : List I) (choices : List (Palette d M)) : E →L[ℂ] E :=
  match labels, choices with
  | [i], [j] => paddedFamily B (ordinary k) (duration k) (forward k i) (profile i) (hsize i) j
  | _, _ => blockPolynomial B (ordinary k) (duration k) (decode k labels choices)

theorem blockFactor_norm_le (B : Polynomial (FreeGroup (Fin d)) E)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (hduration : ∀ k, 1 ≤ duration k) (k : ℕ) (labels : List I) (choices : List (Palette d M)) :
    ‖blockFactor B size profile hsize ordinary duration forward decode k labels choices‖ ≤
      ‖regular B‖ ^ duration k := by
  unfold blockFactor
  split
  · exact padded_norm_le B (ordinary k) (hduration k) _ _ _ _
  · exact block_coefficient_norm_le B (ordinary k) (hduration k) _

end Nonadditivity.HaarProfilePatternBound

namespace Nonadditivity.NoncommutativeCS.EndpointSkeleton
open scoped BigOperators
open HaarOperatorPolynomial HaarProfileBlockCoefficients HaarProfilePadding
  HaarPathProfiles HaarMarkedCompositions HaarProfilePatternBound

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {d M : ℕ}

def singletonWeight {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (size : I → ℕ) (d : ℕ) : ℝ :=
  match P with
  | .done _ => 1
  | .first _ P => P.singletonWeight size d
  | .last _ P => P.singletonWeight size d
  | .middle _ P => P.singletonWeight size d
  | .singleton i P => P.singletonWeight size d * Real.sqrt (((2 * d) ^ size i : ℕ) : ℝ)

def times {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (duration : ℕ → ℕ) (k : ℕ) : List ℕ :=
  match P with
  | .done _ => []
  | .first _ P => duration k :: P.times duration (k + 1)
  | .last _ P => duration k :: P.times duration (k + 1)
  | .middle _ P => duration k :: P.times duration (k + 1)
  | .singleton _ P => duration k :: P.times duration (k + 1)

def budget {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (size : I → ℕ) (d : ℕ)
    (ρ : ℝ) (duration : ℕ → ℕ) (k : ℕ) : ℝ :=
  match P with
  | .done _ => 1
  | .first _ P => P.budget size d ρ duration (k + 1) * ((duration k : ℝ) * ρ ^ duration k)
  | .last _ P => P.budget size d ρ duration (k + 1) * ((duration k : ℝ) * ρ ^ duration k)
  | .middle _ P => P.budget size d ρ duration (k + 1) * ρ ^ duration k
  | .singleton i P => P.budget size d ρ duration (k + 1) *
      (Real.sqrt (((2 * d) ^ size i : ℕ) : ℝ) * ((duration k : ℝ) * ρ ^ duration k))

theorem singletonWeight_nonneg {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (size : I → ℕ) (d : ℕ) :
    0 ≤ P.singletonWeight size d := by
  induction P <;> simp_all [singletonWeight] <;> positivity

theorem budget_nonneg {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (size : I → ℕ) (d : ℕ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (duration : ℕ → ℕ) (k : ℕ) :
    0 ≤ P.budget size d ρ duration k := by
  induction P generalizing k with
  | done => exact zero_le_one
  | first i P ih => exact mul_nonneg (ih (k + 1)) (by positivity)
  | last p P ih => exact mul_nonneg (ih (k + 1)) (by positivity)
  | middle v P ih => exact mul_nonneg (ih (k + 1)) (by positivity)
  | singleton i P ih => exact mul_nonneg (ih (k + 1)) (by positivity)

theorem budget_eq {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b) (size : I → ℕ) (d : ℕ)
    (ρ : ℝ) (duration : ℕ → ℕ) (k : ℕ) :
    P.budget size d ρ duration k = P.singletonWeight size d *
      (markedProduct P.markedFlags (P.times duration k) : ℝ) * ρ ^ (P.times duration k).sum := by
  induction P generalizing k <;>
    simp_all [budget, singletonWeight, times, NoncommutativeCS.EndpointSkeleton.markedFlags,
      markedProduct, pow_add, Nat.cast_mul] <;> ring

/-- The actual row, column, singleton and middle bounds, assembled along
the compiler's precise register program. -/
theorem decorate_cost_le {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : NoncommutativeCS.EndpointSkeleton I a b)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (hduration : ∀ k, 1 ≤ duration k) (k : ℕ) :
    (P.decorate (blockFactor B size profile hsize ordinary duration forward decode) k).compile.cost ≤
      P.budget size d ‖regular B‖ duration k := by
  induction P generalizing k with
  | done => rfl
  | first i P ih =>
      exact mul_le_mul (ih (k + 1))
        (HaarProfileBlockCoefficients.padded_endpoint_bounds B hB (ordinary k)
          (hduration k) (forward k i) (profile i) (hsize i)).1
        (Real.sqrt_nonneg _) (P.budget_nonneg size d (norm_nonneg _) duration (k + 1))
  | @last m n a b p P ih =>
      exact mul_le_mul (ih (k + 1))
        (HaarProfileBlockCoefficients.padded_endpoint_bounds B hB (ordinary k)
          (hduration k) (forward k (a p)) (profile (a p)) (hsize (a p))).2
        (Real.sqrt_nonneg _) (P.budget_nonneg size d (norm_nonneg _) duration (k + 1))
  | @middle m n a b v P ih =>
      have hm : ‖fun s : Fin m → Palette d M =>
          blockFactor B size profile hsize ordinary duration forward decode k (v.map a) (v.map s)‖ ≤
          ‖regular B‖ ^ duration k := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
        intro s
        exact blockFactor_norm_le B size profile hsize ordinary duration forward decode hduration k _ _
      exact mul_le_mul (ih (k + 1)) hm (norm_nonneg _)
        (P.budget_nonneg size d (norm_nonneg _) duration (k + 1))
  | singleton i P ih =>
      exact mul_le_mul (ih (k + 1))
        (HaarProfileBlockCoefficients.padded_singleton_bound B hB (ordinary k)
          (hduration k) (forward k i) (profile i) (hsize i))
        (norm_nonneg _) (P.budget_nonneg size d (norm_nonneg _) duration (k + 1))

/-- The actual fixed-pattern global coefficient sum has the sharp marked
duration product. No local operator-norm estimate appears as a hypothesis. -/
theorem profile_sum_norm_le [Fintype I]
    (P : NoncommutativeCS.EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels)
    (B : Polynomial (FreeGroup (Fin d)) E)
    (hB : ∀ g ∈ B.support, g.toWord.length ≤ 1)
    (size : I → ℕ) (profile : I → Profile (Color d)) (hsize : ∀ i, size i ≤ M)
    (ordinary : ℕ → Bool) (duration : ℕ → ℕ) (forward : ℕ → I → Bool)
    (decode : ℕ → List I → List (Palette d M) → FreeGroup (Fin d))
    (hduration : ∀ k, 1 ≤ duration k) (k : ℕ) :
    ‖∑ σ : I → Palette d M,
      (P.blockFactors (blockFactor B size profile hsize ordinary duration forward decode) k σ).prod‖ ≤
      P.singletonWeight size d * (markedProduct P.markedFlags (P.times duration k) : ℝ) *
        ‖regular B‖ ^ (P.times duration k).sum := by
  have h := (P.block_sum_norm_le _ k hn hc).trans
    (P.decorate_cost_le B hB size profile hsize ordinary duration forward decode hduration k)
  rwa [P.budget_eq] at h

end Nonadditivity.NoncommutativeCS.EndpointSkeleton
