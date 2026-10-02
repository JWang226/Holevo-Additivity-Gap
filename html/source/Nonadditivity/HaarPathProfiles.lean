/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Count
import Mathlib.Tactic

/-! # Finite word-profile counts for the Haar path expansion

A path segment is profiled by its first color, last color and the number
of occurrences of every color. The bound is the profile-count ingredient
of Bordenave--Collins, Lemma 5.8. Subtracting the first color before encoding
is essential: the remaining multiplicities lie in `Fin m`, not `Fin (m+1)`.
The statement here concerns actual profiles of nonempty words of length
at most `m`; no profile-count hypothesis is assumed.
-/
noncomputable section
namespace Nonadditivity.HaarPathProfiles

variable {α : Type*} [DecidableEq α]

/-- The data retained by the refined path equivalence relation. -/
@[ext] structure Profile (α : Type*) where
  first : α
  last : α
  count : α → ℕ

/-- Literal profile of the nonempty word `a :: l`. -/
def wordProfile (a : α) (l : List α) : Profile α where
  first := a
  last := (a :: l).getLast (by simp)
  count := fun x => (a :: l).count x

/-- Realizable profiles, with the full word length bounded by `m`. -/
def BoundedProfile (α : Type*) [DecidableEq α] (m : ℕ) :=
  {p : Profile α // ∃ a l, l.length < m ∧ wordProfile a l = p}

/-- Deleting the first letter leaves fewer than `m` occurrences of every color. -/
theorem residual_count_lt {m : ℕ} (p : BoundedProfile α m) (x : α) :
    p.val.count x - (if x = p.val.first then 1 else 0) < m := by
  obtain ⟨a, l, hl, hp⟩ := p.property
  rw [← hp]
  change (a :: l).count x - (if x = a then 1 else 0) < m
  have hc := lt_of_le_of_lt (List.count_le_length (a := x) (l := l)) hl
  by_cases h : x = a
  · subst x; simpa using hc
  · simpa [List.count_cons, h, Ne.symm h] using hc

/-- The deleted first letter can be recovered without truncated-subtraction loss. -/
theorem count_eq_residual_add {m : ℕ} (p : BoundedProfile α m) (x : α) :
    p.val.count x =
      (p.val.count x - (if x = p.val.first then 1 else 0)) +
        (if x = p.val.first then 1 else 0) := by
  obtain ⟨a, l, hl, hp⟩ := p.property
  rw [← hp]
  change (a :: l).count x =
    ((a :: l).count x - (if x = a then 1 else 0)) + (if x = a then 1 else 0)
  by_cases h : x = a
  · subst x; simp
  · simp [h]

/-- Explicit bounded encoding, independent of the underlying graph vertices. -/
def encode {m : ℕ} (p : BoundedProfile α m) : α × α × (α → Fin m) :=
  (p.val.first, p.val.last,
    fun x => ⟨p.val.count x - (if x = p.val.first then 1 else 0),
      residual_count_lt p x⟩)

theorem encode_injective {m : ℕ} : Function.Injective (encode (α := α) (m := m)) := by
  intro p q h
  have hf : p.val.first = q.val.first := congrArg (fun z => z.1) h
  have hl : p.val.last = q.val.last := congrArg (fun z => z.2.1) h
  have hc : p.val.count = q.val.count := by
    funext x
    have hx := congrArg (fun z : α × α × (α → Fin m) => (z.2.2 x).val) h
    change p.val.count x - (if x = p.val.first then 1 else 0) =
      q.val.count x - (if x = q.val.first then 1 else 0) at hx
    rw [count_eq_residual_add p x, count_eq_residual_add q x, hx, hf]
  exact Subtype.ext (Profile.ext hf hl hc)

instance boundedProfileFintype [Fintype α] (m : ℕ) : Fintype (BoundedProfile α m) :=
  Fintype.ofInjective encode encode_injective

/-- Profile-count bound for an arbitrary finite alphabet. -/
theorem card_boundedProfile_le [Fintype α] (m : ℕ) :
    Fintype.card (BoundedProfile α m) ≤
      Fintype.card α ^ 2 * m ^ Fintype.card α := by
  calc
    _ ≤ Fintype.card (α × α × (α → Fin m)) :=
      Fintype.card_le_of_injective encode encode_injective
    _ = _ := by simp [pow_two, mul_assoc]

/-- Profiles chosen on each core edge have an exponential count only in the
number of core edges, rather than in the original path length. -/
theorem card_profileAssignments_le [Fintype α] {E : Type*} [Fintype E] [DecidableEq E] (m : ℕ) :
    Fintype.card (E → BoundedProfile α m) ≤
      (Fintype.card α ^ 2 * m ^ Fintype.card α) ^ Fintype.card E := by
  rw [Fintype.card_fun]
  exact Nat.pow_le_pow_left (card_boundedProfile_le (α := α) m) _

/-- The signed `d`-generator alphabet used for unitary matrices and their adjoints. -/
abbrev Color (d : ℕ) := Fin d × Bool

/-- Exact base in Bordenave--Collins Lemma 5.8, before the core-edge estimate. -/
theorem card_signedProfile_le (d m : ℕ) :
    Fintype.card (BoundedProfile (Color d) m) ≤ (2*d*m^d)^2 := by
  have h := card_boundedProfile_le (α := Color d) m
  have he : Fintype.card (Color d)^2 * m^Fintype.card (Color d) =
      (2*d*m^d)^2 := by
    simp only [Color, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [pow_mul, mul_pow]
    ring
  exact he ▸ h

/-- In particular, two independent Haar generators need at most `(4*m^2)^2`
profiles on each compressed edge. -/
theorem card_twoGeneratorProfile_le (m : ℕ) :
    Fintype.card (BoundedProfile (Color 2) m) ≤ (4*m^2)^2 := by
  simpa using card_signedProfile_le 2 m

end Nonadditivity.HaarPathProfiles
