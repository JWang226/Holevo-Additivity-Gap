/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.NatAntidiagonal
import Mathlib.Tactic

/-! # Positive time compositions for successive last-return cuts -/

namespace Nonadditivity.HaarTimeCompositions

open scoped BigOperators

/-- `cuts + 1` positive durations, with prescribed total `n`. -/
def compositions : ℕ → ℕ → Finset (List ℕ)
  | 0, n => if n = 0 then ∅ else {[n]}
  | cuts + 1, n => (Finset.range n).biUnion fun k =>
      (compositions cuts (n - (k + 1))).image (List.cons (k + 1))

@[simp] theorem compositions_zero (cuts : ℕ) : compositions cuts 0 = ∅ := by
  cases cuts <;> simp [compositions]

theorem length_of_mem {cuts n : ℕ} {t : List ℕ} (ht : t ∈ compositions cuts n) :
    t.length = cuts + 1 := by
  induction cuts generalizing n t with
  | zero =>
      simp only [compositions] at ht
      split_ifs at ht with hn
      · simp at ht
      · simp only [Finset.mem_singleton] at ht
        simp [ht]
  | succ cuts ih =>
      simp only [compositions, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image] at ht
      obtain ⟨k, hk, u, hu, rfl⟩ := ht
      simp [ih hu]

theorem sum_of_mem {cuts n : ℕ} {t : List ℕ} (ht : t ∈ compositions cuts n) :
    t.sum = n := by
  induction cuts generalizing n t with
  | zero =>
      simp only [compositions] at ht
      split_ifs at ht with hn
      · simp at ht
      · simp only [Finset.mem_singleton] at ht
        simp [ht]
  | succ cuts ih =>
      simp only [compositions, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image] at ht
      obtain ⟨k, hk, u, hu, rfl⟩ := ht
      rw [List.sum_cons, ih hu]
      omega

theorem positive_of_mem {cuts n : ℕ} {t : List ℕ} (ht : t ∈ compositions cuts n) :
    ∀ k ∈ t, 0 < k := by
  induction cuts generalizing n t with
  | zero =>
      simp only [compositions] at ht
      split_ifs at ht with hn
      · simp at ht
      · simp only [Finset.mem_singleton] at ht
        subst t
        simpa using Nat.pos_of_ne_zero hn
  | succ cuts ih =>
      simp only [compositions, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_image] at ht
      obtain ⟨k, hk, u, hu, rfl⟩ := ht
      simpa using And.intro (Nat.zero_lt_succ k) (ih hu)

/-- The exponent counts only the freely chosen cut times. -/
theorem card_le (cuts n : ℕ) : (compositions cuts n).card ≤ n ^ cuts := by
  induction cuts generalizing n with
  | zero =>
      by_cases hn : n = 0 <;> simp [compositions, hn]
  | succ cuts ih =>
      calc
        _ ≤ ∑ k ∈ Finset.range n,
            ((compositions cuts (n - (k + 1))).image (List.cons (k + 1))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ k ∈ Finset.range n, n ^ cuts := by
          apply Finset.sum_le_sum
          intro k hk
          exact (Finset.card_image_le).trans
            ((ih _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) cuts))
        _ = n ^ (cuts + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Summation over compositions is the literal nested sum over first cuts. -/
theorem sum_succ {R : Type*} [AddCommMonoid R] (cuts n : ℕ) (f : List ℕ → R) :
    ∑ t ∈ compositions (cuts + 1) n, f t =
      ∑ k ∈ Finset.range n, ∑ t ∈ compositions cuts (n - (k + 1)), f ((k + 1) :: t) := by
  rw [compositions, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_image (fun _ _ _ _ h => List.cons.inj h |>.2)
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro t hti htj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp htj
    have := (List.cons.inj he).1
    omega

end Nonadditivity.HaarTimeCompositions
