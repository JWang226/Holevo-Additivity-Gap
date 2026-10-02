/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarTimeCompositions
import Nonadditivity.HaarPathRuns

/-! # The corrected marked-factor sum over actual positive time compositions

Only first and last visits carry a length factor. Consecutive interior visits
are compressed into one unmarked block. The literal sum over all positive
segment durations has the prescribed polynomial exponent even though the
published estimate on the number of interior blocks is false.
-/

namespace Nonadditivity.HaarMarkedCompositions

open scoped BigOperators
open HaarTimeCompositions HaarPathRuns

/-- Compress each consecutive unmarked interval to a single unmarked block. -/
def blocks : List Bool → List Bool
  | [] => []
  | a :: l => if a = false ∧ l.head? = some false then blocks l else a :: blocks l

theorem count_blocks (l : List Bool) : (blocks l).count true = l.count true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases a <;> simp only [blocks] <;> split_ifs <;> simp_all

theorem length_blocks (l : List Bool) :
    (blocks l).length = blockCount l + if l.getLast? = some false then 1 else 0 := by
  induction l with
  | nil => simp [blocks, blockCount, middleRuns]
  | cons a l ih =>
      cases l with
      | nil => cases a <;> simp [blocks, blockCount, middleRuns]
      | cons b l =>
          cases a <;> cases b <;>
            simp [blocks, blockCount, middleRuns] at * <;> omega

/-- The product of the durations at the marked positions only. -/
def markedProduct : List Bool → List ℕ → ℕ
  | [], _ => 1
  | _ :: _, [] => 1
  | b :: bs, t :: ts => (if b then t else 1) * markedProduct bs ts

theorem markedProduct_le {n : ℕ} (flags : List Bool) (times : List ℕ)
    (hn : 1 ≤ n) (ht : ∀ t ∈ times, t ≤ n) :
    markedProduct flags times ≤ n ^ flags.count true := by
  induction flags generalizing times with
  | nil => simp [markedProduct]
  | cons b flags ih =>
      cases times with
      | nil => simpa [markedProduct] using Nat.one_le_pow _ _ hn
      | cons t times =>
          have ht' := ht t (by simp)
          have htail : ∀ a ∈ times, a ≤ n := fun a ha => ht a (by simp [ha])
          cases b
          · simpa [markedProduct] using ih times htail
          · simpa [markedProduct, pow_succ, Nat.mul_comm] using
              Nat.mul_le_mul ht' (ih times htail)

/-- The exact sum of marked length factors over positive segment durations. -/
theorem marked_composition_sum_le (n : ℕ) (hn : 1 ≤ n) (flags : List Bool) :
    (∑ times ∈ compositions (flags.length - 1) n, markedProduct flags times) ≤
      n ^ (flags.length - 1 + flags.count true) := by
  calc
    _ ≤ ∑ _times ∈ compositions (flags.length - 1) n, n ^ flags.count true := by
      apply Finset.sum_le_sum
      intro times htimes
      apply markedProduct_le flags times hn
      intro t ht
      exact (List.le_sum_of_mem ht).trans_eq (sum_of_mem htimes)
    _ = (compositions (flags.length - 1) n).card * n ^ flags.count true := by simp
    _ ≤ n ^ (flags.length - 1) * n ^ flags.count true :=
      Nat.mul_le_mul_right _ (card_le _ _)
    _ = _ := (pow_add _ _ _).symm

/-- The repaired exponent applies to the actual compressed endpoint flags. -/
theorem blocks_exponent_le {l : List Bool} {e : ℕ}
    (hhead : l.head? = some true) (hlast : l.getLast? = some true)
    (hmarks : l.count true ≤ 2 * e) :
    (blocks l).length - 1 + (blocks l).count true ≤ 6 * e - 2 := by
  rw [length_blocks, count_blocks, hlast]
  simpa using corrected_exponent_le hhead hmarks

/-- Positive compositions of actual first/last blocks retain the target exponent. -/
theorem corrected_marked_sum_le {l : List Bool} {e : ℕ}
    (hhead : l.head? = some true) (hlast : l.getLast? = some true)
    (hmarks : l.count true ≤ 2 * e) (n : ℕ) (hn : 1 ≤ n) :
    (∑ times ∈ compositions ((blocks l).length - 1) n,
      markedProduct (blocks l) times) ≤ n ^ (6 * e - 2) := by
  exact (marked_composition_sum_le n hn (blocks l)).trans
    (Nat.pow_le_pow_right hn (blocks_exponent_le hhead hlast hmarks))

end Nonadditivity.HaarMarkedCompositions
