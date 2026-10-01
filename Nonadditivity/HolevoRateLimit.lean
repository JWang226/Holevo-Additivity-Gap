/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HolevoTensorSuperadditivity
import Nonadditivity.RegularizedHolevo
import Mathlib.Analysis.Subadditive

/-! # The regularized Holevo supremum is the actual tensor-power rate limit

We prove tensor-power superadditivity using actual product ensembles and an
explicit associativity equivalence of the input, output and Kraus bases, then
apply Fekete's lemma. No operational coding theorem is asserted.
-/

noncomputable section

namespace Nonadditivity.RegularizedHolevo

open Entropy Channels Channels.KrausChannel ActualConsequences
open Filter Topology
open scoped Kronecker Matrix

universe u

/-- Split a positive tensor chain into two positive blocks. -/
def positiveTensorSplit (ι : Type u) (m : ℕ) : (n : ℕ) →
    PositiveTensorIndex ι (m + n + 1) ≃
      PositiveTensorIndex ι m × PositiveTensorIndex ι n
  | 0 => Equiv.refl _
  | n + 1 => ((positiveTensorSplit ι m n).prodCongr (Equiv.refl ι)).trans
      (Equiv.prodAssoc _ _ _)

variable {ι ο κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- The concrete Kraus coefficients regroup under the tensor split. -/
theorem positiveTensorSplit_kraus (T : KrausChannel ι ο κ) (m n : ℕ)
    (k : PositiveTensorIndex κ (m + n + 1))
    (a : PositiveTensorIndex ο (m + n + 1))
    (b : PositiveTensorIndex ι (m + n + 1)) :
    (positiveTensorPower T (m + n + 1)).kraus k a b =
      ((positiveTensorPower T m).tensor (positiveTensorPower T n)).kraus
        (positiveTensorSplit κ m n k) (positiveTensorSplit ο m n a)
        (positiveTensorSplit ι m n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (positiveTensorPower T (m + n + 1)).kraus k.1 a.1 b.1 *
      T.kraus k.2 a.2 b.2 = _
    rw [ih]
    simp only [tensor, Matrix.kroneckerMap_apply, positiveTensorSplit,
      positiveTensorPower]
    exact mul_assoc _ _ _

/-- Regrouping tensor powers is equality of actual Kraus channels after basis
and environment relabeling. -/
theorem positiveTensorPower_split (T : KrausChannel ι ο κ) (m n : ℕ) :
    (((positiveTensorPower T (m + n + 1)).reindex
      (positiveTensorSplit ι m n) (positiveTensorSplit ο m n)).reindexKraus
        (positiveTensorSplit κ m n)) =
      (positiveTensorPower T m).tensor (positiveTensorPower T n) := by
  apply KrausChannel.ext
  funext k
  ext a b
  have h := positiveTensorSplit_kraus T m n
    ((positiveTensorSplit κ m n).symm k)
    ((positiveTensorSplit ο m n).symm a)
    ((positiveTensorSplit ι m n).symm b)
  simpa only [Equiv.apply_symm_apply] using h

theorem positiveTensorPower_holevoBits_superadditive [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) (m n : ℕ) :
    (positiveTensorPower T m).holevoBits + (positiveTensorPower T n).holevoBits ≤
      (positiveTensorPower T (m + n + 1)).holevoBits := by
  have h := (positiveTensorPower T m).holevoBits_tensor_superadditive (positiveTensorPower T n)
  rw [← positiveTensorPower_split] at h
  have he := holevoBits_eq_of_map_eq
    (((positiveTensorPower T (m + n + 1)).reindex
      (positiveTensorSplit ι m n) (positiveTensorSplit ο m n)).reindexKraus
        (positiveTensorSplit κ m n))
    ((positiveTensorPower T (m + n + 1)).reindex
      (positiveTensorSplit ι m n) (positiveTensorSplit ο m n))
    (fun X => reindexKraus_map _ _ X)
  rw [he, holevoBits_reindex] at h
  exact h

/-- Unnormalized actual tensor-power Holevo information, with the zero-use
value defined to be zero. Positive entries retain all actual channel data. -/
def powerHolevo (T : KrausChannel ι ο κ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (positiveTensorPower T n).holevoBits

@[simp] theorem powerHolevo_zero (T : KrausChannel ι ο κ) : powerHolevo T 0 = 0 := rfl
@[simp] theorem powerHolevo_succ (T : KrausChannel ι ο κ) (n : ℕ) :
    powerHolevo T (n + 1) = (positiveTensorPower T n).holevoBits := rfl

theorem powerHolevo_superadditive [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) (m n : ℕ) :
    powerHolevo T m + powerHolevo T n ≤ powerHolevo T (m + n) := by
  cases m with
  | zero => simp
  | succ m =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [Nat.succ_add, Nat.add_succ, powerHolevo_succ] using
        positiveTensorPower_holevoBits_superadditive T m n

end Nonadditivity.RegularizedHolevo

namespace Nonadditivity.ActualConsequences.FiniteQuantumChannel

open Nonadditivity.RegularizedHolevo
open Filter Topology

/-- The normalized Holevo informations of all positive tensor powers converge
to their supremum. This is the actual channel rate limit, proved without an
operational coding theorem or any additional analytic assumption. -/
theorem normalizedPowerHolevo_tendsto (T : FiniteQuantumChannel) :
    Tendsto (normalizedPowerHolevo T.channel) atTop (𝓝 T.regularizedHolevo) := by
  have hsub : Subadditive (fun n => -powerHolevo T.channel n) := by
    intro m n
    have h := powerHolevo_superadditive T.channel m n
    linarith
  have hb : BddBelow (Set.range fun n => -powerHolevo T.channel n / (n : ℝ)) := by
    refine ⟨-T.regularizedHolevo, ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => simpa using T.regularizedHolevo_nonneg
    | succ n =>
      have h := T.normalizedPowerHolevo_le_regularized n
      simpa only [powerHolevo_succ, normalizedPowerHolevo, neg_div] using neg_le_neg h
  have hlim : Tendsto (normalizedPowerHolevo T.channel) atTop (𝓝 (-hsub.lim)) := by
    have h := (hsub.tendsto_lim hb).neg.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, powerHolevo_succ, neg_div, neg_neg,
      normalizedPowerHolevo] using h
  have he : -hsub.lim = T.regularizedHolevo := by
    apply le_antisymm
    · exact le_of_tendsto' hlim T.normalizedPowerHolevo_le_regularized
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n, rfl⟩
      have h := hsub.lim_le_div hb (n := n + 1) (by omega)
      have h' := neg_le_neg h
      simpa only [powerHolevo_succ, neg_div, neg_neg, normalizedPowerHolevo] using h'
  rwa [he] at hlim

end Nonadditivity.ActualConsequences.FiniteQuantumChannel
