/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalBlockingFlatten
import Nonadditivity.OperationalBlockRates

/-! # Operational rate rescaling for genuine channel blocks

Every code for a fixed channel block is flattened into its actual elementary
uses, and the fewer-than-one-block remaining uses are ignored. This constructs
codes for all positive lengths with exactly preserved error eventually.
-/
noncomputable section
namespace Nonadditivity.Operational
open Entropy Channels RegularizedHolevo Filter Topology
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false

/-- Complete blocks occupy no more than the prescribed positive length. -/
theorem blockedIndex_le_length (k n : ℕ) (h : k≤n) :
    blockedIndex k (BlockRates.blockIndex k n)≤n := by
  have he := blockedIndex_add_one k (BlockRates.blockIndex k n)
  rw [BlockRates.blockIndex_add_one h] at he
  have hd := Nat.div_mul_le_self (n+1) (k+1)
  dsimp [BlockRates.blockCount] at he
  nlinarith

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

namespace CodeSequence

/-- A jointly bundled message count and code avoids any artificial
message-alphabet casts when selecting a complete block count. -/
def unblockPacket (T : KrausChannel ι ο κ) (k : ℕ)
    (S : CodeSequence (positiveTensorPower T k)) (n : ℕ) :
    Σ M : ℕ, Code (positiveTensorPower T n) M :=
  if h : k≤n then
    ⟨S.messages (BlockRates.blockIndex k n),
      Code.padTo T ((S.code (BlockRates.blockIndex k n)).flatten T k _)
        (blockedIndex_le_length k n h)⟩
  else ⟨1,oneMessage (positiveTensorPower T n)⟩

/-- Actual full-length coding sequence obtained by flattening complete blocks
and padding their final unused positions. Early short lengths carry one message. -/
def unblock (T : KrausChannel ι ο κ) (k : ℕ)
    (S : CodeSequence (positiveTensorPower T k)) : CodeSequence T where
  messages := fun n => (unblockPacket T k S n).1
  messages_pos := by
    intro n
    unfold unblockPacket
    split_ifs
    · exact S.messages_pos _
    · exact Nat.zero_lt_one
  code := fun n => (unblockPacket T k S n).2

omit [Nonempty ο] in
@[simp] theorem unblock_error (T : KrausChannel ι ο κ) (k : ℕ)
    (S : CodeSequence (positiveTensorPower T k)) (n : ℕ) (h : k≤n) :
    ((S.unblock T k).code n).error=(S.code (BlockRates.blockIndex k n)).error := by
  change (fun B : Σ M : ℕ, Code (positiveTensorPower T n) M => B.2.error)
    (unblockPacket T k S n) = _
  rw [unblockPacket,dif_pos h]
  exact (Code.padTo_error T _ _).trans (Code.flatten_error T k _ _)

omit [Nonempty ο] in
theorem unblock_vanishingError (T : KrausChannel ι ο κ) (k : ℕ)
    (S : CodeSequence (positiveTensorPower T k)) (hE : S.VanishingError) :
    (S.unblock T k).VanishingError := by
  apply (BlockRates.error_subsequence k hE).congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (unblock_error T k S n hn).symm

omit [Nonempty ο] in
theorem unblock_hasRate (T : KrausChannel ι ο κ) (k : ℕ)
    (S : CodeSequence (positiveTensorPower T k)) {R : ℝ} (hR : S.HasRate R) :
    (S.unblock T k).HasRate (R / ((k+1 : ℕ) : ℝ)) := by
  have hs := BlockRates.rescaled_rate k (fun n => Scalar.log2 (S.messages n)) hR
  intro r hr
  filter_upwards [hs r hr,eventually_ge_atTop k] with n hn hkn
  simpa only [rate,unblock,unblockPacket,dif_pos hkn] using hn

end CodeSequence

omit [Nonempty ο] in
/-- Every operational rate on a block of `k+1` uses yields its rescaled rate
on the original channel, with codes at every positive block length. -/
theorem achievableRate_of_block {T : KrausChannel ι ο κ} (k : ℕ) {R : ℝ}
    (hR : AchievableRate (positiveTensorPower T k) R) :
    AchievableRate T (R / ((k+1 : ℕ) : ℝ)) := by
  obtain ⟨S,hE,hR⟩ := hR
  exact ⟨S.unblock T k, S.unblock_vanishingError T k hE, S.unblock_hasRate T k hR⟩

/-- Operational block capacity cannot exceed its number of elementary uses
times the original channel's operational capacity. -/
theorem operationalCapacity_block_le (T : KrausChannel ι ο κ) (k : ℕ) :
    operationalCapacity (positiveTensorPower T k) ≤
      ((k+1 : ℕ) : ℝ)*operationalCapacity T := by
  apply csSup_le ⟨0,zero_achievable _⟩
  intro R hR
  have h := achievableRate_le_capacity (achievableRate_of_block k hR)
  have hk : (0 : ℝ)<((k+1 : ℕ) : ℝ) := by positivity
  exact (div_le_iff₀ hk).mp h |>.trans_eq (mul_comm _ _)

end Nonadditivity.Operational
