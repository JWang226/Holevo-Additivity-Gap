/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.OperationalBlockingCodes

/-! # Exact flattening of physical block-channel codes -/
noncomputable section
namespace Nonadditivity.Operational
open Entropy Channels RegularizedHolevo
open scoped BigOperators Matrix ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false

/-- The positive tensor index of `n+1` consecutive blocks of `k+1` uses. -/
def blockedIndex (k : ℕ) : ℕ → ℕ
  | 0 => k
  | n+1 => blockedIndex k n+k+1

@[simp] theorem blockedIndex_add_one (k n : ℕ) :
    blockedIndex k n+1=(k+1)*(n+1) := by
  induction n with
  | zero => simp [blockedIndex]
  | succ n ih =>
    simp only [blockedIndex]
    nlinarith

/-- Regroup consecutive channel coordinates into genuine tensor blocks. -/
def blockedEquiv (ι : Type*) (k : ℕ) : (n : ℕ) →
    PositiveTensorIndex ι (blockedIndex k n) ≃
      PositiveTensorIndex (PositiveTensorIndex ι k) n
  | 0 => Equiv.refl _
  | n+1 => (positiveTensorSplit ι (blockedIndex k n) k).trans
      ((blockedEquiv ι k n).prodCongr (Equiv.refl _))

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- The block equivalence exactly identifies every actual Kraus coefficient. -/
theorem blockedEquiv_kraus (T : KrausChannel ι ο κ) (k n : ℕ)
    (e : PositiveTensorIndex κ (blockedIndex k n))
    (a : PositiveTensorIndex ο (blockedIndex k n))
    (b : PositiveTensorIndex ι (blockedIndex k n)) :
    (positiveTensorPower T (blockedIndex k n)).kraus e a b =
      (positiveTensorPower (positiveTensorPower T k) n).kraus
        (blockedEquiv κ k n e) (blockedEquiv ο k n a) (blockedEquiv ι k n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (positiveTensorPower T (blockedIndex k n+k+1)).kraus e a b = _
    rw [positiveTensorSplit_kraus T (blockedIndex k n) k]
    simp only [KrausChannel.tensor, Matrix.kroneckerMap_apply]
    rw [ih]
    rfl

/-- The entire block channel equals the flat channel after relabeling actual
input, output, and Kraus coordinates. -/
theorem blockedPower_eq (T : KrausChannel ι ο κ) (k n : ℕ) :
    (((positiveTensorPower T (blockedIndex k n)).reindex
      (blockedEquiv ι k n) (blockedEquiv ο k n)).reindexKraus (blockedEquiv κ k n)) =
      positiveTensorPower (positiveTensorPower T k) n := by
  apply KrausChannel.ext
  funext e
  ext a b
  have h := blockedEquiv_kraus T k n ((blockedEquiv κ k n).symm e)
    ((blockedEquiv ο k n).symm a) ((blockedEquiv ι k n).symm b)
  simpa only [Equiv.apply_symm_apply] using h

/-- The reverse regrouping identity for actual density matrices. -/
theorem blockedPower_map (T : KrausChannel ι ο κ) (k n : ℕ)
    (X : Matrix (PositiveTensorIndex (PositiveTensorIndex ι k) n)
      (PositiveTensorIndex (PositiveTensorIndex ι k) n) ℂ) :
    (positiveTensorPower T (blockedIndex k n)).map
      (Matrix.reindex (blockedEquiv ι k n).symm (blockedEquiv ι k n).symm X) =
      Matrix.reindex (blockedEquiv ο k n).symm (blockedEquiv ο k n).symm
        ((positiveTensorPower (positiveTensorPower T k) n).map X) := by
  apply (Matrix.reindex (blockedEquiv ο k n) (blockedEquiv ο k n)).injective
  rw [←KrausChannel.reindex_map (positiveTensorPower T (blockedIndex k n))
    (blockedEquiv ι k n) (blockedEquiv ο k n)
    (Matrix.reindex (blockedEquiv ι k n).symm (blockedEquiv ι k n).symm X)]
  have hi : Matrix.reindex (blockedEquiv ι k n) (blockedEquiv ι k n)
      (Matrix.reindex (blockedEquiv ι k n).symm (blockedEquiv ι k n).symm X)=X := by
    ext a b
    simp [Matrix.reindex_apply]
  rw [hi]
  rw [←KrausChannel.reindexKraus_map _ (blockedEquiv κ k n),blockedPower_eq]
  ext a b
  simp [Matrix.reindex_apply]

namespace Code

/-- Decode a block-channel code on precisely its consecutive elementary uses. -/
def flatten (T : KrausChannel ι ο κ) (k n : ℕ) {M : ℕ}
    (C : Code (positiveTensorPower (positiveTensorPower T k) n) M) :
    Code (positiveTensorPower T (blockedIndex k n)) M :=
  C.transport _ (blockedEquiv ι k n).symm (blockedEquiv ο k n).symm

@[simp] theorem flatten_error (T : KrausChannel ι ο κ) (k n : ℕ) {M : ℕ}
    (C : Code (positiveTensorPower (positiveTensorPower T k) n) M) :
    (C.flatten T k n).error=C.error :=
  transport_error C _ _ _ (blockedPower_map T k n)

end Code
end Nonadditivity.Operational
