/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeylPowersIndex
import Nonadditivity.WeylPowersControl

/-! # Exact identification of every tensor power of a controlled unitary extension -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.WeylPowers

open Entropy Channels Channels.KrausChannel RegularizedHolevo
open scoped BigOperators Kronecker Matrix

variable {ι ο κ ζ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype ζ] [DecidableEq ζ]

theorem positiveTensorPower_covariant_kraus (T : KrausChannel ι ο κ)
    (U : ζ → unitary (Matrix ο ο ℂ)) (n : ℕ)
    (k : PositiveTensorIndex (ζ × κ) n)
    (a : PositiveTensorIndex ο n) (b : PositiveTensorIndex (ζ × ι) n) :
    (positiveTensorPower (T.covariantExtension U) n).kraus k a b =
      ((positiveTensorPower T n).covariantExtension (positiveUnitaryPower U n)).kraus
        (positivePairEquiv ζ κ n k) a (positivePairEquiv ζ ι n b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases k with ⟨k, ⟨z, k'⟩⟩
    rcases a with ⟨a, a'⟩
    rcases b with ⟨b, ⟨w, b'⟩⟩
    change (positiveTensorPower (T.covariantExtension U) n).kraus k a b *
      (T.covariantExtension U).kraus (z,k') a' (w,b') = _
    rw [ih]
    rw [covariantExtension_kraus_apply, covariantExtension_kraus_apply,
      covariantExtension_kraus_apply]
    change
      (if ((positivePairEquiv ζ ι n) b).1 = ((positivePairEquiv ζ κ n) k).1 then
        ((positiveUnitaryPower U n ((positivePairEquiv ζ κ n) k).1 :
            Matrix (PositiveTensorIndex ο n) (PositiveTensorIndex ο n) ℂ) *
          (positiveTensorPower T n).kraus ((positivePairEquiv ζ κ n) k).2)
            a ((positivePairEquiv ζ ι n) b).2 else 0) *
      (if w = z then ((U z : Matrix ο ο ℂ) * T.kraus k') a' b' else 0) =
      if (((positivePairEquiv ζ ι n) b).1, w) =
          (((positivePairEquiv ζ κ n) k).1, z) then
        (((positiveUnitaryPower U n ((positivePairEquiv ζ κ n) k).1 :
            Matrix (PositiveTensorIndex ο n) (PositiveTensorIndex ο n) ℂ) ⊗ₖ
          (U z : Matrix ο ο ℂ)) *
          ((positiveTensorPower T n).kraus ((positivePairEquiv ζ κ n) k).2 ⊗ₖ
            T.kraus k')) (a,a') (((positivePairEquiv ζ ι n) b).2,b') else 0
    rw [← Matrix.mul_kronecker_mul]
    simp only [Matrix.kroneckerMap_apply, Prod.mk.injEq]
    split_ifs <;> simp_all

/-- The reindexed actual extension power is the extension of the actual power.
This includes all entangled inputs, since it is equality of Kraus channels. -/
theorem positiveTensorPower_covariant (T : KrausChannel ι ο κ)
    (U : ζ → unitary (Matrix ο ο ℂ)) (n : ℕ) :
    (((positiveTensorPower (T.covariantExtension U) n).reindex
      (positivePairEquiv ζ ι n) (Equiv.refl _)).reindexKraus
        (positivePairEquiv ζ κ n)) =
      (positiveTensorPower T n).covariantExtension (positiveUnitaryPower U n) := by
  apply KrausChannel.ext
  funext k
  ext a b
  have h := positiveTensorPower_covariant_kraus T U n
    ((positivePairEquiv ζ κ n).symm k) a ((positivePairEquiv ζ ι n).symm b)
  simpa only [Equiv.apply_symm_apply] using h

theorem positiveTensorPower_covariant_holevo [Nonempty ι] [Nonempty ο] [Nonempty ζ]
    (T : KrausChannel ι ο κ) (U : ζ → unitary (Matrix ο ο ℂ)) (n : ℕ) :
    (positiveTensorPower (T.covariantExtension U) n).holevo =
      ((positiveTensorPower T n).covariantExtension (positiveUnitaryPower U n)).holevo := by
  rw [← positiveTensorPower_covariant]
  rw [holevo_eq_of_map_eq _ _ (fun X => reindexKraus_map _ _ X), holevo_reindex]

end Nonadditivity.WeylPowers
