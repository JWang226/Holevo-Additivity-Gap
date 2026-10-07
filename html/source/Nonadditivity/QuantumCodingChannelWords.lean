/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.QuantumCodingFamilySpectrum
import Nonadditivity.OperationalCapacity
import Nonadditivity.OperationalReindex

/-! # Word coordinates for actual channel tensor powers

The product states used by spectral coding are identified with the nested
tensor indices of the actual Kraus channel. No channel-output identity is
supplied as a coding hypothesis.
-/
noncomputable section
namespace Nonadditivity.QuantumCoding
open Entropy Channels Channels.KrausChannel RegularizedHolevo Operational
open scoped BigOperators Matrix Kronecker
set_option backward.isDefEq.respectTransparency false

def positiveWordEquiv (ι : Type*) : (n : ℕ) → PositiveTensorIndex ι n ≃ (Fin (n+1) → ι)
  | 0 =>
    { toFun := fun a _ => a
      invFun := fun f => f 0
      left_inv := fun _ => rfl
      right_inv := fun f => by funext i; fin_cases i; rfl }
  | n+1 =>
    ((Equiv.prodCongr (positiveWordEquiv ι n) (Equiv.refl ι)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ : Fin (n+2) => ι))

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- The product input on exactly `n+1` genuine channel tensor factors. -/
def productInputState : (n : ℕ) → (Fin (n+1) → DensityMatrix ι) →
    DensityMatrix (PositiveTensorIndex ι n)
  | 0, ρ => ρ 0
  | n+1, ρ => (productInputState n (fun j => ρ j.castSucc)).tensor (ρ (Fin.last (n+1)))

theorem productInputState_entries (n : ℕ) (ρ : Fin (n+1) → DensityMatrix ι)
    (x y : PositiveTensorIndex ι n) :
    (productInputState n ρ).matrix x y =
      ∏ j, (ρ j).matrix (positiveWordEquiv ι n x j) (positiveWordEquiv ι n y j) := by
  induction n with
  | zero => simp [productInputState,positiveWordEquiv]
  | succ n ih =>
    rcases x with ⟨x,i⟩
    rcases y with ⟨y,j⟩
    rw [Fin.prod_univ_castSucc]
    change (productInputState n (fun k => ρ k.castSucc)).matrix x y *
      (ρ (Fin.last (n+1))).matrix i j = _
    rw [ih]
    simp [positiveWordEquiv,Fin.snocEquiv]
    rfl

/-- The word-basis tensor state is the exact reindexing of the channel input. -/
theorem productInputState_reindex (n : ℕ) (ρ : Fin (n+1) → DensityMatrix ι) :
    (productInputState n ρ).reindex (positiveWordEquiv ι n)=tensorFamilyState ρ := by
  apply DensityMatrix.ext
  ext x y
  change (productInputState n ρ).matrix ((positiveWordEquiv ι n).symm x)
    ((positiveWordEquiv ι n).symm y) = _
  rw [productInputState_entries]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Actual product inputs give the componentwise channel outputs. -/
theorem positiveTensorPower_productInputState (T : KrausChannel ι ο κ)
    (n : ℕ) (ρ : Fin (n+1) → DensityMatrix ι) :
    (positiveTensorPower T n).output (productInputState n ρ) =
      productInputState n (fun j => T.output (ρ j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((positiveTensorPower T n).tensor T).output
      ((productInputState n (fun j => ρ j.castSucc)).tensor (ρ (Fin.last (n+1)))) = _
    rw [tensor_output,ih]
    rfl

theorem positiveTensorPower_word_output (T : KrausChannel ι ο κ)
    (n : ℕ) (ρ : Fin (n+1) → DensityMatrix ι) :
    ((positiveTensorPower T n).output (productInputState n ρ)).reindex
      (positiveWordEquiv ο n) = tensorFamilyState (fun j => T.output (ρ j)) := by
  rw [positiveTensorPower_productInputState,productInputState_reindex]

/-- A selected word codebook and its word-basis POVM give an actual channel code. -/
def wordCode (T : KrausChannel ι ο κ) (n M : ℕ)
    (ρ : Fin M → Fin (n+1) → DensityMatrix ι)
    (D : POVM (Fin (n+1) → ο) (Fin M)) : Code (positiveTensorPower T n) M where
  encode := fun m => productInputState n (ρ m)
  decode := D.reindex (positiveWordEquiv ο n).symm

theorem wordCode_probability (T : KrausChannel ι ο κ) (n M : ℕ)
    (ρ : Fin M → Fin (n+1) → DensityMatrix ι)
    (D : POVM (Fin (n+1) → ο) (Fin M)) (m : Fin M) :
    (wordCode T n M ρ D).decode.probability
      ((positiveTensorPower T n).output ((wordCode T n M ρ D).encode m)) m =
      D.probability (tensorFamilyState (fun j => T.output (ρ m j))) m := by
  let σ := (positiveTensorPower T n).output (productInputState n (ρ m))
  have he : (σ.reindex (positiveWordEquiv ο n)).reindex
      (positiveWordEquiv ο n).symm = σ := by
    apply DensityMatrix.ext
    ext i j
    simp [DensityMatrix.reindex,Matrix.reindex_apply]
  have h := D.probability_reindex (positiveWordEquiv ο n).symm
    (σ.reindex (positiveWordEquiv ο n)) m
  rw [he] at h
  change (D.reindex (positiveWordEquiv ο n).symm).probability σ m = _
  rw [h]
  dsimp [σ]
  rw [positiveTensorPower_word_output]

theorem wordCode_error (T : KrausChannel ι ο κ) (n M : ℕ)
    (ρ : Fin M → Fin (n+1) → DensityMatrix ι)
    (D : POVM (Fin (n+1) → ο) (Fin M)) :
    (wordCode T n M ρ D).error =
      1-(∑ m, D.probability (tensorFamilyState (fun j => T.output (ρ m j))) m)/(M:ℝ) := by
  simp only [Code.error,Code.success,wordCode_probability]

end Nonadditivity.QuantumCoding
