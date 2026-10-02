/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Channels
import Nonadditivity.EntropyProducts
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Channel reindexing and environment-coordinate identities

These are actual finite matrix identities. In particular, complementing a tensor
product and conjugating a complement commute without an assumed entropy law.
-/

noncomputable section

namespace Nonadditivity

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

namespace Entropy

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

/-- Relabel an actual density matrix by a basis equivalence. -/
def DensityMatrix.reindex (ρ : DensityMatrix ι) (e : ι ≃ μ) : DensityMatrix μ where
  matrix := Matrix.reindex e e ρ.matrix
  positive := ρ.positive.submatrix e.symm
  normalized := by
    change (∑ j, ρ.matrix (e.symm j) (e.symm j)) = 1
    exact (e.symm.sum_comp (fun i => ρ.matrix i i)).trans ρ.normalized

/-- Relabeling preserves the actual von Neumann entropy, via characteristic roots. -/
theorem DensityMatrix.reindex_entropy (ρ : DensityMatrix ι) (e : ι ≃ μ) :
    (ρ.reindex e).vonNeumann = ρ.vonNeumann := by
  have hc : (ρ.reindex e).matrix.charpoly = ρ.matrix.charpoly :=
    Matrix.charpoly_reindex e ρ.matrix
  have he := (ρ.reindex e).positive.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hc, ρ.positive.isHermitian.roots_charpoly_eq_eigenvalues] at he
  have hs := congrArg (fun s : Multiset ℂ =>
    (s.map (fun z => z.re * Real.log z.re)).sum) he
  simp only [Multiset.map_map, Function.comp_def] at hs
  change (∑ i, ρ.weights i * Real.log (ρ.weights i)) =
    ∑ i, (ρ.reindex e).weights i * Real.log ((ρ.reindex e).weights i) at hs
  exact congrArg Neg.neg hs.symm

end Entropy

namespace Channels.KrausChannel

variable {ι ο κ μ ν η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [Fintype κ]

/-- The complement and complex conjugation have identical Kraus tensors. -/
theorem complementary_conjugate_map (T : Channels.KrausChannel ι ο κ)
    (X : Matrix ι ι ℂ) :
    T.conjugate.complementary.map X = T.complementary.conjugate.map X := rfl

/-- The complement of a tensor product equals the tensor of the complements. -/
theorem complementary_tensor_map [Fintype μ] [DecidableEq μ] [Fintype ν] [Fintype η]
    (T : Channels.KrausChannel ι ο κ) (S : Channels.KrausChannel μ ν η)
    (X : Matrix (ι × μ) (ι × μ) ℂ) :
    (T.tensor S).complementary.map X = (T.complementary.tensor S.complementary).map X := rfl

/-- Relabel the input and output basis indices of an actual Kraus channel. -/
def reindex [Fintype μ] [DecidableEq μ] [Fintype ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    Channels.KrausChannel μ ν κ where
  kraus := fun k => (T.kraus k).submatrix eo.symm ei.symm
  complete := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    calc
      (∑ k, ((T.kraus k).conjTranspose * T.kraus k).submatrix ei.symm ei.symm) =
          (∑ k, (T.kraus k).conjTranspose * T.kraus k).submatrix ei.symm ei.symm := by
        ext a b
        simp only [Matrix.sum_apply, Matrix.submatrix_apply]
      _ = 1 := by rw [T.complete]; exact Matrix.submatrix_one_equiv ei.symm

/-- The channel's reindexing is the concrete conjugation of its input/output coordinates. -/
theorem reindex_map [Fintype μ] [DecidableEq μ] [Fintype ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν)
    (X : Matrix ι ι ℂ) :
    (T.reindex ei eo).map (Matrix.reindex ei ei X) = Matrix.reindex eo eo (T.map X) := by
  simp only [map, reindex, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext a b
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

/-- Kraus-index equivalences do not change the actual channel map. -/
theorem map_eq_of_kraus_equiv [Fintype η]
    (T : Channels.KrausChannel ι ο κ) (S : Channels.KrausChannel ι ο η)
    (e : κ ≃ η) (h : ∀ l, S.kraus l = T.kraus (e.symm l)) (X : Matrix ι ι ℂ) :
    S.map X = T.map X := by
  simp only [map, h]
  exact e.symm.sum_comp (fun k => T.kraus k * X * (T.kraus k).conjTranspose)

/-- Relabel the environment index; the represented channel is unchanged. -/
def reindexKraus [Fintype η] (T : Channels.KrausChannel ι ο κ) (e : κ ≃ η) :
    Channels.KrausChannel ι ο η where
  kraus := fun l => T.kraus (e.symm l)
  complete := (e.symm.sum_comp (fun k => (T.kraus k).conjTranspose * T.kraus k)).trans T.complete

@[simp] theorem reindexKraus_map [Fintype η] (T : Channels.KrausChannel ι ο κ)
    (e : κ ≃ η) (X : Matrix ι ι ℂ) : (T.reindexKraus e).map X = T.map X :=
  map_eq_of_kraus_equiv T _ e (fun _ => rfl) X

section FourFactorShuffle

variable {i₁ i₂ i₃ i₄ o₁ o₂ o₃ o₄ k₁ k₂ k₃ k₄ : Type*}
variable [Fintype i₁] [DecidableEq i₁] [Fintype i₂] [DecidableEq i₂]
variable [Fintype i₃] [DecidableEq i₃] [Fintype i₄] [DecidableEq i₄]
variable [Fintype o₁] [Fintype o₂] [Fintype o₃] [Fintype o₄]
variable [Fintype k₁] [Fintype k₂] [Fintype k₃] [Fintype k₄]

/-- Regroup four actual channel factors, with the input and output basis
permutations explicit. This applies to arbitrary entangled inputs. -/
theorem tensor_shuffle_map
    (T₁ : Channels.KrausChannel i₁ o₁ k₁) (T₂ : Channels.KrausChannel i₂ o₂ k₂)
    (T₃ : Channels.KrausChannel i₃ o₃ k₃) (T₄ : Channels.KrausChannel i₄ o₄ k₄)
    (X : Matrix ((i₁ × i₂) × (i₃ × i₄)) ((i₁ × i₂) × (i₃ × i₄)) ℂ) :
    ((T₁.tensor T₃).tensor (T₂.tensor T₄)).map
      (Matrix.reindex (Equiv.prodProdProdComm i₁ i₂ i₃ i₄)
        (Equiv.prodProdProdComm i₁ i₂ i₃ i₄) X) =
      Matrix.reindex (Equiv.prodProdProdComm o₁ o₂ o₃ o₄)
        (Equiv.prodProdProdComm o₁ o₂ o₃ o₄)
        (((T₁.tensor T₂).tensor (T₃.tensor T₄)).map X) := by
  rw [← reindex_map ((T₁.tensor T₂).tensor (T₃.tensor T₄))
    (Equiv.prodProdProdComm i₁ i₂ i₃ i₄) (Equiv.prodProdProdComm o₁ o₂ o₃ o₄) X]
  apply map_eq_of_kraus_equiv _ _ (Equiv.prodProdProdComm k₁ k₂ k₃ k₄)
  intro k
  ext a b
  simp [reindex, tensor, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodProdProdComm]
  ring

end FourFactorShuffle

end Channels.KrausChannel
end Nonadditivity
