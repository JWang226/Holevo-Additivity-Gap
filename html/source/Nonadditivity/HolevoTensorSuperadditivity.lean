/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HolevoBits

/-! # Holevo superadditivity for genuine tensor-product channels

Product ensembles give the information sum, using the proved entropy identity
for actual product density matrices. No entropy or Holevo additivity premise is
used. Basis changes and Kraus relabeling preserve the Holevo supremum.
-/

noncomputable section

namespace Nonadditivity

open Entropy Channels Channels.KrausChannel
open scoped BigOperators Kronecker Matrix

namespace StateEnsembles

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

/-- An ensemble with an arbitrary finite label type, represented in the defining
`Fin`-indexed collection without changing its weights or states. -/
def Ensemble.ofFinite {α : Type*} [Fintype α] {outputs : Set (DensityMatrix ι)}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (ρ : α → DensityMatrix ι) (hρ : ∀ a, ρ a ∈ outputs) : Ensemble outputs where
  size := Fintype.card α
  weight := p ∘ (Fintype.equivFin α).symm
  weight_nonneg := fun a => hp ((Fintype.equivFin α).symm a)
  weight_sum := ((Fintype.equivFin α).symm.sum_comp p).trans hsum
  state := ρ ∘ (Fintype.equivFin α).symm
  state_mem := fun a => hρ ((Fintype.equivFin α).symm a)

theorem Ensemble.ofFinite_average {α : Type*} [Fintype α]
    {outputs : Set (DensityMatrix ι)}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (ρ : α → DensityMatrix ι) (hρ : ∀ a, ρ a ∈ outputs) :
    (Ensemble.ofFinite p hp hsum ρ hρ).average = DensityMatrix.mixture p hp hsum ρ := by
  apply DensityMatrix.ext
  exact (Fintype.equivFin α).symm.sum_comp (fun a => (p a : ℂ) • (ρ a).matrix)

theorem Ensemble.ofFinite_information {α : Type*} [Fintype α]
    {outputs : Set (DensityMatrix ι)}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (ρ : α → DensityMatrix ι) (hρ : ∀ a, ρ a ∈ outputs) :
    (Ensemble.ofFinite p hp hsum ρ hρ).information =
      (DensityMatrix.mixture p hp hsum ρ).vonNeumann - ∑ a, p a * (ρ a).vonNeumann := by
  unfold Ensemble.information
  rw [Ensemble.ofFinite_average]
  congr 1
  exact (Fintype.equivFin α).symm.sum_comp (fun a => p a * (ρ a).vonNeumann)

/-- Relabel all output states of an ensemble by the same basis equivalence. -/
def Ensemble.reindex {outputs : Set (DensityMatrix ι)} (e : Ensemble outputs)
    (u : ι ≃ μ) : Ensemble ((fun ρ => ρ.reindex u) '' outputs) where
  size := e.size
  weight := e.weight
  weight_nonneg := e.weight_nonneg
  weight_sum := e.weight_sum
  state := fun a => (e.state a).reindex u
  state_mem := fun a => ⟨e.state a, e.state_mem a, rfl⟩

theorem Ensemble.reindex_average {outputs : Set (DensityMatrix ι)}
    (e : Ensemble outputs) (u : ι ≃ μ) :
    (e.reindex u).average = e.average.reindex u := by
  apply DensityMatrix.ext
  ext a b
  simp only [Ensemble.average, Ensemble.reindex, DensityMatrix.mixture_matrix,
    DensityMatrix.reindex, Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply]

@[simp] theorem Ensemble.reindex_information {outputs : Set (DensityMatrix ι)}
    (e : Ensemble outputs) (u : ι ≃ μ) : (e.reindex u).information = e.information := by
  unfold Ensemble.information
  rw [Ensemble.reindex_average, DensityMatrix.reindex_entropy]
  simp only [Ensemble.reindex, DensityMatrix.reindex_entropy]
  rfl

@[simp] theorem density_reindex_symm (ρ : DensityMatrix ι) (u : ι ≃ μ) :
    (ρ.reindex u).reindex u.symm = ρ := by
  apply DensityMatrix.ext
  ext a b
  simp [DensityMatrix.reindex, Matrix.reindex_apply]

theorem quantity_reindex_le [Nonempty ι] [Nonempty μ]
    {outputs : Set (DensityMatrix ι)} (hne : outputs.Nonempty) (u : ι ≃ μ) :
    quantity outputs ≤ quantity ((fun ρ => ρ.reindex u) '' outputs) := by
  apply csSup_le
  · obtain ⟨ρ, hρ⟩ := hne
    exact ⟨_, singleton ρ hρ, rfl⟩
  · rintro _ ⟨e, rfl⟩
    change e.information ≤ _
    rw [← e.reindex_information u]
    exact le_csSup (information_bddAbove _) ⟨e.reindex u, rfl⟩

/-- The ensemble supremum is exactly invariant under an output basis change. -/
theorem quantity_reindex [Nonempty ι] [Nonempty μ]
    {outputs : Set (DensityMatrix ι)} (hne : outputs.Nonempty) (u : ι ≃ μ) :
    quantity ((fun ρ => ρ.reindex u) '' outputs) = quantity outputs := by
  apply le_antisymm
  · have h := quantity_reindex_le (hne.image ((fun ρ => ρ.reindex u))) u.symm
    have he : ((fun ρ => ρ.reindex u.symm) '' ((fun ρ => ρ.reindex u) '' outputs)) =
        outputs := by
      ext ρ
      constructor
      · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
        simpa using hσ
      · intro hρ
        exact ⟨ρ.reindex u, ⟨ρ, hρ, rfl⟩, density_reindex_symm ρ u⟩
    rwa [he] at h
  · exact quantity_reindex_le hne u

end StateEnsembles

namespace Channels.KrausChannel

variable {ι ο κ μ ν η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
variable [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] [Fintype η]

/-- The independent product of two actual channel-output ensembles. -/
def productEnsemble (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (e : StateEnsembles.Ensemble T.outputs) (f : StateEnsembles.Ensemble S.outputs) :
    StateEnsembles.Ensemble (T.tensor S).outputs :=
  StateEnsembles.Ensemble.ofFinite (fun ab : Fin e.size × Fin f.size =>
    e.weight ab.1 * f.weight ab.2)
    (fun ab => mul_nonneg (e.weight_nonneg _) (f.weight_nonneg _))
    (by simp [Fintype.sum_prod_type, ← Finset.mul_sum,
      e.weight_sum, f.weight_sum])
    (fun ab => (e.state ab.1).tensor (f.state ab.2))
    (fun ab => by
      obtain ⟨ρ, hρ⟩ := e.state_mem ab.1
      obtain ⟨σ, hσ⟩ := f.state_mem ab.2
      exact ⟨ρ.tensor σ, by rw [tensor_output, hρ, hσ]⟩)

theorem productEnsemble_average (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (e : StateEnsembles.Ensemble T.outputs) (f : StateEnsembles.Ensemble S.outputs) :
    (T.productEnsemble S e f).average = e.average.tensor f.average := by
  unfold productEnsemble
  rw [StateEnsembles.Ensemble.ofFinite_average]
  apply DensityMatrix.ext
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [DensityMatrix.mixture_matrix, Fintype.sum_prod_type, Matrix.sum_apply,
    Matrix.smul_apply, DensityMatrix.tensor_matrix, Matrix.kroneckerMap_apply,
    StateEnsembles.Ensemble.average, smul_eq_mul, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The information of the product ensemble is the sum of the two informations. -/
theorem productEnsemble_information (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (e : StateEnsembles.Ensemble T.outputs) (f : StateEnsembles.Ensemble S.outputs) :
    (T.productEnsemble S e f).information = e.information + f.information := by
  have hw : (∑ ab : Fin e.size × Fin f.size,
      (e.weight ab.1 * f.weight ab.2) *
        ((e.state ab.1).vonNeumann + (f.state ab.2).vonNeumann)) =
      (∑ a, e.weight a * (e.state a).vonNeumann) +
        (∑ b, f.weight b * (f.state b).vonNeumann) := by
    simp only [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib]
    congr 1
    · simp_rw [show ∀ a b, (e.weight a * f.weight b) * (e.state a).vonNeumann =
          (e.weight a * (e.state a).vonNeumann) * f.weight b by intros; ring]
      simp [← Finset.mul_sum, f.weight_sum]
    · simp_rw [mul_assoc]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, e.weight_sum, one_mul]
  have ha := productEnsemble_average T S e f
  unfold productEnsemble at ha ⊢
  rw [StateEnsembles.Ensemble.ofFinite_average] at ha
  rw [StateEnsembles.Ensemble.ofFinite_information, ha, DensityMatrix.tensor_entropy]
  simp_rw [DensityMatrix.tensor_entropy]
  rw [hw]
  unfold StateEnsembles.Ensemble.information
  ring

/-- Holevo information is superadditive for arbitrary actual finite channels. -/
theorem holevo_tensor_superadditive [Nonempty ι] [Nonempty ο] [Nonempty μ] [Nonempty ν]
    (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η) :
    T.holevo + S.holevo ≤ (T.tensor S).holevo := by
  have hT : (Set.range fun e : StateEnsembles.Ensemble T.outputs => e.information).Nonempty := by
    obtain ⟨ρ, hρ⟩ := T.outputs_nonempty
    exact ⟨_, StateEnsembles.singleton ρ hρ, rfl⟩
  have hS : (Set.range fun e : StateEnsembles.Ensemble S.outputs => e.information).Nonempty := by
    obtain ⟨ρ, hρ⟩ := S.outputs_nonempty
    exact ⟨_, StateEnsembles.singleton ρ hρ, rfl⟩
  apply (le_sub_iff_add_le).mp
  apply csSup_le hT
  rintro _ ⟨e, rfl⟩
  apply (le_sub_iff_add_le).mpr
  rw [add_comm]
  apply (le_sub_iff_add_le).mp
  apply csSup_le hS
  rintro _ ⟨f, rfl⟩
  apply (le_sub_iff_add_le).mpr
  rw [add_comm, ← productEnsemble_information T S e f]
  exact le_csSup (StateEnsembles.information_bddAbove _) ⟨_, rfl⟩

theorem holevoBits_tensor_superadditive
    [Nonempty ι] [Nonempty ο] [Nonempty μ] [Nonempty ν]
    (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η) :
    T.holevoBits + S.holevoBits ≤ (T.tensor S).holevoBits := by
  simpa only [holevoBits, add_div] using
    div_le_div_of_nonneg_right (T.holevo_tensor_superadditive S) Scalar.log_two_pos.le

/-- Equivalent input/output bases do not change the Holevo quantity. -/
theorem holevo_reindex [Nonempty ι] [Nonempty ο] [Nonempty μ] [Nonempty ν]
    (T : KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    (T.reindex ei eo).holevo = T.holevo := by
  have he : (T.reindex ei eo).outputs = (fun ρ => ρ.reindex eo) '' T.outputs := by
    ext σ
    constructor
    · rintro ⟨ρ, rfl⟩
      refine ⟨T.output (ρ.reindex ei.symm), ⟨_, rfl⟩, ?_⟩
      apply DensityMatrix.ext
      have h := T.reindex_map ei eo (ρ.reindex ei.symm).matrix
      simpa [DensityMatrix.reindex, Matrix.reindex_apply] using h.symm
    · rintro ⟨_, ⟨ρ, rfl⟩, rfl⟩
      refine ⟨ρ.reindex ei, ?_⟩
      apply DensityMatrix.ext
      exact T.reindex_map ei eo ρ.matrix
  unfold holevo
  rw [he, StateEnsembles.quantity_reindex T.outputs_nonempty eo]

theorem holevo_eq_of_map_eq (T : KrausChannel ι ο κ) (S : KrausChannel ι ο η)
    (h : ∀ X, T.map X = S.map X) : T.holevo = S.holevo := by
  have ho : T.output = S.output := by
    funext ρ
    apply DensityMatrix.ext
    exact h ρ.matrix
  unfold holevo outputs
  rw [ho]

@[simp] theorem holevoBits_reindex
    [Nonempty ι] [Nonempty ο] [Nonempty μ] [Nonempty ν]
    (T : KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    (T.reindex ei eo).holevoBits = T.holevoBits := by rw [holevoBits, holevo_reindex]; rfl

theorem holevoBits_eq_of_map_eq (T : KrausChannel ι ο κ) (S : KrausChannel ι ο η)
    (h : ∀ X, T.map X = S.map X) : T.holevoBits = S.holevoBits := by
  rw [holevoBits, T.holevo_eq_of_map_eq S h]; rfl

end Channels.KrausChannel
end Nonadditivity
