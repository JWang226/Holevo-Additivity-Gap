/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathVertexFibre
import Nonadditivity.HaarPathRefined

/-! # Exact vertex-label factor for the genuine refined path class -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarRefinedVertexFibre

open scoped BigOperators
open HaarPathGraph HaarPathClasses HaarPathProfiles
open HaarPathVertexFibre (VertexLabels)

variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

def Fibre (P : Path V d m) := {Q : Path V d m // RefinedPattern P Q}
def ColorFibre (P : Path V d m) :=
  {Q : Path V d m // Q.vertex=P.vertex ∧ RefinedPattern P Q}

instance (P : Path V d m) : Fintype (Fibre P) := by
  classical
  unfold Fibre
  infer_instance
instance (P : Path V d m) : Fintype (ColorFibre P) := by
  classical
  unfold ColorFibre
  infer_instance

/-- Changing only vertex labels preserves every actual core-chain profile. -/
theorem normalize_refined {P Q : Path V d m} (h : RefinedPattern P Q) :
    RefinedPattern P (HaarPathVertexFibre.normalize P Q) := by
  have hcoarse := h.samePattern.symm.trans (HaarPathVertexFibre.normalize_samePattern h.samePattern)
  exact h.trans (RefinedPattern.of_colors_eq hcoarse rfl)

def coarseColor {P : Path V d m} (C : ColorFibre P) : HaarPathVertexFibre.ColorFibre P :=
  ⟨C.val,C.property.1,C.property.2.samePattern⟩

theorem reconstruct_refined (P : Path V d m) (e : VertexLabels P) (C : ColorFibre P) :
    RefinedPattern P (HaarPathVertexFibre.reconstruct P e (coarseColor C)) := by
  have hcoarse := C.property.2.samePattern.symm.trans
    (HaarPathVertexFibre.reconstruct_samePattern P e (coarseColor C))
  exact C.property.2.trans (RefinedPattern.of_colors_eq hcoarse rfl)

/-- Genuine refined paths are exactly independent vertex injections and
fixed-vertex refined colorings. -/
def fibreEquiv (P : Path V d m) : Fibre P ≃ VertexLabels P × ColorFibre P where
  toFun Q := (HaarPathVertexFibre.labels Q.property.samePattern,
    ⟨HaarPathVertexFibre.normalize P Q.val,rfl,normalize_refined Q.property⟩)
  invFun eC := ⟨HaarPathVertexFibre.reconstruct P eC.1 (coarseColor eC.2),
    reconstruct_refined P eC.1 eC.2⟩
  left_inv Q := by
    apply Subtype.ext
    apply Path.ext_data
    · funext i
      exact HaarPathVertexFibre.labels_apply Q.property.samePattern i
    · rfl
  right_inv eC := by
    rcases eC with ⟨e,C⟩
    apply Prod.ext
    · apply Function.Embedding.ext
      intro v
      obtain ⟨i,hi⟩ := v.property
      have hv : v = ⟨P.vertex i,⟨i,rfl⟩⟩ := Subtype.ext hi.symm
      rw [hv,HaarPathVertexFibre.labels_apply]
      rfl
    · apply Subtype.ext
      exact Path.ext_data C.property.1.symm rfl

/-- Exact vertex factor in the grouped operator coefficient sum. -/
theorem sum_fibre_colors {R : Type*} [AddCommMonoid R] (P : Path V d m)
    (f : (Fin m → Color d) → R) :
    ∑ Q : Fibre P, f Q.val.colors =
      Fintype.card (VertexLabels P) • ∑ C : ColorFibre P, f C.val.colors := by
  rw [← (fibreEquiv P).symm.sum_comp]
  simp only [Fintype.sum_prod_type, fibreEquiv, HaarPathVertexFibre.reconstruct, coarseColor]
  simp

/-- The visited-vertex range is precisely the graph's original vertex set. -/
theorem range_vertex_eq (P : Path V d m) (hm : 0 < m) :
    Set.range P.vertex = (P.vertices : Set V) := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    by_cases hj : j.val < m
    · have he : j = (⟨j.val,hj⟩ : Fin m).castSucc := Fin.ext rfl
      rw [he]
      exact P.start_mem _
    · have he : j = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [he,P.closed]
      exact P.start_mem ⟨0,hm⟩
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i.castSucc,rfl⟩

theorem card_vertexLabels_le (P : Path V d m) (hm : 0 < m) :
    Fintype.card (VertexLabels P) ≤ Fintype.card V ^ P.vertices.card := by
  have hc : Fintype.card (Set.range P.vertex) = P.vertices.card := by
    exact Fintype.card_of_finset' P.vertices (fun v => by
      rw [range_vertex_eq P hm]
      rfl)
  simpa only [hc] using HaarPathVertexFibre.card_vertexLabels_le P

end Nonadditivity.HaarRefinedVertexFibre
