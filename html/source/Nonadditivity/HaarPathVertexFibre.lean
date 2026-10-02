/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathClasses

/-! # Exact separation of vertex labelings from a path class

For a fixed incidence pattern, choosing distinct labels for the visited
vertices is independent of the generator colors. This constructs the literal
bijection used to pull the `N^v` factor out of the grouped coefficient sum.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarPathGraph.Path

variable {V : Type*} {d m : ℕ}

theorem ext_data {P Q : Path V d m} (hv : P.vertex = Q.vertex) (hc : P.colors = Q.colors) :
    P = Q := by
  cases P
  cases Q
  cases hv
  cases hc
  rfl

instance [Fintype V] : Fintype (Path V d m) :=
  Fintype.ofInjective (fun P : Path V d m => (P.vertex,P.colors))
    (fun _ _ h => ext_data (congrArg Prod.fst h) (congrArg Prod.snd h))

end Nonadditivity.HaarPathGraph.Path

namespace Nonadditivity.HaarPathVertexFibre

open scoped BigOperators
open HaarPathGraph HaarPathClasses HaarPathProfiles

variable {V : Type*} [Fintype V] {d m : ℕ}

/-- The actual coarse path class before quotienting. -/
def Fibre (P : Path V d m) := {Q : Path V d m // SamePattern P Q}

/-- Its color fibre after fixing the original vertex labeling. -/
def ColorFibre (P : Path V d m) :=
  {Q : Path V d m // Q.vertex = P.vertex ∧ SamePattern P Q}

instance (P : Path V d m) : Fintype (Fibre P) := by
  classical
  unfold Fibre
  infer_instance
instance (P : Path V d m) : Fintype (ColorFibre P) := by
  classical
  unfold ColorFibre
  infer_instance

abbrev VertexLabels (P : Path V d m) := Set.range P.vertex ↪ V

instance visitedFintype (P : Path V d m) : Fintype (Set.range P.vertex) := by
  classical
  infer_instance

instance vertexLabelsFintype (P : Path V d m) : Fintype (VertexLabels P) := by
  classical
  unfold VertexLabels
  infer_instance

/-- Keep the colors and restore the reference vertex names. -/
def normalize (P Q : Path V d m) : Path V d m where
  vertex := P.vertex
  colors := Q.colors
  closed := P.closed
  reduced := Q.reduced

theorem normalize_samePattern {P Q : Path V d m} (h : SamePattern P Q) :
    SamePattern P (normalize P Q) := by
  refine ⟨fun _ _ => Iff.rfl, ?_⟩
  intro a b hab
  exact h.2 a b hab

/-- The unique injection assigning the new name to each visited vertex. -/
def labels {P Q : Path V d m} (h : SamePattern P Q) : VertexLabels P :=
  (rangeEquivOfKernel P.vertex Q.vertex h.1).toEmbedding.trans
    (Function.Embedding.subtype (fun v => v ∈ Set.range Q.vertex))

@[simp] theorem labels_apply {P Q : Path V d m} (h : SamePattern P Q) (i : Fin (m+1)) :
    labels h ⟨P.vertex i,⟨i,rfl⟩⟩ = Q.vertex i :=
  rangeEquivOfKernel_apply P.vertex Q.vertex h.1 i

/-- Reconstruct a path by an injective choice of vertex names and a color fibre. -/
def reconstruct (P : Path V d m) (e : VertexLabels P) (C : ColorFibre P) : Path V d m where
  vertex i := e ⟨P.vertex i,⟨i,rfl⟩⟩
  colors := C.val.colors
  closed := by congr 1; exact Subtype.ext P.closed
  reduced := C.val.reduced

theorem reconstruct_samePattern (P : Path V d m) (e : VertexLabels P) (C : ColorFibre P) :
    SamePattern P (reconstruct P e C) := by
  constructor
  · intro i j
    change P.vertex i = P.vertex j ↔ e ⟨P.vertex i,⟨i,rfl⟩⟩ = e ⟨P.vertex j,⟨j,rfl⟩⟩
    exact ⟨fun h => congrArg e (Subtype.ext h),fun h => congrArg Subtype.val (e.injective h)⟩
  · intro a b hab
    exact C.property.2.2 a b hab

/-- Literal path-class parametrization: vertex injections times fixed-vertex colors. -/
def fibreEquiv (P : Path V d m) : Fibre P ≃ VertexLabels P × ColorFibre P where
  toFun Q := (labels Q.property, ⟨normalize P Q.val,rfl,normalize_samePattern Q.property⟩)
  invFun eC := ⟨reconstruct P eC.1 eC.2,reconstruct_samePattern P eC.1 eC.2⟩
  left_inv Q := by
    apply Subtype.ext
    apply Path.ext_data
    · funext i
      exact labels_apply Q.property i
    · rfl
  right_inv eC := by
    rcases eC with ⟨e,C⟩
    apply Prod.ext
    · apply Function.Embedding.ext
      intro v
      obtain ⟨i,hi⟩ := v.property
      have hv : v = ⟨P.vertex i,⟨i,rfl⟩⟩ := Subtype.ext hi.symm
      rw [hv,labels_apply]
      rfl
    · apply Subtype.ext
      exact Path.ext_data C.property.1.symm rfl

/-- Exact grouped coefficient sum, since coefficients do not depend on vertex names. -/
theorem sum_fibre_colors {R : Type*} [AddCommMonoid R] (P : Path V d m)
    (f : (Fin m → Color d) → R) :
    ∑ Q : Fibre P, f Q.val.colors =
      Fintype.card (VertexLabels P) • ∑ C : ColorFibre P, f C.val.colors := by
  rw [← (fibreEquiv P).symm.sum_comp]
  simp only [Fintype.sum_prod_type, fibreEquiv, reconstruct]
  simp

/-- The vertex factor has the exact dimension exponent, with no factorial loss. -/
theorem card_vertexLabels_le (P : Path V d m) :
    Fintype.card (VertexLabels P) ≤ Fintype.card V ^ Fintype.card (Set.range P.vertex) := by
  classical
  have h := Fintype.card_le_of_injective
    (fun e : VertexLabels P => (e : Set.range P.vertex → V)) Function.Embedding.coe_injective
  simpa only [Fintype.card_fun] using h

end Nonadditivity.HaarPathVertexFibre
