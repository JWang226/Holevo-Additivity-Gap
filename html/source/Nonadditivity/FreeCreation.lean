/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.FreeModel
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Concrete reduced-word projections and free creation operators

These operators act on the actual square-summable functions used by FreeModel.
They are the cancellation decomposition underlying the length-two estimate.
-/

noncomputable section

namespace Nonadditivity.FreeCreation

open Nonadditivity.FreeModel
open scoped BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

section Mask

variable {G : Type*}

/-- An actual coordinate projection on the regular Hilbert space. -/
def maskFunction (P : G → Prop) (f : Hilbert G) : Hilbert G :=
  ⟨fun x => if P x then f x else 0, by
    classical
    apply memℓp_gen
    apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun x => ?_) (f.property.summable (by norm_num))
    split_ifs <;> simp⟩

@[simp] theorem maskFunction_apply (P : G → Prop) (f : Hilbert G) (x : G) :
    maskFunction P f x = if P x then f x else 0 := rfl

theorem maskFunction_norm_le (P : G → Prop) (f : Hilbert G) :
    ‖maskFunction P f‖ ≤ ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg f)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  apply Summable.tsum_le_tsum
    (fun x => ?_) ((maskFunction P f).property.summable (by norm_num))
    (f.property.summable (by norm_num))
  classical
  simp only [maskFunction_apply]
  split_ifs <;> simp

def maskLinear (P : G → Prop) : Hilbert G →ₗ[ℂ] Hilbert G where
  toFun := maskFunction P
  map_add' := by
    intro f h
    ext x
    classical
    simp only [maskFunction_apply, lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c f
    ext x
    classical
    simp only [maskFunction_apply, lp.coeFn_smul, Pi.smul_apply]
    split_ifs <;> simp

/-- The coordinate mask is a genuine bounded linear projection. -/
def mask (P : G → Prop) : Hilbert G →L[ℂ] Hilbert G :=
  (maskLinear P).mkContinuous 1 (by
    intro f
    simpa [maskLinear] using maskFunction_norm_le P f)

@[simp] theorem mask_apply (P : G → Prop) (f : Hilbert G) (x : G) :
    mask P f x = if P x then f x else 0 := rfl

theorem mask_norm_le (P : G → Prop) (f : Hilbert G) : ‖mask P f‖ ≤ ‖f‖ :=
  maskFunction_norm_le P f

theorem mask_adjoint (P : G → Prop) : (mask P).adjoint = mask P := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (∑' x, inner ℂ (f x) (mask P h x)) =
    ∑' x, inner ℂ (mask P f x) (h x)
  apply tsum_congr
  intro x
  classical
  simp only [mask_apply]
  split_ifs <;> simp

theorem mask_add_complement (P : G → Prop) :
    mask P + mask (fun x => ¬ P x) = ContinuousLinearMap.id ℂ (Hilbert G) := by
  ext f x
  classical
  simp only [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    mask_apply, ContinuousLinearMap.id_apply]
  by_cases h : P x <;> simp [h]

end Mask

section Word

variable {α : Type*} [DecidableEq α]

abbrev Letter (α : Type*) := α × Bool

def flip (s : Letter α) : Letter α := (s.1, !s.2)

omit [DecidableEq α] in
@[simp] theorem flip_flip (s : Letter α) : flip (flip s) = s := by
  rcases s with ⟨a,b⟩
  cases b <;> rfl

def letter (s : Letter α) : FreeGroup α :=
  if s.2 then FreeGroup.of s.1 else (FreeGroup.of s.1)⁻¹

omit [DecidableEq α] in
@[simp] theorem letter_flip (s : Letter α) : letter (flip s) = (letter s)⁻¹ := by
  rcases s with ⟨a,b⟩
  cases b <;> simp [letter, flip]

@[simp] theorem letter_toWord (s : Letter α) : (letter s).toWord = [s] := by
  rcases s with ⟨a,b⟩
  cases b <;> simp [letter, FreeGroup.invRev]

/-- Words whose reduced first letter is the specified letter. -/
def Cone (s : Letter α) (x : FreeGroup α) : Prop := ∃ t, x.toWord = s :: t

theorem cone_disjoint {s t : Letter α} (hne : s ≠ t) (x : FreeGroup α) :
    ¬ (Cone s x ∧ Cone t x) := by
  rintro ⟨⟨u,hu⟩, ⟨v,hv⟩⟩
  exact hne (List.cons.inj (hu.symm.trans hv)).1

theorem cone_shift_iff (s : Letter α) (x : FreeGroup α) :
    Cone s (letter s * x) ↔ ¬ Cone (flip s) x := by
  have hword : (letter s * x).toWord = FreeGroup.reduce (s :: x.toWord) := by
    rw [FreeGroup.toWord_mul, letter_toWord]
    rfl
  cases hx : x.toWord with
  | nil =>
    simp [Cone, hword, hx, FreeGroup.reduce]
  | cons t tail =>
    have hred : FreeGroup.reduce (t :: tail) = t :: tail := by
      rw [← hx]
      exact FreeGroup.reduce_toWord x
    unfold Cone
    rw [hword, FreeGroup.reduce.cons, hx, hred]
    by_cases he : s.1 = t.1 ∧ s.2 = !t.2
    · have ht : t = flip s := by
        rcases s with ⟨a,b⟩
        rcases t with ⟨c,d⟩
        cases b <;> cases d <;> simp_all [flip]
      simp only [he]
      have hn : ¬ ∃ u, tail = s :: u := by
        rintro ⟨u, rfl⟩
        have hr := FreeGroup.isReduced_toWord (x := x)
        rw [hx, FreeGroup.isReduced_cons_cons] at hr
        have hb := hr.1 (by simp [ht, flip])
        have hb' : (flip s).2 = s.2 := by simpa [ht] using hb
        rcases s with ⟨a,b⟩
        cases b <;> simp [flip] at hb'
      simp [ht, hn]
    · have ht : t ≠ flip s := by
        intro ht
        apply he
        rw [ht]
        rcases s with ⟨a,b⟩
        cases b <;> simp [flip]
      simp [he, ht]

end Word

section Operators

variable {α : Type*} [DecidableEq α]

theorem leftRegular_adjoint {G : Type*} [Group G] (g : G) :
    (leftRegular g).adjoint = leftRegular g⁻¹ := by
  change ContinuousLinearMap.adjoint
    ((reindexIsometry (Equiv.mulLeft g⁻¹)) : Hilbert G →L[ℂ] Hilbert G) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  change f ((Equiv.mulLeft g⁻¹).symm x) = f ((g⁻¹)⁻¹ * x)
  simp

theorem leftRegular_inner {G : Type*} [Group G] (g : G) (f h : Hilbert G) :
    inner ℂ (leftRegular g f) (leftRegular g h) = inner ℂ f h :=
  (reindexIsometry (Equiv.mulLeft g⁻¹)).inner_map_map f h

/-- A letter creation shift, retaining only words where the new letter does
not cancel. Its range consists of words with that reduced first letter. -/
def creation (s : Letter α) : Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  (mask (Cone s)).comp (leftRegular (letter s))

@[simp] theorem creation_apply (s : Letter α) (f : Hilbert (FreeGroup α))
    (x : FreeGroup α) :
    creation s f x = if Cone s x then f ((letter s)⁻¹ * x) else 0 := rfl

/-- Creation is equally the full shift restricted to its noncancelling input cone. -/
theorem creation_domain (s : Letter α) :
    creation s = (leftRegular (letter s)).comp (mask (fun x => ¬ Cone (flip s) x)) := by
  ext f x
  have hc : Cone s x ↔ ¬ Cone (flip s) ((letter s)⁻¹ * x) := by
    simpa [mul_assoc] using cone_shift_iff s ((letter s)⁻¹ * x)
  simp [creation_apply, ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply, hc]

theorem creation_adjoint (s : Letter α) :
    (creation s).adjoint = (leftRegular (letter s)⁻¹).comp (mask (Cone s)) := by
  rw [creation, ContinuousLinearMap.adjoint_comp, mask_adjoint, leftRegular_adjoint]

/-- The actual regular generator is the sum of creation and inverse annihilation. -/
theorem leftRegular_letter_decomposition (s : Letter α) :
    leftRegular (letter s) = creation s + (creation (flip s)).adjoint := by
  rw [creation_domain, creation_adjoint, letter_flip, inv_inv]
  ext f x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    lp.coeFn_add, Pi.add_apply, leftRegular_apply, mask_apply]
  by_cases hx : Cone (flip s) ((letter s)⁻¹ * x) <;> simp [hx]

theorem creation_norm_le (s : Letter α) (f : Hilbert (FreeGroup α)) :
    ‖creation s f‖ ≤ ‖f‖ :=
  (mask_norm_le (Cone s) (leftRegular (letter s) f)).trans_eq
    (leftRegular_preserves_norm (letter s) f)

/-- Different first-letter creation ranges are orthogonal. -/
theorem creation_inner_zero {s t : Letter α} (hne : s ≠ t)
    (f h : Hilbert (FreeGroup α)) : inner ℂ (creation s f) (creation t h) = 0 := by
  change (∑' x, inner ℂ (creation s f x) (creation t h x)) = 0
  have hz : ∀ x, inner ℂ (creation s f x) (creation t h x) = 0 := by
    intro x
    by_cases hs : Cone s x
    · have ht : ¬ Cone t x := fun ht => cone_disjoint hne x ⟨hs,ht⟩
      simp [creation_apply, ht]
    · simp [creation_apply, hs]
  simp_rw [hz]
  exact tsum_zero

/-- The middle cancellation term vanishes for different letters. -/
theorem creation_adjoint_comp_zero {s t : Letter α} (hne : s ≠ t) :
    (creation s).adjoint.comp (creation t) = 0 := by
  rw [creation_adjoint]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply,
    creation_apply, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hs : Cone s (letter s * x)
  · have ht : ¬ Cone t (letter s * x) := fun ht => cone_disjoint hne _ ⟨hs,ht⟩
    simp [hs, ht]
  · simp [hs]

/-- On another first-letter range, creation has no cancellation and is a full isometry. -/
theorem creation_comp_creation_eq_shift {s t : Letter α} (hne : flip s ≠ t) :
    (creation s).comp (creation t) = (leftRegular (letter s)).comp (creation t) := by
  rw [creation_domain]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply, creation_apply]
  by_cases hs : Cone (flip s) ((letter s)⁻¹ * x)
  · have ht : ¬ Cone t ((letter s)⁻¹ * x) := fun ht => cone_disjoint hne _ ⟨hs,ht⟩
    simp [hs, ht]
  · simp [hs]

/-- A reduced length-two shift has exactly three cancellation components. -/
theorem length_two_decomposition {s t : Letter α} (hne : flip s ≠ t) :
    leftRegular (letter s * letter t) =
      (creation s).comp (creation t) +
      (creation s).comp (creation (flip t)).adjoint +
      (creation (flip s)).adjoint.comp (creation (flip t)).adjoint := by
  rw [leftRegular_mul, leftRegular_letter_decomposition s,
    leftRegular_letter_decomposition t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add, creation_adjoint_comp_zero hne, zero_add]

end Operators

end Nonadditivity.FreeCreation
