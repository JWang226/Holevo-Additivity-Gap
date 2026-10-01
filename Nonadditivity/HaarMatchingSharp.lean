/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarMatchingCount
import Nonadditivity.HaarMatchingFibers

/-! # The high-multiplicity matching bound

Fixing the disagreement images leaves a literal bijection between fibers of
identical entries. Fibers of size zero or one carry no factorial cost; all
other costs are charged to half the total multiplicity of entries occurring
at least four times.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarMatchingSharp
open HaarMatchingCount HaarMatchingFibers HaarPathMultiplicity
open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E] {p : ℕ}

abbrev Remaining (S : Finset (Fin p)) := {a : Fin p // a ∉ S}

def restriction (x y : Fin p → E) (S : Finset (Fin p))
    (σ : AgreementMatching x y S) : S → Fin p := fun a => σ.val a.val

abbrev RestrictionFiber (x y : Fin p → E) (S : Finset (Fin p)) (t : S → Fin p) :=
  {σ : AgreementMatching x y S // restriction x y S σ=t}

/-- Fixed images on the exceptional positions leave an actual bijection
between the complementary occurrence sets, preserving their entry labels. -/
def fiberToLabel (x y : Fin p → E) (S : Finset (Fin p)) (t : S → Fin p)
    (σ₀ σ : RestrictionFiber x y S t) :
    LabelEquiv (fun a : Remaining S => x a.val)
      (fun b : Remaining (S.image σ₀.val.val) => y b.val) := by
  classical
  have hs (a : Fin p) (ha : a ∈ S) : σ.val.val a=σ₀.val.val a :=
    congrFun (σ.property.trans σ₀.property.symm) ⟨a,ha⟩
  let e : Remaining S ≃ Remaining (S.image σ₀.val.val) :=
    σ.val.val.subtypeEquiv (fun a => by
      constructor
      · intro ha hm
        obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hm
        have hba : b=a := σ.val.val.injective ((hs b hb).trans he)
        exact ha (hba ▸ hb)
      · intro ha hm
        exact ha (Finset.mem_image.mpr ⟨a,hm,(hs a hm).symm⟩))
  exact ⟨e,fun a => (σ.val.property a.val a.property).symm⟩

omit [Fintype E] [DecidableEq E] in
theorem fiberToLabel_injective (x y : Fin p → E) (S : Finset (Fin p)) (t : S → Fin p)
    (σ₀ : RestrictionFiber x y S t) : Function.Injective (fiberToLabel x y S t σ₀) := by
  classical
  intro σ τ h
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro a
  by_cases ha : a ∈ S
  · exact congrFun (σ.property.trans τ.property.symm) ⟨a,ha⟩
  · exact congrArg (fun f : LabelEquiv (fun a : Remaining S => x a.val)
      (fun b : Remaining (S.image σ₀.val.val) => y b.val) => (f.val ⟨a,ha⟩).val) h

/-- Actual residual multiplicity of one entry value. -/
def residualCount (x : Fin p → E) (S : Finset (Fin p)) (e : E) : ℕ :=
  Fintype.card {a : Remaining S // x a.val=e}

omit [Fintype E] in
theorem residualCount_le (x : Fin p → E) (S : Finset (Fin p)) (e : E) :
    residualCount x S e ≤ p := by
  classical
  apply (Fintype.card_subtype_le _).trans
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun a : Fin p => a ∉ S)

omit [Fintype E] in
/-- Every remaining positive occurrence has a distinct negative partner;
the combined multiplicity is therefore at least twice the residual size. -/
theorem twice_residualCount_le (x y : Fin p → E) (S : Finset (Fin p))
    (σ : AgreementMatching x y S) (e : E) :
    2*residualCount x S e ≤ (List.ofFn x ++ List.ofFn y).count e := by
  classical
  let A := {a : Remaining S // x a.val=e}
  let f : A → {a : Fin p // x a=e} := fun a => ⟨a.val.val,a.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {a : Fin p // x a=e} => z.val) h
  let g : A → {b : Fin p // y b=e} := fun a =>
    ⟨σ.val a.val.val,(σ.property a.val.val a.val.property).symm.trans a.property⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact σ.val.injective (congrArg Subtype.val h)
  have hpos := Fintype.card_le_of_injective f hf
  have hneg := Fintype.card_le_of_injective g hg
  have hx : Fintype.card {a : Fin p // x a=e}=(List.ofFn x).count e := by
    rw [count_ofFn_eq_card,Fintype.card_subtype]
  have hy : Fintype.card {a : Fin p // y a=e}=(List.ofFn y).count e := by
    rw [count_ofFn_eq_card,Fintype.card_subtype]
  rw [hx] at hpos
  rw [hy] at hneg
  change residualCount x S e ≤ _ at hpos hneg
  rw [List.count_append]
  omega

lemma sum_high_multiplicity (L : List E) :
    (∑ e : E, if 4 ≤ L.count e then L.count e else 0)=highMultiplicityOccurrences L := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  have hz : L.count e=0 := List.count_eq_zero.mpr
    (fun h => he (List.mem_toFinset.mpr h))
  simp [hz]

/-- After the exceptional images have been fixed, only repeated pairs carry
any choice: their total cost is at most half the high multiplicity count. -/
theorem card_restrictionFiber_le (hp : 0 < p) (x y : Fin p → E)
    (S : Finset (Fin p)) (t : S → Fin p) :
    Fintype.card (RestrictionFiber x y S t) ≤
      p^(highMultiplicityOccurrences (List.ofFn x ++ List.ofFn y)/2) := by
  classical
  by_cases h : Nonempty (RestrictionFiber x y S t)
  · obtain ⟨σ₀⟩ := h
    calc
      _ ≤ Fintype.card (LabelEquiv (fun a : Remaining S => x a.val)
          (fun b : Remaining (S.image σ₀.val.val) => y b.val)) :=
        Fintype.card_le_of_injective (fiberToLabel x y S t σ₀)
          (fiberToLabel_injective x y S t σ₀)
      _ ≤ ∏ e : E, (residualCount x S e).factorial := by
        simpa only [residualCount, ← Nat.card_eq_fintype_card] using
          (card_labelEquiv_le (fun a : Remaining S => x a.val)
            (fun b : Remaining (S.image σ₀.val.val) => y b.val))
      _ ≤ _ := by
        have hnum := prod_factorial_le_pow_half_high p hp (residualCount x S)
          (fun e => (List.ofFn x ++ List.ofFn y).count e)
          (residualCount_le x S) (twice_residualCount_le x y S σ₀.val)
        simpa only [sum_high_multiplicity] using hnum
  · letI : IsEmpty (RestrictionFiber x y S t) := not_nonempty_iff.mp h
    simp

/-- The sharp matching estimate before selecting any row/column data. -/
theorem card_agreementMatching_le_sharp (hp : 0 < p) (x y : Fin p → E)
    (S : Finset (Fin p)) :
    Fintype.card (AgreementMatching x y S) ≤
      p^(S.card+highMultiplicityOccurrences (List.ofFn x ++ List.ofFn y)/2) := by
  classical
  calc
    _ = ∑ t : S → Fin p, Fintype.card (RestrictionFiber x y S t) := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv (restriction x y S))).symm
    _ ≤ ∑ _t : S → Fin p,
        p^(highMultiplicityOccurrences (List.ofFn x ++ List.ofFn y)/2) :=
      Finset.sum_le_sum (fun t _ => card_restrictionFiber_le hp x y S t)
    _ = p^S.card * p^(highMultiplicityOccurrences (List.ofFn x ++ List.ofFn y)/2) := by
      simp
    _ = _ := (pow_add _ _ _).symm

/-- The actual fixed-relative Haar matching bound, with the fourth-and-higher
multiplicity statistic from the literal entry list. -/
theorem card_relativeMatching_le_sharp {R C : Type*}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (hp : 0 < p) (i k : Fin p → R) (j l : Fin p → C) (α : Equiv.Perm (Fin p)) :
    Fintype.card (RelativeMatching i k j l α) ≤ p^(α.support.card+
      highMultiplicityOccurrences (List.ofFn (fun a => (i a,j a)) ++
        List.ofFn (fun a => (k a,l a)))/2) := by
  classical
  let f : RelativeMatching i k j l α →
      AgreementMatching (fun a => (i a,j a)) (fun a => (k a,l a)) α.support := fun σ =>
    ⟨σ.val,by
      intro a ha
      have hα : α a=a := by simpa only [Equiv.Perm.mem_support,not_not] using ha
      apply Prod.ext
      · exact congrFun σ.property.1 a
      · simpa only [Function.comp_apply,Equiv.Perm.mul_apply,hα] using congrFun σ.property.2 a⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    exact congrArg (fun z : AgreementMatching (fun a => (i a,j a))
      (fun a => (k a,l a)) α.support => z.val) h
  exact (Fintype.card_le_of_injective f hf).trans (card_agreementMatching_le_sharp hp _ _ α.support)

end Nonadditivity.HaarMatchingSharp
