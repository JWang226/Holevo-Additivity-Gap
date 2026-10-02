/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathCounting
import Nonadditivity.HaarPathVertexFibre
import Nonadditivity.HaarPathRefined
import Nonadditivity.HaarPathProfileReverse

/-! # Counting the genuine refined path quotient

Within each actual coarse class, one profile per unoriented suppressed chain
is sufficient: the reverse profile is forced. Transport to a fixed class
representative gives a concrete injective profile assignment.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {d m : ℕ}

instance refinedClassFintype : Fintype (RefinedClass V d m) := Quotient.fintype _

def refinedToCoarse : RefinedClass V d m → PathClass V d m :=
  Quotient.lift (Quotient.mk _) (fun _ _ h => Quotient.sound h.samePattern)

@[simp] theorem refinedToCoarse_mk (P : Path V d m) :
    refinedToCoarse (Quotient.mk _ P)=Quotient.mk _ P := rfl

/-- Actual refined classes lying over a given coarse class. -/
def RefinedOver (C : PathClass V d m) := {D : RefinedClass V d m // refinedToCoarse D=C}

instance (C : PathClass V d m) : Fintype (RefinedOver C) := by
  unfold RefinedOver
  infer_instance

def orientation (P : Path V d m) (s : P.unorientedChains) : P.CoreChain :=
  Classical.choose (show s.val.Nonempty from by
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp s.property
    rw [←he]
    simp)

omit [Fintype V] in
theorem orientation_mem (P : Path V d m) (s : P.unorientedChains) :
    orientation P s ∈ s.val := Classical.choose_spec _

def chainOrbit (P : Path V d m) (c : P.CoreChain) : P.unorientedChains :=
  ⟨{c,P.coreChainReverse c},Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩⟩

theorem orientation_cases (P : Path V d m) (c : P.CoreChain) :
    orientation P (chainOrbit P c)=c ∨
      orientation P (chainOrbit P c)=P.coreChainReverse c := by
  simpa only [chainOrbit,Finset.mem_insert,Finset.mem_singleton] using
    orientation_mem P (chainOrbit P c)

def overRepresentative {C : PathClass V d m} (D : RefinedOver C) : Path V d m :=
  Quotient.out D.val

theorem over_samePattern {C : PathClass V d m} (D : RefinedOver C) :
    SamePattern (Quotient.out C) (overRepresentative D) := by
  apply @Quotient.exact _ (pathSetoid (V := V) (d := d) (m := m))
  change Quotient.mk _ (Quotient.out C)=refinedToCoarse (Quotient.mk _ (overRepresentative D))
  rw [Quotient.out_eq]
  have hd : (Quotient.mk _ (overRepresentative D) : RefinedClass V d m)=D.val :=
    Quotient.out_eq D.val
  rw [hd,D.property]

/-- The actual profile labels on chosen orientations of the representative's
suppressed chains. -/
def overProfileAssignment {C : PathClass V d m} (D : RefinedOver C) :
    (Quotient.out C).unorientedChains → BoundedProfile (Color d) m :=
  fun s => (overRepresentative D).coreChainProfile
    ((over_samePattern D).coreChainEquiv (orientation (Quotient.out C) s))

/-- Equality on one orientation forces equality on the reverse orientation. -/
theorem overProfiles_all {C : PathClass V d m} (D E : RefinedOver C)
    (he : overProfileAssignment D=overProfileAssignment E)
    (c : (Quotient.out C).CoreChain) :
    (overRepresentative D).coreChainProfile ((over_samePattern D).coreChainEquiv c)=
      (overRepresentative E).coreChainProfile ((over_samePattern E).coreChainEquiv c) := by
  have h := congrFun he (chainOrbit (Quotient.out C) c)
  change (overRepresentative D).coreChainProfile
      ((over_samePattern D).coreChainEquiv (orientation _ _)) =
    (overRepresentative E).coreChainProfile
      ((over_samePattern E).coreChainEquiv (orientation _ _)) at h
  rcases orientation_cases (Quotient.out C) c with hc | hc
  · simpa only [hc] using h
  · rw [hc] at h
    simp only [SamePattern.coreChainEquiv_apply,SamePattern.coreChainMap_reverse] at h
    have hr := HaarPathGraph.Path.coreChainProfile_reverse_eq_of_profile_eq
      (overRepresentative D) (overRepresentative E) _ _ h
    simpa only [Path.coreChainReverse_involutive] using hr

/-- The profile assignment is injective on the genuine refined quotient. -/
theorem overProfileAssignment_injective (C : PathClass V d m) :
    Function.Injective (@overProfileAssignment V _ _ d m C) := by
  intro D E he
  let hD := over_samePattern D
  let hE := over_samePattern E
  let hDE := hD.symm.trans hE
  have hr : RefinedPattern (overRepresentative D) (overRepresentative E) := by
    refine ⟨hDE,fun c => ?_⟩
    let a := hD.coreChainEquiv.symm c
    have ha : hD.coreChainEquiv a=c := hD.coreChainEquiv.apply_symm_apply c
    have hv := overProfiles_all D E he a
    have ht : hDE.coreChainEquiv (hD.coreChainEquiv a)=hE.coreChainEquiv a := by
      simpa only [SamePattern.coreChainEquiv_apply] using
        (hD.coreChainMap_trans hDE a).symm
    rw [ha] at hv ht
    exact hv.trans (congrArg (overRepresentative E).coreChainProfile ht.symm)
  apply Subtype.ext
  calc
    D.val = Quotient.mk _ (overRepresentative D) := (Quotient.out_eq D.val).symm
    _ = Quotient.mk _ (overRepresentative E) := Quotient.sound hr
    _ = E.val := Quotient.out_eq E.val

/-- Exact refined-fibre count with the original profile exponent. -/
theorem card_refinedOver_le (C : PathClass V d m) (hm : 0 < m) (hd : 0 < d) :
    Fintype.card (RefinedOver C) ≤
      (2*d*m^d)^(3*(Quotient.out C).defectTwice+4) := by
  calc
    _ ≤ Fintype.card ((Quotient.out C).unorientedChains → BoundedProfile (Color d) m) :=
      Fintype.card_le_of_injective _ (overProfileAssignment_injective C)
    _ ≤ _ := (Quotient.out C).card_chainProfileAssignments_le hm hd

/-- Actual refined classes at a fixed integer defect. -/
abbrev RefinedDefectClass (V : Type*) [Fintype V] [DecidableEq V]
    (m δ : ℕ) (hm : 0 < m) :=
  {D : RefinedClass V 2 m // classDefectTwice hm (refinedToCoarse D)=δ}

def refinedDefectEquiv (hm : 0 < m) (δ : ℕ) :
    RefinedDefectClass V m δ hm ≃
      Σ C : DefectClass V m δ hm, RefinedOver C.val where
  toFun D := ⟨⟨refinedToCoarse D.val,D.property⟩,⟨D.val,rfl⟩⟩
  invFun CD := ⟨CD.2.val,by rw [CD.2.property]; exact CD.1.property⟩
  left_inv D := rfl
  right_inv CD := by
    obtain ⟨⟨C,hC⟩,D,hD⟩ := CD
    dsimp at hD
    subst C
    rfl

/-- Corrected coarse-class and exact profile counts combined on the genuine
refined quotient, with no class-cardinality hypothesis. -/
theorem card_refinedDefectClass_le (hm : 0 < m) (δ : ℕ) :
    Fintype.card (RefinedDefectClass V m δ hm) ≤
      128^(δ+2)*m^(3*δ+6)*(4*m^2)^(3*δ+4) := by
  rw [Fintype.card_congr (refinedDefectEquiv hm δ),Fintype.card_sigma]
  have hC (C : DefectClass V m δ hm) :
      Fintype.card (RefinedOver C.val) ≤ (4*m^2)^(3*δ+4) := by
    have h := card_refinedOver_le C.val hm (by decide : 0 < 2)
    have hd := classRepresentative_defect hm C
    change (Quotient.out C.val).defectTwice=δ at hd
    simpa only [hd,show 2*2=4 from rfl] using h
  calc
    _ ≤ ∑ C : DefectClass V m δ hm, (4*m^2)^(3*δ+4) :=
      Finset.sum_le_sum (fun C _ => hC C)
    _ = Fintype.card (DefectClass V m δ hm)*(4*m^2)^(3*δ+4) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_defectClass_le hm δ)

/-- Every concrete subfamily of refined classes at a fixed defect inherits
our genuine quotient bound. -/
theorem card_refined_subfamily_le (hm : 0 < m) (δ : ℕ)
    (s : Finset (RefinedClass V 2 m))
    (hs : ∀ C ∈ s, classDefectTwice hm (refinedToCoarse C)=δ) :
    s.card ≤ 128^(δ+2)*m^(3*δ+6)*(4*m^2)^(3*δ+4) := by
  let f : s → RefinedDefectClass V m δ hm := fun C => ⟨C.val,hs C.val C.property⟩
  have hf : Function.Injective f := by
    intro C D h
    have he := congrArg (fun x : RefinedDefectClass V m δ hm => x.val) h
    exact Subtype.ext he
  have h := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at h
  exact h.trans (card_refinedDefectClass_le hm δ)

end Nonadditivity.HaarPathClasses
