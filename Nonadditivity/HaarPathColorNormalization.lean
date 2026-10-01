/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathFreshRuns

/-! # Local color normalization of actual path incidence patterns

At each newly discovered vertex, the incoming color and the immediately
following outgoing color are distinct. An actual local permutation sends
them to two fixed labels. Thus every internal fresh-run incidence is forced
in the normalized pattern, while the full color alphabet remains `2d`.
The normalized labels are incidence data, not a new globally colored path.
-/

noncomputable section
namespace Nonadditivity.HaarPathClasses
open HaarPathGraph HaarPathProfiles

/-- A permutation of a finite alphabet may normalize any ordered distinct
pair to any other ordered distinct pair. -/
theorem exists_perm_map_pair {E : Type*} [Fintype E]
    (a b c d : E) (hab : a≠b) (hcd : c≠d) :
    ∃ σ : Equiv.Perm E, σ a=c ∧ σ b=d := by
  obtain ⟨σ,hσ⟩ := exists_perm_of_kernel_eq
    (fun t : Bool => if t then b else a) (fun t : Bool => if t then d else c)
    (by intro s t; cases s <;> cases t <;> simp [hab,hcd,Ne.symm hab,Ne.symm hcd])
  exact ⟨σ,by simpa using hσ false,by simpa using hσ true⟩

variable {V : Type*} [DecidableEq V] {d m : ℕ}

/-- One actual permutation per vertex simultaneously normalizes every first
arrival and its next departure. There is exactly one first arrival at each
non-root visited vertex. -/
theorem exists_local_color_normalization (P : Path V d m) (hm : 0<m)
    (c₀ c₁ : Color d) (hc : c₀≠c₁) :
    ∃ β : V → Equiv.Perm (Color d),
      β (P.vertex 0) (P.colors ⟨0,hm⟩)=c₀ ∧
      (∀ i : Fin m, P.FirstVisit i →
        β (P.vertex i.succ) (flipColor (P.colors i))=c₀) ∧
      (∀ i j : Fin m, P.FirstVisit i → i.val+1=j.val →
        β (P.vertex i.succ) (P.colors j)=c₁) := by
  classical
  have hlocal (v : V) : ∃ σ : Equiv.Perm (Color d),
      (v=P.vertex 0 → σ (P.colors ⟨0,hm⟩)=c₀) ∧
      (∀ i : Fin m, P.FirstVisit i → P.vertex i.succ=v →
        σ (flipColor (P.colors i))=c₀) ∧
      (∀ i j : Fin m, P.FirstVisit i → i.val+1=j.val → P.vertex i.succ=v →
        σ (P.colors j)=c₁) := by
    by_cases hv : v=P.vertex 0
    · refine ⟨Equiv.swap (P.colors ⟨0,hm⟩) c₀,?_,?_,?_⟩
      · intro _; simp
      · intro i hi hiv
        exact (P.firstVisit_terminal_ne_root hi (hiv.trans hv)).elim
      · intro i j hi hij hiv
        exact (P.firstVisit_terminal_ne_root hi (hiv.trans hv)).elim
    · by_cases hex : ∃ i : Fin m, P.FirstVisit i ∧ P.vertex i.succ=v
      · obtain ⟨i,hi,hiv⟩ := hex
        let j : Fin m := ⟨i.val+1,P.firstVisit_not_last hi⟩
        have hij : i.val+1=j.val := rfl
        have hdist : flipColor (P.colors i)≠P.colors j := Ne.symm (P.reduced i j hij)
        obtain ⟨σ,hσ₀,hσ₁⟩ := exists_perm_map_pair
          (flipColor (P.colors i)) (P.colors j) c₀ c₁ hdist hc
        refine ⟨σ,fun h => (hv h).elim,?_,?_⟩
        · intro k hk hkv
          have he : k=i := P.firstVisit_terminal_injective
            ((P.mem_firstTimes k).mpr hk) ((P.mem_firstTimes i).mpr hi) (hkv.trans hiv.symm)
          subst k
          exact hσ₀
        · intro k l hk hkl hkv
          have he : k=i := P.firstVisit_terminal_injective
            ((P.mem_firstTimes k).mpr hk) ((P.mem_firstTimes i).mpr hi) (hkv.trans hiv.symm)
          subst k
          have he : l=j := Fin.ext (hkl.symm.trans hij)
          subst l
          exact hσ₁
      · refine ⟨Equiv.refl _,fun h => (hv h).elim,?_,?_⟩
        · intro i hi hiv
          exact (hex ⟨i,hi,hiv⟩).elim
        · intro i j hi hij hiv
          exact (hex ⟨i,hi,hiv⟩).elim
  choose β hβ using hlocal
  exact ⟨β,(hβ _).1 rfl,fun i hi => (hβ _).2.1 i hi rfl,
    fun i j hi hij => (hβ _).2.2 i j hi hij rfl⟩

/-- Locally normalized incidence colors, retaining both orientations. -/
def normalizedIncidenceColor (P : Path V d m) (β : V → Equiv.Perm (Color d))
    (a : Incidence m) : Color d := β (incidenceVertex P a) (incidenceColor P a)

omit [DecidableEq V] in
/-- Normalization preserves the actual local equality pattern exactly. -/
theorem normalizedIncidenceColor_eq_iff (P : Path V d m)
    (β : V → Equiv.Perm (Color d)) (a b : Incidence m)
    (hv : incidenceVertex P a=incidenceVertex P b) :
    normalizedIncidenceColor P β a=normalizedIncidenceColor P β b ↔
      incidenceColor P a=incidenceColor P b := by
  simp only [normalizedIncidenceColor,hv]
  exact (β (incidenceVertex P b)).injective.eq_iff

/-- Four local labels suffice for the two-generator Haar problem. -/
theorem color_two_card : Fintype.card (Color 2)=4 := by simp [Color]

end Nonadditivity.HaarPathClasses
