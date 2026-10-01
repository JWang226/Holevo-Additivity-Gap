/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarChainColoring
import Nonadditivity.HaarProfileWordReverse
import Nonadditivity.HaarRepresentativePositions

/-! # Independent unoriented profile palettes

A choice of one reduced profile word for every unoriented core edge is exactly
a reversal-compatible assignment on all oriented chains. The equivalence has
no compatibility restrictions between distinct unoriented labels.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathGraph.Path
open HaarPathProfiles HaarProfileCoefficient
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

abbrev ChainPalette := ∀ e : P.unorientedChains,
  Words d (P.representative e).val.length (P.coreChainProfile (P.representative e)).val

def paletteWord (σ : P.ChainPalette) (c : P.CoreChain) :
    Words d c.val.length (P.coreChainProfile c).val := by
  classical
  by_cases h : c=P.representative (P.chainLabel c)
  · exact h.symm ▸ σ (P.chainLabel c)
  · have hr : c=P.coreChainReverse (P.representative (P.chainLabel c)) :=
      (P.eq_representative_or_reverse c).resolve_left h
    exact hr.symm ▸ P.reverseProfileWord _ (σ (P.chainLabel c))

@[simp] theorem paletteWord_representative (σ : P.ChainPalette) (e : P.unorientedChains) :
    P.paletteWord σ (P.representative e)=σ e := by
  simp [paletteWord,P.label_representative]
  apply eq_of_heq
  exact (eqRec_heq (φ := fun c : P.CoreChain =>
    Words d c.val.length (P.coreChainProfile c).val) _ _).trans
      (congr_arg_heq σ (P.label_representative e))

@[simp] theorem paletteWord_reverse_representative (σ : P.ChainPalette) (e : P.unorientedChains) :
    P.paletteWord σ (P.coreChainReverse (P.representative e))=
      P.reverseProfileWord (P.representative e) (σ e) := by
  simp [paletteWord,P.label_representative,P.coreChainReverse_ne_self]
  apply eq_of_heq
  exact (eqRec_heq (φ := fun c : P.CoreChain =>
    Words d c.val.length (P.coreChainProfile c).val) _ _).trans (congr_arg_heq
    (fun e => P.reverseProfileWord (P.representative e) (σ e))
    ((P.chainLabel_reverse _).trans (P.label_representative e)))

theorem word_cast_chain {c c' : P.CoreChain} (h : c=c')
    (w : Words d c.val.length (P.coreChainProfile c).val) :
    word (h ▸ w)=word w := by
  cases h
  rfl

/-- The coefficient uses the chosen representative word or its group inverse,
according to the literal orientation of the occurrence. -/
theorem paletteWord_word (σ : P.ChainPalette) (c : P.CoreChain) :
    word (P.paletteWord σ c) =
      if c=P.representative (P.chainLabel c) then word (σ (P.chainLabel c))
      else (word (σ (P.chainLabel c)))⁻¹ := by
  classical
  unfold paletteWord
  split_ifs
  · exact P.word_cast_chain _ _
  · rw [P.word_cast_chain,P.reverseProfileWord_word]

theorem paletteWord_reversal (σ : P.ChainPalette) (p : P.ChainPosition) :
    (P.paletteWord σ (P.reversePosition p).1).val (P.reversePosition p).2=
      flipColor ((P.paletteWord σ p.1).val p.2) := by
  have hpos (e : P.unorientedChains) (i : Fin (P.representative e).val.length) :
      (P.paletteWord σ (P.reversePosition ⟨P.representative e,i⟩).1).val
        (P.reversePosition ⟨P.representative e,i⟩).2 =
        flipColor ((P.paletteWord σ (P.representative e)).val i) := by
    change (P.paletteWord σ (P.coreChainReverse (P.representative e))).val
      (Fin.cast (P.coreChainReverse_length _).symm i.rev) = _
    rw [P.paletteWord_reverse_representative,P.paletteWord_representative,P.reverseProfileWord_val]
    apply congrArg flipColor
    apply congrArg (σ e).val
    apply Fin.ext
    simp only [Fin.val_cast,Fin.val_rev]
    rw [P.coreChainReverse_length]
    have hi := i.isLt
    omega
  obtain ⟨⟨e,i,b⟩,rfl⟩ := P.representativePosition_surjective p
  cases b
  · change (P.paletteWord σ (P.reversePosition (P.reversePosition ⟨P.representative e,i⟩)).1).val
      (P.reversePosition (P.reversePosition ⟨P.representative e,i⟩)).2 = _
    rw [P.reversePosition_involutive]
    have hh := congrArg flipColor (hpos e i)
    rw [flipColor_involutive] at hh
    exact hh.symm
  · exact hpos e i

def paletteColoring (σ : P.ChainPalette) : P.ChainColoring where
  value := P.paletteWord σ
  reversal := P.paletteWord_reversal σ

namespace ChainColoring
variable {P} (F : P.ChainColoring)

def palette : P.ChainPalette := fun e => F.value (P.representative e)

theorem value_reverse (c : P.CoreChain) :
    F.value (P.coreChainReverse c)=P.reverseProfileWord c (F.value c) := by
  apply Subtype.ext
  funext i
  let j : Fin c.val.length := (Fin.cast (P.coreChainReverse_length c) i).rev
  have hj : Fin.cast (P.coreChainReverse_length c).symm j.rev=i := by
    apply Fin.ext
    simp only [j,Fin.val_cast,Fin.val_rev]
    have hi : i.val<c.val.length := lt_of_lt_of_eq i.isLt (P.coreChainReverse_length c)
    omega
  have h := F.reversal ⟨c,j⟩
  change (F.value (P.coreChainReverse c)).val
    (Fin.cast (P.coreChainReverse_length c).symm j.rev)=flipColor ((F.value c).val j) at h
  rw [hj] at h
  rw [P.reverseProfileWord_val,h]
  apply congrArg flipColor
  apply congrArg (F.value c).val
  apply Fin.ext
  simp only [j,Fin.val_rev,Fin.val_cast]
  have hl := P.coreChainReverse_length c
  omega

@[ext] theorem ext {F G : P.ChainColoring} (h : ∀ c, F.value c=G.value c) : F=G := by
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      have he : f=g := funext h
      cases he
      rfl

end ChainColoring

@[simp] theorem paletteColoring_palette (σ : P.ChainPalette) :
    (P.paletteColoring σ).palette=σ := by
  funext e
  exact P.paletteWord_representative σ e

@[simp] theorem paletteColoring_of_palette (F : P.ChainColoring) :
    P.paletteColoring F.palette=F := by
  apply ChainColoring.ext
  intro c
  change P.paletteWord F.palette c=F.value c
  obtain ⟨e,hc | hc⟩ : ∃ e : P.unorientedChains,
      c=P.representative e ∨ c=P.coreChainReverse (P.representative e) :=
    ⟨P.chainLabel c,P.eq_representative_or_reverse c⟩
  · subst c
    exact P.paletteWord_representative F.palette e
  · subst c
    rw [P.paletteWord_reverse_representative,F.value_reverse]
    rfl

/-- Exact factorization into independent actual reduced profile families. -/
def chainPaletteEquiv : P.ChainPalette ≃ P.ChainColoring where
  toFun := P.paletteColoring
  invFun := ChainColoring.palette
  left_inv := P.paletteColoring_palette
  right_inv := P.paletteColoring_of_palette

end Nonadditivity.HaarPathGraph.Path
