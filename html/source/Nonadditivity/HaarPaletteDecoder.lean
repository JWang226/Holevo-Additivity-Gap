/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarChainColoringPalettes
import Nonadditivity.HaarProfileAssignmentBound
import Mathlib.Data.List.GetD

/-! # Literal block decoding of the common word palette

Each block reads its chosen profile words in its actual orientations. The
decoder reverses the block order to match the coefficient-factor convention.
Its singleton restriction agrees exactly with the padded endpoint families.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPaletteDecoder
open HaarPathGraph HaarPathProfiles HaarProfileCoefficient HaarProfilePadding
  HaarProfileAssignmentBound

def paletteGroupWord {d M : ℕ} (w : Palette d M) : FreeGroup (Fin d) :=
  FreeGroup.mk (List.ofFn w.2)

@[simp] theorem paletteGroupWord_embedWords {d k M : ℕ} {p : Profile (Color d)}
    (hk : k≤M) (w : Words d k p) : paletteGroupWord (embedWords hk w)=word w := rfl

def orientedPalette {d M : ℕ} (forward : Bool) (w : Palette d M) : FreeGroup (Fin d) :=
  if forward then paletteGroupWord w else (paletteGroupWord w)⁻¹

@[simp] theorem orientedPalette_embedWords {d k M : ℕ} {p : Profile (Color d)}
    (hk : k≤M) (forward : Bool) (w : Words d k p) :
    orientedPalette forward (embedWords hk w)=orientedWord forward w := rfl

def decode {I : Type*} {d M : ℕ} (directions : ℕ → ℕ → Bool)
    (k : ℕ) (_labels : List I) (choices : List (Palette d M)) : FreeGroup (Fin d) :=
  ((choices.mapIdx (fun j w => orientedPalette (directions k j) w)).reverse).prod

def forward {I : Type*} (directions : ℕ → ℕ → Bool) (k : ℕ) (_i : I) : Bool :=
  directions k 0

@[simp] theorem decode_singleton {I : Type*} {d n M : ℕ} {p : Profile (Color d)}
    (directions : ℕ → ℕ → Bool) (k : ℕ) (i : I) (hn : n≤M) (w : Words d n p) :
    decode directions k [i] [embedWords hn w]=orientedWord (directions k 0) w := by
  simp [decode]

theorem decode_embedAssignment {I : Type*} {d M : ℕ}
    (directions : ℕ → ℕ → Bool) (size : I → ℕ) (profile : I → Profile (Color d))
    (hsize : ∀ i, size i≤M) (σ : ∀ i, Words d (size i) (profile i)) (k : ℕ) (i : I) :
    decode directions k [i] [embedAssignment size profile hsize σ i]=
      orientedWord (forward directions k i) (σ i) := by
  exact decode_singleton directions k i (hsize i) (σ i)

variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

def chainForward (c : P.CoreChain) : Bool := decide (c=P.representative (P.chainLabel c))

def chainEmbed (σ : P.ChainPalette) (e : P.unorientedChains) : Palette d m :=
  embedWords (P.coreChain_length_le (P.representative e)) (σ e)

theorem orientedPalette_chainEmbed (σ : P.ChainPalette) (c : P.CoreChain) :
    orientedPalette (chainForward P c) (chainEmbed P σ (P.chainLabel c))=
      word (P.paletteWord σ c) := by
  rw [P.paletteWord_word]
  simp only [chainEmbed,orientedPalette_embedWords,orientedWord,chainForward,decide_eq_true_eq]

/-- Exact decoding of one actual core-chain block, including repeated labels
and arbitrary mixtures of the two orientations. -/
theorem decode_chain_block (σ : P.ChainPalette) (directions : ℕ → ℕ → Bool)
    (k : ℕ) (cs : List P.CoreChain)
    (hdir : ∀ j (hj : j<cs.length), directions k j=chainForward P cs[j]) :
    decode directions k (cs.map P.chainLabel)
        (cs.map (fun c => chainEmbed P σ (P.chainLabel c))) =
      (cs.reverse.map (fun c => word (P.paletteWord σ c))).prod := by
  have he : (cs.map (fun c => chainEmbed P σ (P.chainLabel c))).mapIdx
      (fun j w => orientedPalette (directions k j) w) =
      cs.map (fun c => word (P.paletteWord σ c)) := by
    apply List.ext_getElem
    · simp
    · intro j hj hk
      have hj' : j<cs.length := by simpa using hj
      simp only [List.getElem_mapIdx,List.getElem_map]
      rw [hdir j hj',orientedPalette_chainEmbed P]
  unfold decode
  rw [he,List.map_reverse]

/-- Directions are read from the literal occurrence blocks. Out-of-range
entries are irrelevant to decoding and receive a fixed default. -/
def blockDirections (blocks : List (List P.CoreChain)) (k j : ℕ) : Bool :=
  match (blocks.getD k [])[j]? with
  | some c => chainForward P c
  | none => true

theorem blockDirections_get (blocks : List (List P.CoreChain)) (k : ℕ)
    (hk : k<blocks.length) (j : ℕ) (hj : j<blocks[k].length) :
    blockDirections P blocks k j=chainForward P blocks[k][j] := by
  simp only [blockDirections,List.getD_eq_getElem blocks [] hk,List.getElem?_eq_getElem hj]

theorem decode_actual_block (σ : P.ChainPalette) (blocks : List (List P.CoreChain))
    (k : ℕ) (hk : k<blocks.length) :
    decode (blockDirections P blocks) k (blocks[k].map P.chainLabel)
        (blocks[k].map (fun c => chainEmbed P σ (P.chainLabel c))) =
      (blocks[k].reverse.map (fun c => word (P.paletteWord σ c))).prod :=
  decode_chain_block P σ _ _ _ (blockDirections_get P blocks k hk)

end Nonadditivity.HaarPaletteDecoder
