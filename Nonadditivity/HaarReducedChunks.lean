/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarNonbacktrackingSegmentation
import Mathlib.Data.List.Infix

/-! # Reduced, nontrivial group words on actual contiguous chunks

Grouping consecutive pieces of a reduced word introduces neither cancellation
nor trivial chunks. These identities supply the literal hypotheses of the
checked positive-time coefficient factorization.
-/
noncomputable section
namespace Nonadditivity.HaarNonbacktracking
variable {α C : Type*} [DecidableEq α]

theorem chunk_flatMap_reduced (chunks : List (List (FreeGroup α)))
    (hred : FreeGroup.IsReduced (chunks.flatten.flatMap FreeGroup.toWord))
    {chunk : List (FreeGroup α)} (hc : chunk ∈ chunks) :
    FreeGroup.IsReduced (chunk.flatMap FreeGroup.toWord) := by
  exact hred.infix ((List.infix_of_mem_flatten hc).flatMap FreeGroup.toWord)

theorem chunk_prod_toWord (chunks : List (List (FreeGroup α)))
    (hred : FreeGroup.IsReduced (chunks.flatten.flatMap FreeGroup.toWord))
    {chunk : List (FreeGroup α)} (hc : chunk ∈ chunks) :
    chunk.prod.toWord=chunk.flatMap FreeGroup.toWord :=
  toWord_prod_of_reduced chunk (chunk_flatMap_reduced chunks hred hc)

theorem chunk_prod_ne_one (chunks : List (List (FreeGroup α)))
    (hred : FreeGroup.IsReduced (chunks.flatten.flatMap FreeGroup.toWord))
    (hne : ∀ g ∈ chunks.flatten, g≠1)
    {chunk : List (FreeGroup α)} (hc : chunk ∈ chunks) (hchunk : chunk≠[]) :
    chunk.prod≠1 := by
  cases chunk with
  | nil => exact (hchunk rfl).elim
  | cons g gs =>
      exact prod_cons_ne_one_of_reduced g gs
        (hne g (List.mem_flatten.mpr ⟨g::gs,hc,by simp⟩))
        (chunk_flatMap_reduced chunks hred hc)

theorem chunk_products_flatMap (chunks : List (List (FreeGroup α)))
    (hred : FreeGroup.IsReduced (chunks.flatten.flatMap FreeGroup.toWord)) :
    (chunks.map List.prod).flatMap FreeGroup.toWord =
      chunks.flatten.flatMap FreeGroup.toWord := by
  rw [List.flatMap_map]
  calc
    _ = chunks.flatMap (fun c => c.flatMap FreeGroup.toWord) := by
      apply List.flatMap_congr
      intro c hc
      exact chunk_prod_toWord chunks hred hc
    _ = _ := by
      clear hred
      induction chunks with
      | nil => rfl
      | cons c cs ih =>
          simp only [List.flatMap_cons,List.flatten_cons,List.flatMap_append]
          exact congrArg (c.flatMap FreeGroup.toWord ++ ·) ih

theorem chunk_products_reduced (chunks : List (List (FreeGroup α)))
    (hred : FreeGroup.IsReduced (chunks.flatten.flatMap FreeGroup.toWord)) :
    FreeGroup.IsReduced ((chunks.map List.prod).flatMap FreeGroup.toWord) := by
  rwa [chunk_products_flatMap chunks hred]

theorem chunk_products_nontrivial (chunks : List (List (FreeGroup α)))
    (hred : FreeGroup.IsReduced (chunks.flatten.flatMap FreeGroup.toWord))
    (hne : ∀ g ∈ chunks.flatten, g≠1) (hchunks : ∀ c∈chunks, c≠[]) :
    ∀ g∈chunks.map List.prod, g≠1 := by
  intro g hg
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hg
  exact chunk_prod_ne_one chunks hred hne hc (hchunks c hc)

/-- Payload form: every original occurrence retains its own orientation and
word; the chunks need only concatenate to the original occurrence list. -/
theorem occurrence_chunk_spec (cs : List C) (chunks : List (List C))
    (φ : C → FreeGroup α) (hflat : chunks.flatten=cs)
    (hred : FreeGroup.IsReduced ((cs.map φ).flatMap FreeGroup.toWord))
    (hne : ∀ c∈cs, φ c≠1) (hchunks : ∀ c∈chunks, c≠[]) :
    let gs := chunks.map (fun c => (c.map φ).prod)
    gs.flatMap FreeGroup.toWord = (cs.map φ).flatMap FreeGroup.toWord ∧
      FreeGroup.IsReduced (gs.flatMap FreeGroup.toWord) ∧
      (∀ g∈gs, g≠1) ∧ gs.prod=(cs.map φ).prod := by
  let ls := chunks.map (List.map φ)
  have hl : ls.flatten=cs.map φ := by
    rw [←List.map_flatten,hflat]
  have hr : FreeGroup.IsReduced (ls.flatten.flatMap FreeGroup.toWord) := by rwa [hl]
  have hn : ∀ g∈ls.flatten, g≠1 := by
    rw [hl]
    intro g hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hg
    exact hne c hc
  have hls : ∀ c∈ls, c≠[] := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    exact fun he => hchunks b hb (List.map_eq_nil_iff.mp he)
  have hword := chunk_products_flatMap ls hr
  rw [hl] at hword
  have hgn := chunk_products_nontrivial ls hr hn hls
  have hgr := chunk_products_reduced ls hr
  have hprod := congrArg FreeGroup.mk hword
  rw [mk_flatMap_toWord,mk_flatMap_toWord] at hprod
  have hout := And.intro hword (And.intro hgr (And.intro hgn hprod))
  simpa only [ls,List.map_map,Function.comp_def] using hout

end Nonadditivity.HaarNonbacktracking
