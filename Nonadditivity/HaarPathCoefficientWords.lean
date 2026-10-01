/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarProfileCoefficient
import Nonadditivity.HaarNonbacktrackingSegmentation
import Nonadditivity.HaarPathDecomposition

/-! # Reduced coefficient chunks from the actual closed path

The degree-two chain decomposition is connected to the free group coefficient
factorization. Reducedness and nontriviality of every occurring chain are
proved from the original path, rather than supplied as extra hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarPathGraph

open scoped BigOperators
open HaarPathProfiles HaarNonbacktracking HaarTimeCompositions

private theorem reducedPair {d : ℕ} (a b : Color d) (h : b ≠ flipColor a) :
    a.1 = b.1 → a.2 = b.2 := by
  rcases a with ⟨a,s⟩
  rcases b with ⟨b,t⟩
  intro hab
  change a = b at hab
  subst b
  cases s <;> cases t <;> simp_all [flipColor]

namespace Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

omit [DecidableEq V] in
/-- The signed generator list of the actual graph path is reduced. -/
theorem colorList_reduced : FreeGroup.IsReduced (List.ofFn P.colors) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hi' : i + 1 < m := by simpa using hi
  simp only [List.getElem_ofFn]
  exact reducedPair _ _ (P.reduced ⟨i, by omega⟩ ⟨i + 1, hi'⟩ rfl)

omit [DecidableEq V] in
@[simp] theorem color_traversalList : P.traversalList.map color = List.ofFn P.colors := by
  simp [traversalList, List.map_ofFn, Function.comp_def, traversal]

/-- An actual occurring core chain is a contiguous subword of the original path. -/
theorem chain_colors_reduced (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList)
    (c : P.CoreChain) (hc : c ∈ cs) : FreeGroup.IsReduced (c.val.map color) := by
  have hchain : c.val <:+: P.traversalList := by
    rw [← hcs]
    exact List.infix_of_mem_flatten (List.mem_map_of_mem hc)
  apply P.colorList_reduced.infix
  simpa only [P.color_traversalList] using hchain.map color

/-- The group element of the literal signed-color sequence on a core chain. -/
def chainWord (c : P.CoreChain) : FreeGroup (Fin d) := FreeGroup.mk (c.val.map color)

theorem chainWord_toWord (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList)
    (c : P.CoreChain) (hc : c ∈ cs) : (P.chainWord c).toWord = c.val.map color := by
  exact FreeGroup.toWord_mk.trans (P.chain_colors_reduced cs hcs c hc).reduce_eq

theorem chainWord_ne_one (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList)
    (c : P.CoreChain) (hc : c ∈ cs) : P.chainWord c ≠ 1 := by
  intro h
  have hw := P.chainWord_toWord cs hcs c hc
  rw [h, FreeGroup.toWord_one] at hw
  exact P.toCore_nonempty c.property.1 (List.map_eq_nil_iff.mp hw.symm)

/-- Concatenating the actual chain words recovers the original reduced word. -/
theorem chainWords_flatMap (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten = P.traversalList) :
    (cs.map P.chainWord).flatMap FreeGroup.toWord = List.ofFn P.colors := by
  rw [List.flatMap_map]
  have hf : cs.flatMap (fun c => (P.chainWord c).toWord) =
      cs.flatMap (fun c => c.val.map color) := by
    apply List.flatMap_congr
    intro c hc
    exact P.chainWord_toWord cs hcs c hc
  rw [hf]
  have he : cs.flatMap (fun c => c.val.map color) =
      (cs.map (fun c => c.val.map color)).flatten := by
    clear hcs hf
    induction cs with
    | nil => rfl
    | cons c cs ih => simp [ih]
  rw [he]
  have hm := congrArg (List.map color) hcs
  rw [List.map_flatten, List.map_map] at hm
  exact hm.trans P.color_traversalList

/-- The exact non-returning time expansion for the actual core-chain path
segments, with no assumed separation or reducedness of the segments. -/
theorem coefficient_factorization_chains {R : Type*} [Ring R]
    (A : MonoidAlgebra R (FreeGroup (Fin d)))
    (hA : ∀ a ∈ A.support, a.toWord.length ≤ 1)
    (c : P.CoreChain) (cs : List P.CoreChain)
    (hcs : ((c :: cs).map Subtype.val).flatten = P.traversalList) (n : ℕ) :
    (A ^ n) (FreeGroup.mk (List.ofFn P.colors)) =
      ∑ times ∈ compositions cs.length n,
        segmentedProduct A (P.chainWord c) (cs.map P.chainWord) times := by
  have hflat := P.chainWords_flatMap (c :: cs) hcs
  have hprod : FreeGroup.mk (List.ofFn P.colors) =
      (P.chainWord c :: cs.map P.chainWord).prod := by
    rw [← hflat, mk_flatMap_toWord]
    rfl
  rw [hprod]
  have hh : ∀ w ∈ P.chainWord c :: cs.map P.chainWord, w ≠ 1 := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (show w ∈ (c :: cs).map P.chainWord from hw)
    exact P.chainWord_ne_one (c :: cs) hcs q hq
  simpa only [List.length_map] using coefficient_factorization_segments A hA
    (P.chainWord c) (cs.map P.chainWord) hh
    (by rw [← List.map_cons, hflat]; exact P.colorList_reduced) n

end Path
end Nonadditivity.HaarPathGraph
