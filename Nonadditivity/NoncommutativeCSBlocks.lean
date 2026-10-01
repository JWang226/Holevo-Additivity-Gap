/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSSkeletonDecoration
import Mathlib.Data.List.SplitLengths

/-! # Literal blocks and occurrence lifts of endpoint skeletons

Each compressed middle run is a single block. Splitting an actual occurrence
list by these block lengths preserves every occurrence and hence all its
orientation data, while recovering precisely the skeleton's label blocks.
-/
noncomputable section
namespace Nonadditivity.NoncommutativeCS.EndpointSkeleton
variable {I C : Type*}

def blocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointSkeleton I a b → List (List I)
  | .done _ => []
  | .first i P => [i] :: P.blocks
  | .last (a := a) p P => [a p] :: P.blocks
  | .middle (a := a) visits P => visits.map a :: P.blocks
  | .singleton i P => [i] :: P.blocks

@[simp] theorem flatten_blocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) : P.blocks.flatten=P.word := by
  induction P <;> simp_all [blocks, word]

@[simp] theorem length_blocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) : P.blocks.length=P.markedFlags.length := by
  induction P <;> simp_all [blocks, markedFlags]

theorem blocks_nonempty {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (hP : P.Compressed) :
    ∀ block ∈ P.blocks, block ≠ [] := by
  induction P with
  | done => simp [blocks]
  | first i P ih => simpa [blocks] using ih hP
  | last p P ih => simpa [blocks] using ih hP
  | middle visits P ih => simpa [blocks] using And.intro hP.1 (ih hP.2.2)
  | singleton i P ih => simpa [blocks] using ih hP

private theorem map_splitLengths (f : C → I) (sizes : List ℕ) (cs : List C) :
    (sizes.splitLengths cs).map (List.map f)=sizes.splitLengths (cs.map f) := by
  induction sizes generalizing cs with
  | nil => simp
  | cons n ns ih => simp [List.splitLengths_cons, ih, List.map_take, List.map_drop]

private theorem splitLengths_lengths_flatten (ls : List (List I)) :
    (ls.map List.length).splitLengths ls.flatten=ls := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp [List.splitLengths_cons, ih]

/-- Actual occurrences split according to the skeleton, retaining their
full values rather than replacing them by label names. -/
def occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (cs : List C) : List (List C) :=
  (P.blocks.map List.length).splitLengths cs

theorem map_occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (label : C → I) (cs : List C)
    (hcs : cs.map label=P.word) :
    (P.occurrenceBlocks cs).map (List.map label)=P.blocks := by
  unfold occurrenceBlocks
  rw [map_splitLengths, hcs, ← P.flatten_blocks, splitLengths_lengths_flatten]

theorem flatten_occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (label : C → I) (cs : List C)
    (hcs : cs.map label=P.word) :
    (P.occurrenceBlocks cs).flatten=cs := by
  apply List.flatten_splitLengths
  have hlen := congrArg List.length hcs
  simpa only [List.length_map, ← P.flatten_blocks, List.length_flatten] using hlen.le

theorem lengths_occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (label : C → I) (cs : List C)
    (hcs : cs.map label=P.word) :
    (P.occurrenceBlocks cs).map List.length=P.blocks.map List.length := by
  have h := congrArg (List.map List.length) (P.map_occurrenceBlocks label cs hcs)
  simpa only [List.map_map, List.length_map, Function.comp_def] using h

@[simp] theorem length_occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (cs : List C) :
    (P.occurrenceBlocks cs).length=P.markedFlags.length := by
  simp [occurrenceBlocks]

theorem occurrenceBlocks_nonempty {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (hP : P.Compressed)
    (label : C → I) (cs : List C) (hcs : cs.map label=P.word) :
    ∀ block ∈ P.occurrenceBlocks cs, block ≠ [] := by
  intro block hb he
  have hm : block.map label ∈ P.blocks := by
    rw [← P.map_occurrenceBlocks label cs hcs]
    exact List.mem_map_of_mem hb
  exact P.blocks_nonempty hP _ hm (by simp [he])

/-- Reading the compiler from right to left restores the actual original
occurrence order, including all repeated orientations. -/
theorem flatten_reversed_occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (label : C → I) (cs : List C)
    (hcs : cs.reverse.map label=P.word) :
    ((P.occurrenceBlocks cs.reverse).reverse.map List.reverse).flatten=cs := by
  have h := congrArg List.reverse (P.flatten_occurrenceBlocks label cs.reverse hcs)
  simpa only [List.reverse_flatten, List.reverse_reverse, List.map_reverse] using h

theorem flatten_map_reversed_occurrenceBlocks {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (label : C → I) (cs : List C)
    (hcs : cs.reverse.map label=P.word) :
    ((P.occurrenceBlocks cs.reverse).map List.reverse).reverse.flatten=cs := by
  have h := congrArg List.reverse (P.flatten_occurrenceBlocks label cs.reverse hcs)
  simpa only [List.reverse_flatten, List.reverse_reverse] using h

/-- The register compiler multiplies the chronological blocks in reverse
order, with exactly their original absolute block indices. -/
theorem blockFactors_eq_reverse_mapIdx
    {𝕜 E J : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [Fintype J] [DecidableEq J]
    {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E)
    (k : ℕ) (σ : I → J) :
    P.blockFactors A k σ=
      (P.blocks.mapIdx (fun j ls => A (k+j) ls (ls.map σ))).reverse := by
  induction P generalizing k <;>
    simp_all [blocks, blockFactors, List.mapIdx_cons, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]

end Nonadditivity.NoncommutativeCS.EndpointSkeleton
