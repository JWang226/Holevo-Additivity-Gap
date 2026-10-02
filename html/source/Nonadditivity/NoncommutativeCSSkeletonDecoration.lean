/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSEndpointSkeleton
import Mathlib.Data.List.FinRange

/-! # Whole-block coefficient decoration and global sum bound

A middle block is decorated by one arbitrary coefficient operator depending
on its whole list of profile choices. No product decomposition of that
operator is required. The preceding compiler supplies all endpoint bookkeeping.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.NoncommutativeCS.EndpointSkeleton
open scoped BigOperators InnerProduct

variable {𝕜 E I J : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [Fintype J] [DecidableEq J]

def decorate {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E)
    (k : ℕ) : EndpointTrace 𝕜 E I J a b :=
  match P with
  | .done a => .done a
  | .first i P => .first i (fun j => A k [i] [j]) (P.decorate A (k + 1))
  | .last (a := a) p P => .last p (fun j => A k [a p] [j]) (P.decorate A (k + 1))
  | .middle (a := a) v P =>
      .middle (fun s => A k (v.map a) (v.map s)) (P.decorate A (k + 1))
  | .singleton i P => .singleton i (fun j => A k [i] [j]) (P.decorate A (k + 1))

/-- The independent variable names are determined by the occurrence trace,
and are independent of every coefficient operator. -/
theorem decorate_labels {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E) (k : ℕ) :
    List.ofFn (P.decorate A k).labels = P.profileLabels := by
  induction P generalizing k with
  | done => rfl
  | first i P ih =>
      simpa [decorate, EndpointTrace.labels, EndpointTrace.compile,
        AssignmentProgram.variableCount, List.ofFn_succ, profileLabels] using
        congrArg (List.cons i) (ih (k + 1))
  | last p P ih => exact ih (k + 1)
  | middle v P ih => exact ih (k + 1)
  | singleton i P ih =>
      simpa [decorate, EndpointTrace.labels, EndpointTrace.compile,
        AssignmentProgram.variableCount, List.ofFn_succ, profileLabels] using
        congrArg (List.cons i) (ih (k + 1))

def markedFlags {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointSkeleton I a b → List Bool
  | .done _ => []
  | .first _ P => true :: P.markedFlags
  | .last _ P => true :: P.markedFlags
  | .middle _ P => false :: P.markedFlags
  | .singleton _ P => true :: P.markedFlags

/-- Every independent label pays at most two marked occurrences, allowing
for the registers already open at the two boundaries. -/
theorem marked_count_boundary {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) :
    P.markedFlags.count true + n ≤ 2 * P.profileLabels.length + m := by
  induction P <;> simp_all [markedFlags, profileLabels] <;> omega

/-- Compression prevents adjacent middle blocks. The one possible extra
block occurs only if the trace itself starts in the middle. -/
theorem compressed_length_le {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (hP : P.Compressed) :
    P.markedFlags.length ≤ 2 * P.markedFlags.count true +
      (if P.startsMiddle then 1 else 0) := by
  induction P with
  | done => simp [markedFlags, startsMiddle]
  | first i P ih =>
      have h := ih hP
      cases hs : P.startsMiddle <;> simp_all [markedFlags, startsMiddle] <;> omega
  | last p P ih =>
      have h := ih hP
      cases hs : P.startsMiddle <;> simp_all [markedFlags, startsMiddle] <;> omega
  | middle v P ih =>
      obtain ⟨_, hs, hc⟩ := hP
      have h := ih hc
      simp_all [markedFlags, startsMiddle]
  | singleton i P ih =>
      have h := ih hP
      cases hs : P.startsMiddle <;> simp_all [markedFlags, startsMiddle] <;> omega

theorem startsMiddle_false_of_empty {n : ℕ} {b : Fin n → I}
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) b) (hP : P.Compressed) :
    P.startsMiddle = false := by
  cases P with
  | done => rfl
  | first => rfl
  | singleton => rfl
  | middle v P =>
      cases v with
      | nil => exact (hP.1 rfl).elim
      | cons p v => exact Fin.elim0 p

/-- The corrected BC coefficient exponent for an actual compressed trace.
This uses the true block count and counts the costly marked factors only. -/
theorem coefficient_exponent_le
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.Compressed) :
    P.markedFlags.length - 1 + P.markedFlags.count true ≤
      6 * P.profileLabels.length - 1 := by
  have hl := P.compressed_length_le hP
  rw [P.startsMiddle_false_of_empty hP] at hl
  have hm := P.marked_count_boundary
  simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hl hm
  omega

theorem decorate_markedFlags {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E) (k : ℕ) :
    (P.decorate A k).markedFlags = P.markedFlags := by
  induction P generalizing k <;> simp_all [decorate, markedFlags, EndpointTrace.markedFlags]

/-- Ordered factors read directly from a global assignment; middle blocks
receive their full profile list in one call to `A`. -/
def blockFactors {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E)
    (k : ℕ) (σ : I → J) : List (E →L[𝕜] E) :=
  match P with
  | .done _ => []
  | .first i P => P.blockFactors A (k + 1) σ ++ [A k [i] [σ i]]
  | .last (a := a) p P => P.blockFactors A (k + 1) σ ++ [A k [a p] [σ (a p)]]
  | .middle (a := a) v P =>
      P.blockFactors A (k + 1) σ ++ [A k (v.map a) ((v.map a).map σ)]
  | .singleton i P => P.blockFactors A (k + 1) σ ++ [A k [i] [σ i]]

theorem decorate_factors {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E)
    (k : ℕ) (σ : I → J) :
    (P.decorate A k).factors σ = P.blockFactors A k σ := by
  induction P generalizing k <;>
    simp_all [decorate, EndpointTrace.factors, blockFactors, List.map_map]

theorem coversLabels_of_profileLabels {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (P : EndpointSkeleton I a b) (A : ℕ → List I → List J → E →L[𝕜] E) (k : ℕ)
    (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels) :
    (P.decorate A k).CoversLabels := by
  constructor
  · apply List.nodup_ofFn.mp
    rw [decorate_labels]
    exact hn
  · intro i
    have hi := hc i
    rw [← decorate_labels P A k, List.mem_ofFn] at hi
    exact hi

/-- A fully compiled, literal sum over all global profiles for whole-block
operators, with the exact endpoint and middle operator costs. -/
theorem block_sum_norm_le [Fintype I] [DecidableEq I]
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (A : ℕ → List I → List J → E →L[𝕜] E) (k : ℕ)
    (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels) :
    ‖∑ σ : I → J, (P.blockFactors A k σ).prod‖ ≤ (P.decorate A k).compile.cost := by
  have h := (P.decorate A k).sum_products_norm_le (P.coversLabels_of_profileLabels A k hn hc)
  simpa only [decorate_factors] using h

theorem profileLabels_length_eq_card [Fintype I] [DecidableEq I]
    {m n : ℕ} {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b)
    (hn : P.profileLabels.Nodup) (hc : ∀ i : I, i ∈ P.profileLabels) :
    P.profileLabels.length = Fintype.card I := by
  have hu : P.profileLabels.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact List.mem_toFinset.mpr (hc i)
  simpa [hu] using (List.toFinset_card_of_nodup hn).symm

/-- For a word containing every label, the automatic compiler supplies all
coverage and distinctness facts needed by the global profile inequality. -/
theorem exists_closed_compiler [Fintype I] [DecidableEq I]
    (l : List I) (hl : ∀ i : I, i ∈ l) :
    ∃ P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I),
      P.word = l ∧ P.Compressed ∧ P.profileLabels.Nodup ∧
        (∀ i : I, i ∈ P.profileLabels) ∧
        P.markedFlags.length - 1 + P.markedFlags.count true ≤ 6 * Fintype.card I - 1 := by
  obtain ⟨P, hw, hp, hn, hc⟩ := exists_compressed l (Fin.elim0 : Fin 0 → I)
    (fun p => Fin.elim0 p) (fun p => Fin.elim0 p)
  have hc' : ∀ i : I, i ∈ P.profileLabels := by
    intro i
    apply (hc i).mpr
    exact ⟨hl i, by rintro ⟨p, _⟩; exact Fin.elim0 p⟩
  refine ⟨P, hw, hp, hn, hc', ?_⟩
  have h := P.coefficient_exponent_le hp
  rwa [P.profileLabels_length_eq_card hn hc'] at h

end Nonadditivity.NoncommutativeCS.EndpointSkeleton
