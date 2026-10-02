/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSEndpointTrace

/-! # Automatic compressed endpoint skeletons

The purely finite compiler below opens a label at its first repeated visit,
closes it at its last visit, and sums a singleton at its sole visit. Consecutive
middle visits are merged into one block. A later decoration may attach an
arbitrary operator to the whole block, without factorizing that operator.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Nonadditivity.NoncommutativeCS

inductive EndpointSkeleton (I : Type*) :
    {m n : ℕ} → (Fin m → I) → (Fin n → I) → Type _
  | done {n : ℕ} (layout : Fin n → I) : EndpointSkeleton I layout layout
  | first {m n : ℕ} {a : Fin m → I} {b : Fin n → I} (i : I)
      (rest : EndpointSkeleton I (Fin.cons i a) b) : EndpointSkeleton I a b
  | last {m n : ℕ} {a : Fin (m + 1) → I} {b : Fin n → I} (p : Fin (m + 1))
      (rest : EndpointSkeleton I (p.removeNth a) b) : EndpointSkeleton I a b
  | middle {m n : ℕ} {a : Fin m → I} {b : Fin n → I} (visits : List (Fin m))
      (rest : EndpointSkeleton I a b) : EndpointSkeleton I a b
  | singleton {m n : ℕ} {a : Fin m → I} {b : Fin n → I} (i : I)
      (rest : EndpointSkeleton I a b) : EndpointSkeleton I a b

namespace EndpointSkeleton
variable {I : Type*}

def word {m n : ℕ} {a : Fin m → I} {b : Fin n → I} : EndpointSkeleton I a b → List I
  | .done _ => []
  | .first i P => i :: P.word
  | .last (a := a) p P => a p :: P.word
  | .middle (a := a) v P => v.map a ++ P.word
  | .singleton i P => i :: P.word

def profileLabels {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointSkeleton I a b → List I
  | .done _ => []
  | .first i P => i :: P.profileLabels
  | .last _ P => P.profileLabels
  | .middle _ P => P.profileLabels
  | .singleton i P => i :: P.profileLabels

def startsMiddle {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointSkeleton I a b → Bool
  | .middle _ _ => true
  | _ => false

def Compressed {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointSkeleton I a b → Prop
  | .done _ => True
  | .first _ P => P.Compressed
  | .last _ P => P.Compressed
  | .middle v P => v ≠ [] ∧ P.startsMiddle = false ∧ P.Compressed
  | .singleton _ P => P.Compressed

/-- Prepending a middle visit merges it with the next middle block. -/
def prependMiddle {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (p : Fin m) : EndpointSkeleton I a b → EndpointSkeleton I a b
  | .middle v P => .middle (p :: v) P
  | P => .middle [p] P

@[simp] theorem word_prependMiddle {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (p : Fin m) (P : EndpointSkeleton I a b) :
    (P.prependMiddle p).word = a p :: P.word := by
  cases P <;> simp [prependMiddle, word]

@[simp] theorem profileLabels_prependMiddle {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (p : Fin m) (P : EndpointSkeleton I a b) :
    (P.prependMiddle p).profileLabels = P.profileLabels := by
  cases P <;> rfl

theorem compressed_prependMiddle {m n : ℕ} {a : Fin m → I} {b : Fin n → I}
    (p : Fin m) {P : EndpointSkeleton I a b} (hP : P.Compressed) :
    (P.prependMiddle p).Compressed := by
  cases P <;> simp_all [prependMiddle, Compressed, startsMiddle]

theorem mem_range_removeNth {m : ℕ} {a : Fin (m + 1) → I}
    (ha : Function.Injective a) (p : Fin (m + 1)) (i : I) :
    i ∈ Set.range (p.removeNth a) ↔ i ∈ Set.range a ∧ i ≠ a p := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨⟨p.succAbove q, rfl⟩, ?_⟩
    exact fun h => Fin.succAbove_ne p q (ha h)
  · rintro ⟨⟨q, rfl⟩, hq⟩
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (show q ≠ p from fun h => hq (congrArg a h))
    exact ⟨r, congrArg a hr⟩

/-- Every finite occurrence sequence admits a compressed first/last trace.
The independent profileLabels are precisely the labels not already open at the
start, each introduced once. No coefficient or norm assertion is assumed. -/
theorem exists_compressed [DecidableEq I] (l : List I) :
    ∀ {m : ℕ} (a : Fin m → I), Function.Injective a → (∀ p, a p ∈ l) →
      ∃ P : EndpointSkeleton I a (Fin.elim0 : Fin 0 → I),
        P.word = l ∧ P.Compressed ∧ P.profileLabels.Nodup ∧
          ∀ i, i ∈ P.profileLabels ↔ i ∈ l ∧ i ∉ Set.range a := by
  induction l with
  | nil =>
      intro m a ha hl
      cases m with
      | zero =>
          have he : a = (Fin.elim0 : Fin 0 → I) := Subsingleton.elim _ _
          subst a
          refine ⟨.done Fin.elim0, rfl, trivial, List.nodup_nil, ?_⟩
          simp [profileLabels]
      | succ m => simpa using hl (0 : Fin (m + 1))
  | cons i l ih =>
      intro m a ha hl
      by_cases hi : i ∈ Set.range a
      · obtain ⟨p, hp⟩ := hi
        by_cases hf : i ∈ l
        · have hl' : ∀ q, a q ∈ l := by
            intro q
            rcases List.mem_cons.mp (hl q) with hq | hq
            · exact hq ▸ hf
            · exact hq
          obtain ⟨P, hword, hcomp, hnodup, hvars⟩ := ih a ha hl'
          refine ⟨P.prependMiddle p, ?_, compressed_prependMiddle p hcomp, ?_, ?_⟩
          · simp [hword, hp]
          · simpa using hnodup
          · intro j
            rw [profileLabels_prependMiddle, hvars]
            have hi : i ∈ Set.range a := ⟨p, hp⟩
            simp only [List.mem_cons]
            by_cases he : j = i
            · subst j; simp [hi]
            · simp [he]
        · cases m with
          | zero => exact Fin.elim0 p
          | succ m =>
              have hb : Function.Injective (p.removeNth a) := ha.comp Fin.succAbove_right_injective
              have hl' : ∀ q, p.removeNth a q ∈ l := by
                intro q
                have hq := hl (p.succAbove q)
                rcases List.mem_cons.mp hq with hq | hq
                · have he : p.succAbove q = p := ha (hq.trans hp.symm)
                  exact (Fin.succAbove_ne p q he).elim
                · exact hq
              obtain ⟨P, hword, hcomp, hnodup, hvars⟩ := ih (p.removeNth a) hb hl'
              refine ⟨.last p P, ?_, hcomp, hnodup, ?_⟩
              · simp [word, hp, hword]
              · intro j
                change j ∈ P.profileLabels ↔ _
                rw [hvars, mem_range_removeNth ha p j, hp]
                simp only [List.mem_cons]
                by_cases he : j = i
                · subst j
                  simp [hf, show i ∈ Set.range a from ⟨p, hp⟩]
                · tauto
      · have hl' : ∀ q, a q ∈ l := by
          intro q
          rcases List.mem_cons.mp (hl q) with hq | hq
          · exact (hi ⟨q, hq⟩).elim
          · exact hq
        by_cases hf : i ∈ l
        · have hb : Function.Injective (Fin.cons i a) := Fin.cons_injective_of_injective hi ha
          have hlb : ∀ q : Fin (m + 1), (Fin.cons i a : Fin (m + 1) → I) q ∈ l := by
            intro q
            refine Fin.cases hf (fun r => ?_) q
            exact hl' r
          obtain ⟨P, hword, hcomp, hnodup, hvars⟩ := ih (Fin.cons i a) hb hlb
          have hnot : i ∉ P.profileLabels := by
            rw [hvars]
            simp [Fin.range_cons]
          refine ⟨.first i P, ?_, hcomp, List.nodup_cons.mpr ⟨hnot, hnodup⟩, ?_⟩
          · simp [word, hword]
          · intro j
            simp only [profileLabels, List.mem_cons, hvars, Fin.range_cons, Set.mem_insert_iff]
            by_cases he : j = i
            · subst j; simp [hi]
            · simp [he]
        · obtain ⟨P, hword, hcomp, hnodup, hvars⟩ := ih a ha hl'
          have hnot : i ∉ P.profileLabels := by rw [hvars]; simp [hf]
          refine ⟨.singleton i P, ?_, hcomp, List.nodup_cons.mpr ⟨hnot, hnodup⟩, ?_⟩
          · simp [word, hword]
          · intro j
            simp only [profileLabels, List.mem_cons, hvars]
            by_cases he : j = i
            · subst j; simp [hi]
            · simp [he]

end EndpointSkeleton
end Nonadditivity.NoncommutativeCS
