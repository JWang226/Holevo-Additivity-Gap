/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ProductHaagerupBall

/-! # Canonical indices for finite product free-group balls -/
noncomputable section
universe u
namespace Nonadditivity.ProductHaagerupProduct
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ProductHaagerupBall (BallWords)

/-- Parenthesized product group used to expose the coordinate induction. -/
def GroupIndex (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | j+1 => FreeGroup α × GroupIndex α j

instance groupIndexGroup (α : Type*) (j : ℕ) : Group (GroupIndex α j) := by
  induction j with
  | zero => exact inferInstanceAs (Group PUnit)
  | succ j ih =>
    letI := ih
    exact inferInstanceAs (Group (FreeGroup α × GroupIndex α j))

/-- One independently reduced word per free-group coordinate. -/
def WordIndex (α : Type u) (q : ℕ) : ℕ → Type u
  | 0 => PUnit
  | j+1 => BallWords α q × WordIndex α q j

instance wordIndexFintype (α : Type*) [Fintype α] (q j : ℕ) : Fintype (WordIndex α q j) := by
  induction j with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ j ih =>
    letI := ih
    exact inferInstanceAs (Fintype (BallWords α q × WordIndex α q j))

def wordValue {α : Type*} {q : ℕ} : {j : ℕ} → WordIndex α q j → GroupIndex α j
  | 0, _ => PUnit.unit
  | _+1, w => (FreeGroup.mk w.1.2.1, wordValue w.2)

def reduced {α : Type*} {q : ℕ} : {j : ℕ} → WordIndex α q j → Prop
  | 0, _ => True
  | _+1, w => FreeGroup.IsReduced w.1.2.1 ∧ reduced w.2


instance groupIndexDecidableEq (α : Type*) [DecidableEq α] (j : ℕ) :
    DecidableEq (GroupIndex α j) := by
  induction j with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ j ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (FreeGroup α × GroupIndex α j))

def RadiusLe {α : Type*} [DecidableEq α] (q : ℕ) : {j : ℕ} → GroupIndex α j → Prop
  | 0, _ => True
  | _+1, g => FreeGroup.norm g.1 ≤ q ∧ RadiusLe q g.2

section Canonical
variable {α : Type*} [DecidableEq α] {q j : ℕ}

def canonicalBallWord (g : FreeGroup α) (hg : FreeGroup.norm g ≤ q) : BallWords α q :=
  ⟨⟨g.toWord.length, by change FreeGroup.norm g < q+1; omega⟩, ⟨g.toWord, rfl⟩⟩

def canonicalWord : {j : ℕ} → (g : GroupIndex α j) → RadiusLe q g → WordIndex α q j
  | 0, _, _ => PUnit.unit
  | _+1, g, hg => (canonicalBallWord g.1 hg.1, canonicalWord g.2 hg.2)

theorem wordValue_canonical (g : GroupIndex α j) (hg : RadiusLe q g) :
    wordValue (canonicalWord g hg) = g := by
  induction j with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ j ih =>
    apply Prod.ext
    · exact FreeGroup.mk_toWord
    · exact ih _ _

theorem canonical_reduced (g : GroupIndex α j) (hg : RadiusLe q g) :
    reduced (canonicalWord g hg) := by
  induction j with
  | zero => trivial
  | succ j ih => exact ⟨FreeGroup.isReduced_toWord, ih _ _⟩

theorem wordValue_radius (w : WordIndex α q j) : RadiusLe q (wordValue w) := by
  induction j with
  | zero => trivial
  | succ j ih =>
    refine ⟨?_, ih _⟩
    exact (FreeGroup.norm_mk_le.trans_eq w.1.2.2).trans (by omega)

theorem ballWord_mk_injective {u v : BallWords α q}
    (hu : FreeGroup.IsReduced u.2.1) (hv : FreeGroup.IsReduced v.2.1)
    (h : FreeGroup.mk u.2.1 = FreeGroup.mk v.2.1) : u = v := by
  have hl := congrArg FreeGroup.toWord h
  rw [FreeGroup.toWord_mk, FreeGroup.toWord_mk, hu.reduce_eq, hv.reduce_eq] at hl
  rcases u with ⟨lu,u⟩
  rcases v with ⟨lv,v⟩
  have he : lu = lv := by
    apply Fin.ext
    exact u.2.symm.trans ((congrArg List.length hl).trans v.2)
  subst lv
  congr 1
  exact Subtype.ext hl

/-- Reduced word indices do not count any group element twice. -/
theorem wordValue_injective_reduced {u v : WordIndex α q j}
    (hu : reduced u) (hv : reduced v) (h : wordValue u = wordValue v) : u = v := by
  induction j with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ j ih =>
    apply Prod.ext
    · exact ballWord_mk_injective hu.1 hv.1 (congrArg Prod.fst h)
    · exact ih hu.2 hv.2 (congrArg Prod.snd h)


/-- Exact summation over canonical reduced word representatives. -/
theorem sum_reduced_wordIndex [Fintype α] {M : Type*} [AddCommMonoid M]
    (S : Finset (GroupIndex α j)) (hS : ∀ g ∈ S, RadiusLe q g)
    (F : GroupIndex α j → M) :
    (∑ w : WordIndex α q j,
      if reduced w ∧ wordValue w ∈ S then F (wordValue w) else 0) = ∑ g ∈ S, F g := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun w _ => wordValue w)
  · intro w hw
    exact (Finset.mem_filter.mp hw).2.2
  · intro u hu v hv huv
    exact wordValue_injective_reduced (Finset.mem_filter.mp hu).2.1
      (Finset.mem_filter.mp hv).2.1 huv
  · intro g hg
    refine ⟨canonicalWord g (hS g hg), ?_, wordValue_canonical g (hS g hg)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨canonical_reduced g _, by rwa [wordValue_canonical]⟩
  · intro w hw
    rfl

end Canonical
end Nonadditivity.ProductHaagerupProduct
