/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega

/-!
# Explicit free subgroup of the free group on two generators

The binary covering graph construction proves the manuscript's short
embedding lemma, with generator length bound `2 * Nat.log 2 (K-1) + 1`.
A concrete finite state permutation representation proves injectivity,
without a topological covering-space hypothesis or an assumed free basis.
The file also includes the elementary conjugate construction `x^i y x^-i`
with length bound `2*K-1`.
-/

namespace Nonadditivity.FreeEmbedding

abbrev Two := FreeGroup Bool

def x : Two := FreeGroup.of false
def y : Two := FreeGroup.of true

/-- The `i`th conjugate in the explicit infinite free subgroup. -/
def conjugate (i : ℕ) : Two := x ^ i * y * (x ^ i)⁻¹

private def leftRegular (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext z; simp
  map_mul' g h := by ext z; simp

private def shift : FreeGroup ℤ ≃* FreeGroup ℤ :=
  FreeGroup.freeGroupCongr (Equiv.addRight (1 : ℤ))

private theorem shift_of (i : ℤ) :
    shift (FreeGroup.of i) = FreeGroup.of (i + 1) := by
  change FreeGroup.map (Equiv.addRight (1 : ℤ)) (FreeGroup.of i) = _
  rw [FreeGroup.map.of]
  rfl

private def witnessAction : Two →* Equiv.Perm (FreeGroup ℤ) :=
  FreeGroup.lift (fun b : Bool => if b then Equiv.mulLeft (FreeGroup.of (0 : ℤ))
    else shift.toEquiv)

private theorem witness_x : witnessAction x = shift.toEquiv := by
  simp [witnessAction, x]

private theorem witness_y :
    witnessAction y = leftRegular (FreeGroup ℤ) (FreeGroup.of (0 : ℤ)) := by
  simp [witnessAction, y, leftRegular]

private theorem automorphism_conjugation (G : Type*) [Group G]
    (e : G ≃* G) (g : G) :
    e.toEquiv * leftRegular G g * e.toEquiv⁻¹ = leftRegular G (e g) := by
  ext z
  change e (g * e.symm z) = e g * z
  rw [map_mul, e.apply_symm_apply]

private theorem conjugate_succ (i : ℕ) :
    conjugate (i + 1) = x * conjugate i * x⁻¹ := by
  simp only [conjugate, pow_succ', mul_inv_rev, mul_assoc]

private theorem witness_conjugate (i : ℕ) :
    witnessAction (conjugate i) =
      leftRegular (FreeGroup ℤ) (FreeGroup.of (i : ℤ)) := by
  induction i with
  | zero => simpa [conjugate] using witness_y
  | succ i hi =>
      rw [conjugate_succ, map_mul, map_mul, map_inv, hi, witness_x,
        automorphism_conjugation, shift_of]
      simp

/-- The actual homomorphism sending generator `i` to `x^i y x^-i`. -/
def embedding (K : ℕ) : FreeGroup (Fin K) →* Two :=
  FreeGroup.lift (fun i => conjugate i.val)

@[simp] theorem embedding_of (K : ℕ) (i : Fin K) :
    embedding K (FreeGroup.of i) = conjugate i.val := by
  simp [embedding]

private theorem map_injective {α β : Type*} [Nonempty α]
    (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeGroup.map f) := by
  classical
  have hleft : Function.LeftInverse (FreeGroup.map (Function.invFun f))
      (FreeGroup.map f) := by
    intro g
    rw [FreeGroup.map.comp]
    rw [Function.invFun_comp hf]
    exact FreeGroup.map.id g
  exact hleft.injective

/-- Injectivity is proved by a concrete permutation representation of `F₂`.
The representation recovers each word in the independent integer-indexed
generators of `FreeGroup ℤ`. -/
theorem embedding_injective {K : ℕ} (hK : 0 < K) :
    Function.Injective (embedding K) := by
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let index : Fin K → ℤ := fun i => i.val
  have hindex : Function.Injective index := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℤ) = j.val at hij
    exact_mod_cast hij
  have hmap : Function.Injective (FreeGroup.map index) := map_injective index hindex
  have haction : witnessAction.comp (embedding K) =
      (leftRegular (FreeGroup ℤ)).comp (FreeGroup.map index) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, embedding_of, FreeGroup.map.of]
    exact witness_conjugate i.val
  intro g h heq
  apply hmap
  have heq' := congrArg (fun p : Equiv.Perm (FreeGroup ℤ) => p 1)
    (congrArg witnessAction heq)
  change (witnessAction.comp (embedding K) g) 1 =
    (witnessAction.comp (embedding K) h) 1 at heq'
  rw [haction] at heq'
  simpa [leftRegular] using heq'

/-- The explicit generators have at most `2*i+1` letters. -/
theorem norm_conjugate_le (i : ℕ) :
    FreeGroup.norm (conjugate i) ≤ 2 * i + 1 := by
  calc
    FreeGroup.norm (conjugate i) ≤
        FreeGroup.norm (x ^ i * y) + FreeGroup.norm ((x ^ i)⁻¹) :=
      FreeGroup.norm_mul_le _ _
    _ ≤ (FreeGroup.norm (x ^ i) + FreeGroup.norm y) +
        FreeGroup.norm ((x ^ i)⁻¹) :=
      Nat.add_le_add_right (FreeGroup.norm_mul_le _ _) _
    _ = 2 * i + 1 := by
      rw [FreeGroup.norm_inv_eq]
      simp [x, y, FreeGroup.norm_of_pow, FreeGroup.norm_of]
      omega

/-- A uniform bound for the generator images of the concrete embedding. -/
theorem norm_embedding_of_le (K : ℕ) (i : Fin K) :
    FreeGroup.norm (embedding K (FreeGroup.of i)) ≤ 2 * K - 1 := by
  rw [embedding_of]
  have hi := i.isLt
  exact (norm_conjugate_le i.val).trans (by omega)

end Nonadditivity.FreeEmbedding

namespace Nonadditivity.FreeEmbedding.Covering

private def child (b : Bool) (v : ℕ) : ℕ := 2 * v + if b then 2 else 1

private theorem child_pos (b : Bool) (v : ℕ) : 0 < child b v := by
  cases b <;> simp [child]

private theorem child_injective (b : Bool) : Function.Injective (child b) := by
  intro v w h
  cases b <;> simp [child] at h <;> omega

private theorem child_pair_injective {b c : Bool} {v w : ℕ}
    (h : child b v = child c w) : b = c ∧ v = w := by
  cases b <;> cases c <;> simp [child] at h ⊢ <;> omega

private def treeEdge (M : ℕ) (e : Bool × Fin M) : Prop := child e.1 e.2.val < M

private instance treeEdgeDecidable (M : ℕ) : DecidablePred (treeEdge M) :=
  fun e => inferInstanceAs (Decidable (child e.1 e.2.val < M))

private abbrev TreeEdges (M : ℕ) := {e : Bool × Fin M // treeEdge M e}
private abbrev ExtraEdges (M : ℕ) := {e : Bool × Fin M // ¬ treeEdge M e}

private def partialTarget (M : ℕ) (b : Bool) :
    {v : Fin M // child b v.val < M} → Fin M :=
  fun v => ⟨child b v.val, v.property⟩

private theorem partialTarget_injective (M : ℕ) (b : Bool) :
    Function.Injective (partialTarget M b) := by
  intro v w h
  apply Subtype.ext
  apply Fin.ext
  apply child_injective b
  exact congrArg Fin.val h

/-- Each partial labelled binary-tree map is completed to an actual permutation. -/
private noncomputable def transition (M : ℕ) (b : Bool) : Equiv.Perm (Fin M) :=
  (Equiv.ofInjective (partialTarget M b) (partialTarget_injective M b)).extendSubtype

private theorem transition_tree (M : ℕ) (b : Bool) (v : Fin M)
    (h : child b v.val < M) :
    (transition M b v).val = child b v.val := by
  unfold transition
  rw [Equiv.extendSubtype_apply_of_mem _ v h]
  rfl

private noncomputable def edgeLabel (M : ℕ) (b : Bool) (v : Fin M) :
    FreeGroup (ExtraEdges M) :=
  if h : treeEdge M (b, v) then 1 else FreeGroup.of ⟨(b, v), h⟩

private theorem edgeLabel_tree (M : ℕ) (b : Bool) (v : Fin M)
    (h : child b v.val < M) : edgeLabel M b v = 1 := by
  simp [edgeLabel, treeEdge, h]

private noncomputable def skew (M : ℕ) (b : Bool) :
    Equiv.Perm (Fin M × FreeGroup (ExtraEdges M)) where
  toFun z := (transition M b z.1, edgeLabel M b z.1 * z.2)
  invFun z := ((transition M b).symm z.1,
    (edgeLabel M b ((transition M b).symm z.1))⁻¹ * z.2)
  left_inv z := by simp
  right_inv z := by simp

private theorem skew_apply (M : ℕ) (b : Bool)
    (v : Fin M) (g : FreeGroup (ExtraEdges M)) :
    skew M b (v, g) = (transition M b v, edgeLabel M b v * g) := rfl

private noncomputable def action (M : ℕ) :
    Two →* Equiv.Perm (Fin M × FreeGroup (ExtraEdges M)) := FreeGroup.lift (skew M)

private theorem action_of (M : ℕ) (b : Bool) : action M (FreeGroup.of b) = skew M b := by
  simp [action]

private def parent (v : ℕ) : ℕ := (v - 1) / 2
private def parentLabel (v : ℕ) : Bool := decide (v % 2 = 0)

private theorem parent_lt {v : ℕ} (h : 0 < v) : parent v < v := by
  unfold parent
  omega

private theorem child_parent {v : ℕ} (h : 0 < v) :
    child (parentLabel v) (parent v) = v := by
  simp only [child, parentLabel, parent]
  split <;> simp_all <;> omega

private def path (v : ℕ) : Two :=
  if v = 0 then 1 else FreeGroup.of (parentLabel v) * path (parent v)
termination_by v
decreasing_by apply parent_lt; omega

private theorem path_zero : path 0 = 1 := by rw [path]; simp

private theorem path_pos {v : ℕ} (h : 0 < v) :
    path v = FreeGroup.of (parentLabel v) * path (parent v) := by
  rw [path]
  simp [Nat.ne_of_gt h]

private theorem path_action (M : ℕ) (hM : 0 < M) (v : ℕ) (hv : v < M)
    (g : FreeGroup (ExtraEdges M)) :
    action M (path v) (⟨0, hM⟩, g) = (⟨v, hv⟩, g) := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      by_cases hz : v = 0
      · subst v
        simp [path_zero]
      · have hp : parent v < v := parent_lt (Nat.pos_of_ne_zero hz)
        have hpM : parent v < M := hp.trans hv
        have hchild : child (parentLabel v) (parent v) = v :=
          child_parent (Nat.pos_of_ne_zero hz)
        rw [path_pos (Nat.pos_of_ne_zero hz), map_mul, Equiv.Perm.mul_apply,
          ih (parent v) hp hpM, action_of, skew_apply]
        have hc : child (parentLabel v) (⟨parent v, hpM⟩ : Fin M).val < M := by
          simpa [hchild] using hv
        rw [edgeLabel_tree M (parentLabel v) ⟨parent v, hpM⟩ hc, one_mul]
        congr 1
        apply Fin.ext
        rw [transition_tree M (parentLabel v) ⟨parent v, hpM⟩ hc]
        exact hchild

private theorem path_inverse_action (M : ℕ) (hM : 0 < M) (v : Fin M)
    (g : FreeGroup (ExtraEdges M)) :
    action M (path v.val)⁻¹ (v, g) = (⟨0, hM⟩, g) := by
  apply (action M (path v.val)).injective
  rw [map_inv]
  change (action M (path v.val)) ((action M (path v.val)).symm (v, g)) = _
  rw [Equiv.apply_symm_apply]
  exact (path_action M hM v.val v.isLt g).symm

private theorem norm_path_le (v : ℕ) : FreeGroup.norm (path v) ≤ Nat.log 2 (v + 1) := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      by_cases hz : v = 0
      · subst v; simp [path_zero, FreeGroup.norm_one]
      · have hv : 0 < v := Nat.pos_of_ne_zero hz
        have hp : parent v < v := parent_lt hv
        have hparent : parent v + 1 = (v + 1) / 2 := by unfold parent; omega
        have hlog : 1 ≤ Nat.log 2 (v + 1) :=
          (Nat.le_log_iff_pow_le (by decide) (by omega)).2 (by simp; omega)
        calc
          FreeGroup.norm (path v) ≤
              FreeGroup.norm (FreeGroup.of (parentLabel v)) +
              FreeGroup.norm (path (parent v)) := by
            rw [path_pos hv]
            exact FreeGroup.norm_mul_le _ _
          _ ≤ 1 + Nat.log 2 (parent v + 1) := by
            rw [FreeGroup.norm_of]
            exact Nat.add_le_add_left (ih (parent v) hp) 1
          _ = Nat.log 2 (v + 1) := by
            rw [hparent, Nat.log_div_base]
            omega

private noncomputable def basedLoop (M : ℕ) (e : ExtraEdges M) : Two :=
  (path (transition M e.val.1 e.val.2).val)⁻¹ *
    FreeGroup.of e.val.1 * path e.val.2.val

private theorem basedLoop_action (M : ℕ) (hM : 0 < M) (e : ExtraEdges M)
    (g : FreeGroup (ExtraEdges M)) :
    action M (basedLoop M e) (⟨0, hM⟩, g) =
      (⟨0, hM⟩, FreeGroup.of e * g) := by
  rw [basedLoop, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    path_action M hM e.val.2.val e.val.2.isLt g, action_of, skew_apply]
  have he : edgeLabel M e.val.1 e.val.2 = FreeGroup.of e := by
    simp [edgeLabel, e.property]
  rw [he]
  exact path_inverse_action M hM (transition M e.val.1 e.val.2) (FreeGroup.of e * g)

private noncomputable def loopMap (M : ℕ) : FreeGroup (ExtraEdges M) →* Two :=
  FreeGroup.lift (basedLoop M)

private theorem loopMap_action (M : ℕ) (hM : 0 < M) (w : FreeGroup (ExtraEdges M))
    (g : FreeGroup (ExtraEdges M)) :
    action M (loopMap M w) (⟨0, hM⟩, g) = (⟨0, hM⟩, w * g) := by
  induction w using FreeGroup.induction_on generalizing g with
  | C1 => simp
  | of e =>
      simpa [loopMap] using basedLoop_action M hM e g
  | inv_of e he =>
      apply (action M (loopMap M (FreeGroup.of e))).injective
      simp only [map_inv]
      change (action M (loopMap M (FreeGroup.of e)))
          ((action M (loopMap M (FreeGroup.of e))).symm (⟨0, hM⟩, g)) =
        (action M (loopMap M (FreeGroup.of e)))
          (⟨0, hM⟩, (FreeGroup.of e)⁻¹ * g)
      rw [Equiv.apply_symm_apply, he]
      simp
  | mul u v hu hv =>
      rw [map_mul, map_mul, Equiv.Perm.mul_apply, hv, hu]
      simp [mul_assoc]

private theorem loopMap_injective (M : ℕ) (hM : 0 < M) :
    Function.Injective (loopMap M) := by
  intro u v huv
  have h := congrArg (fun w => action M w (⟨0, hM⟩, 1)) huv
  simpa [loopMap_action M hM] using congrArg Prod.snd h

private theorem norm_basedLoop_le (M : ℕ) (e : ExtraEdges M) :
    FreeGroup.norm (basedLoop M e) ≤ 2 * Nat.log 2 M + 1 := by
  have hsource : Nat.log 2 (e.val.2.val + 1) ≤ Nat.log 2 M :=
    Nat.log_monotone (by omega)
  have htarget : Nat.log 2 ((transition M e.val.1 e.val.2).val + 1) ≤ Nat.log 2 M :=
    Nat.log_monotone (by have h := (transition M e.val.1 e.val.2).isLt; omega)
  calc
    FreeGroup.norm (basedLoop M e) ≤
        FreeGroup.norm ((path (transition M e.val.1 e.val.2).val)⁻¹ *
          FreeGroup.of e.val.1) + FreeGroup.norm (path e.val.2.val) :=
      FreeGroup.norm_mul_le _ _
    _ ≤ (FreeGroup.norm ((path (transition M e.val.1 e.val.2).val)⁻¹) +
        FreeGroup.norm (FreeGroup.of e.val.1)) + FreeGroup.norm (path e.val.2.val) :=
      Nat.add_le_add_right (FreeGroup.norm_mul_le _ _) _
    _ ≤ (Nat.log 2 M + 1) + Nat.log 2 M := by
      rw [FreeGroup.norm_inv_eq, FreeGroup.norm_of]
      exact Nat.add_le_add
        (Nat.add_le_add_right ((norm_path_le _).trans htarget) 1)
        ((norm_path_le _).trans hsource)
    _ = 2 * Nat.log 2 M + 1 := by omega

private def treeTarget (M : ℕ) (hM : 0 < M) :
    TreeEdges M → {v : Fin M // v ≠ ⟨0, hM⟩} := fun e =>
  ⟨⟨child e.val.1 e.val.2.val, e.property⟩, by
    intro h
    have hv := congrArg Fin.val h
    have hp := child_pos e.val.1 e.val.2.val
    change child e.val.1 e.val.2.val = 0 at hv
    omega⟩

private theorem treeTarget_injective (M : ℕ) (hM : 0 < M) :
    Function.Injective (treeTarget M hM) := by
  intro e f hef
  have hchild : child e.val.1 e.val.2.val = child f.val.1 f.val.2.val :=
    congrArg (fun z => z.val.val) hef
  obtain ⟨hb, hv⟩ := child_pair_injective hchild
  apply Subtype.ext
  exact Prod.ext hb (Fin.ext hv)

private theorem extraEdges_card (M : ℕ) (hM : 0 < M) :
    M + 1 ≤ Fintype.card (ExtraEdges M) := by
  classical
  have htree := Fintype.card_le_of_injective (treeTarget M hM) (treeTarget_injective M hM)
  have hnonroot : Fintype.card {v : Fin M // v ≠ ⟨0, hM⟩} = M - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hnonroot] at htree
  have hcomp : Fintype.card (ExtraEdges M) = 2 * M - Fintype.card (TreeEdges M) := by
    rw [Fintype.card_subtype_compl]
    simp
  omega

private noncomputable def edgeIndex (M : ℕ) (hM : 0 < M) : Fin (M + 1) ↪ ExtraEdges M :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa using extraEdges_card M hM))

/-- The binary covering graph gives `M+1` independent based loops in `F₂`. -/
noncomputable def shortEmbedding (M : ℕ) (hM : 0 < M) : FreeGroup (Fin (M + 1)) →* Two :=
  (loopMap M).comp (FreeGroup.map (edgeIndex M hM))

theorem shortEmbedding_injective (M : ℕ) (hM : 0 < M) :
    Function.Injective (shortEmbedding M hM) := by
  haveI : Nonempty (Fin (M + 1)) := ⟨0⟩
  exact (loopMap_injective M hM).comp
    (Nonadditivity.FreeEmbedding.map_injective (edgeIndex M hM) (edgeIndex M hM).injective)

theorem norm_shortEmbedding_of_le (M : ℕ) (hM : 0 < M) (i : Fin (M + 1)) :
    FreeGroup.norm (shortEmbedding M hM (FreeGroup.of i)) ≤ 2 * Nat.log 2 M + 1 := by
  simp only [shortEmbedding, MonoidHom.comp_apply, FreeGroup.map.of, loopMap,
    FreeGroup.lift_apply_of]
  exact norm_basedLoop_le M _

end Nonadditivity.FreeEmbedding.Covering

namespace Nonadditivity.FreeEmbedding

/-- The manuscript's embedding, obtained by completing the labelled binary
tree on `K-1` vertices and selecting `K` of its non-tree based loops. -/
noncomputable def logarithmicEmbedding (K : ℕ) (hK : 2 ≤ K) :
    FreeGroup (Fin K) →* Two :=
  (Covering.shortEmbedding (K - 1) (by omega)).comp
    (FreeGroup.freeGroupCongr (finCongr (by omega : K = K - 1 + 1))).toMonoidHom

theorem logarithmicEmbedding_injective (K : ℕ) (hK : 2 ≤ K) :
    Function.Injective (logarithmicEmbedding K hK) :=
  (Covering.shortEmbedding_injective (K - 1) (by omega)).comp
    (FreeGroup.freeGroupCongr (finCongr (by omega : K = K - 1 + 1))).injective

/-- Exact generator word length in the short free-group embedding.
`Nat.log 2 (K-1)` is the integer floor of the binary logarithm. -/
theorem norm_logarithmicEmbedding_of_le (K : ℕ) (hK : 2 ≤ K) (i : Fin K) :
    FreeGroup.norm (logarithmicEmbedding K hK (FreeGroup.of i)) ≤
      2 * Nat.log 2 (K - 1) + 1 := by
  unfold logarithmicEmbedding
  change FreeGroup.norm (Covering.shortEmbedding (K - 1) (by omega)
    (FreeGroup.map (finCongr (by omega : K = K - 1 + 1)) (FreeGroup.of i))) ≤ _
  rw [FreeGroup.map.of]
  exact Covering.norm_shortEmbedding_of_le (K - 1) (by omega) _

/-- Unconditional existence form of the short embedding lemma. -/
theorem exists_short_embedding (K : ℕ) (hK : 2 ≤ K) :
    ∃ f : FreeGroup (Fin K) →* FreeGroup Bool,
      Function.Injective f ∧ ∀ i : Fin K,
        FreeGroup.norm (f (FreeGroup.of i)) ≤ 2 * Nat.log 2 (K - 1) + 1 :=
  ⟨logarithmicEmbedding K hK, logarithmicEmbedding_injective K hK,
    norm_logarithmicEmbedding_of_le K hK⟩

end Nonadditivity.FreeEmbedding
