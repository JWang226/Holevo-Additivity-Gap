/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.PolynomialReduction
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual word shortening on products of free groups

A canonical concatenation of coordinate words supplies a finite word
presentation. Prefix/suffix cuts therefore reduce the total product degree;
no commutation assumption between letters within a factor is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Nonadditivity.ProductPolynomialReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open PolynomialReduction

variable {α : Type} [DecidableEq α] {n : ℕ}
abbrev GroupWord (α : Type) (n : ℕ) := Fin n → FreeGroup α

def degree (w : GroupWord α n) : ℕ := ∑ j, FreeGroup.norm (w j)

@[simp] theorem degree_one : degree (1 : GroupWord α n) = 0 := by simp [degree]
@[simp] theorem degree_inv (w : GroupWord α n) : degree w⁻¹ = degree w := by simp [degree]

theorem degree_mul_le (v w : GroupWord α n) : degree (v*w) ≤ degree v + degree w := by
  simpa [degree, Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      FreeGroup.norm_mul_le (v j) (w j))

def generator (x : Fin n × α) : GroupWord α n :=
  fun j => if j=x.1 then FreeGroup.of x.2 else 1

@[simp] theorem degree_generator (x : Fin n × α) : degree (generator x) = 1 := by
  simp [degree, generator, apply_ite FreeGroup.norm]

def evaluate : FreeGroup (Fin n × α) →* GroupWord α n := FreeGroup.lift generator

theorem degree_evaluate_le (v : FreeGroup (Fin n × α)) :
    degree (evaluate v) ≤ FreeGroup.norm v := by
  have hlist : ∀ l : List ((Fin n × α) × Bool), degree (evaluate (FreeGroup.mk l)) ≤ l.length := by
    intro l
    induction l with
    | nil => simp [evaluate]
    | cons x l ih =>
      rw [evaluate, FreeGroup.lift_mk] at ih ⊢
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      have hx : degree (cond x.2 (generator x.1) (generator x.1)⁻¹) = 1 := by
        cases x.2 <;> simp
      exact (degree_mul_le _ _).trans (by omega)
  simpa only [FreeGroup.mk_toWord] using hlist v.toWord

/-- A coordinate word mapped into the free group on all labeled generators. -/
def localWord (j : Fin n) (v : FreeGroup α) : FreeGroup (Fin n × α) :=
  FreeGroup.map (fun a => (j,a)) v

theorem norm_localWord_le (j : Fin n) (v : FreeGroup α) :
    FreeGroup.norm (localWord j v) ≤ FreeGroup.norm v := by
  calc
    FreeGroup.norm (localWord j v) =
      FreeGroup.norm (FreeGroup.mk (v.toWord.map (fun x => ((j,x.1),x.2)))) := by
        rw [← FreeGroup.map.mk, FreeGroup.mk_toWord]
        rfl
    _ ≤ (v.toWord.map (fun x => ((j,x.1),x.2))).length := FreeGroup.norm_mk_le
    _ = FreeGroup.norm v := by simp [FreeGroup.norm]

theorem evaluate_localWord (j : Fin n) (v : FreeGroup α) (k : Fin n) :
    evaluate (localWord j v) k = if k=j then v else 1 := by
  have heq : (Pi.evalMonoidHom (fun _ : Fin n => FreeGroup α) k).comp
      (evaluate.comp (FreeGroup.map (fun a : α => (j,a)))) =
      (if k=j then MonoidHom.id (FreeGroup α) else 1) := by
    apply FreeGroup.ext_hom
    intro a
    by_cases h : k=j <;> simp [evaluate, generator, h]
  by_cases h : k=j <;>
    simpa [localWord, h] using congrArg (fun f : FreeGroup α →* FreeGroup α => f v) heq

/-- Canonical ordered concatenation, preserving the sum of coordinate lengths. -/
def flatten (w : GroupWord α n) : FreeGroup (Fin n × α) :=
  ((List.finRange n).map (fun j => localWord j (w j))).prod

theorem evaluate_flatten (w : GroupWord α n) : evaluate (flatten w) = w := by
  funext k
  change ((Pi.evalMonoidHom (fun _ : Fin n => FreeGroup α) k).comp evaluate) (flatten w) = w k
  simp only [flatten, map_list_prod, List.map_map, Function.comp_def]
  have heq : ∀ j : Fin n,
      ((Pi.evalMonoidHom (fun _ : Fin n => FreeGroup α) k).comp evaluate) (localWord j (w j)) =
        if k=j then w j else 1 := fun j => evaluate_localWord j (w j) k
  simp only [heq]
  rw [List.prod_map_eq_pow_single k]
  · simp
  · intro j hj hmem
    simp [Ne.symm hj]

theorem norm_flatten_le (w : GroupWord α n) : FreeGroup.norm (flatten w) ≤ degree w := by
  have hlist : ∀ l : List (Fin n),
      FreeGroup.norm ((l.map (fun j => localWord j (w j))).prod) ≤
        (l.map (fun j => FreeGroup.norm (w j))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact (FreeGroup.norm_mul_le _ _).trans (Nat.add_le_add (norm_localWord_le j (w j)) ih)
  simpa only [flatten, degree, Fin.sum_univ_def] using hlist (List.finRange n)

def firstPart (r : ℕ) (w : GroupWord α n) : GroupWord α n :=
  evaluate (firstHalf r (flatten w))
def secondPart (r : ℕ) (w : GroupWord α n) : GroupWord α n :=
  evaluate (suffix r (flatten w))

theorem parts_mul (r : ℕ) (w : GroupWord α n) : firstPart r w * secondPart r w = w := by
  rw [firstPart, secondPart, ← map_mul, firstHalf_mul_suffix, evaluate_flatten]

theorem degree_firstPart_le (r : ℕ) (w : GroupWord α n) : degree (firstPart r w) ≤ r :=
  (degree_evaluate_le _).trans (norm_firstHalf_le _ _)

theorem degree_secondPart_le (r : ℕ) (w : GroupWord α n) (hw : degree w ≤ 2*r) :
    degree (secondPart r w) ≤ r :=
  (degree_evaluate_le _).trans (norm_suffix_le _ _ ((norm_flatten_le w).trans hw))

/-- Deterministic support obtained from the two halves of every canonical word. -/
def splitSupport (T : Finset (GroupWord α n)) (r : ℕ) : Finset (GroupWord α n) :=
  insert 1 ((T.image fun w => (firstPart r w)⁻¹) ∪ T.image (secondPart r))

@[simp] theorem one_mem_splitSupport (T : Finset (GroupWord α n)) (r : ℕ) :
    (1 : GroupWord α n) ∈ splitSupport T r := by simp [splitSupport]

theorem subset_difference_splitSupport (T : Finset (GroupWord α n)) (r : ℕ) :
    T ⊆ Linearization.differenceSupport (splitSupport T r) := by
  intro w hw
  apply Linearization.mem_differenceSupport.mpr
  refine ⟨(firstPart r w)⁻¹, ?_, secondPart r w, ?_, ?_⟩
  · simp [splitSupport, Finset.mem_image_of_mem _ hw]
  · simp [splitSupport, Finset.mem_image_of_mem _ hw]
  · simpa using parts_mul r w

theorem splitSupport_degree (T : Finset (GroupWord α n)) (r : ℕ)
    (hT : ∀ w ∈ T, degree w ≤ 2*r) :
    ∀ w ∈ splitSupport T r, degree w ≤ r := by
  intro w hw
  simp only [splitSupport, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hw
  rcases hw with rfl | (⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩)
  · simp
  · simpa only [degree_inv] using degree_firstPart_le r v
  · exact degree_secondPart_le r v (hT v hv)

theorem splitSupport_card (T : Finset (GroupWord α n)) (r : ℕ) :
    (splitSupport T r).card ≤ 1 + 2*T.card := by
  calc
    (splitSupport T r).card ≤
        (((T.image fun w => (firstPart r w)⁻¹) ∪ T.image (secondPart r))).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (T.image fun w => (firstPart r w)⁻¹).card + (T.image (secondPart r)).card + 1 :=
      Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ T.card + T.card + 1 := Nat.add_le_add_right
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le) 1
    _ = 1 + 2*T.card := by omega

/-- Degree one is genuine linear support in the individual tensor-factor generators. -/
theorem degree_le_one_letters (w : GroupWord α n) (hw : degree w ≤ 1) :
    w = 1 ∨ ∃ x : Fin n × α, w = generator x ∨ w = (generator x)⁻¹ := by
  have hlen : (flatten w).toWord.length ≤ 1 := (norm_flatten_le w).trans hw
  have heval : evaluate (FreeGroup.mk (flatten w).toWord) = w := by
    rw [FreeGroup.mk_toWord, evaluate_flatten]
  cases hl : (flatten w).toWord with
  | nil =>
    left
    simpa [hl] using heval.symm
  | cons x l =>
    cases l with
    | nil =>
      right
      refine ⟨x.1, ?_⟩
      rw [hl] at heval
      cases hx : x.2 with
      | false =>
        right
        simpa [evaluate, FreeGroup.lift_mk, hx] using heval.symm
      | true =>
        left
        simpa [evaluate, FreeGroup.lift_mk, hx] using heval.symm
    | cons y l => simp [hl] at hlen

def halve (P : Polynomial (GroupWord α n)) (r : ℕ) : Polynomial (GroupWord α n) :=
  P.step (splitSupport P.support r) (one_mem_splitSupport _ _)

theorem halve_degree (P : Polynomial (GroupWord α n)) (r : ℕ)
    (hP : ∀ w ∈ P.support, degree w ≤ 2*r) :
    ∀ w ∈ (halve P r).support, degree w ≤ r :=
  splitSupport_degree P.support r hP

/-- Repeat the actual square-root factorization, ending with words of length one. -/
def reduce (P : Polynomial (GroupWord α n)) : ℕ → Polynomial (GroupWord α n)
  | 0 => P
  | k+1 => reduce (halve P (2^k)) k

/-- Exact enlargement multiplier of the recursively constructed coefficient space. -/
def dimensionCost (P : Polynomial (GroupWord α n)) : ℕ → ℕ
  | 0 => 1
  | k+1 => 2 * (splitSupport P.support (2^k)).card * dimensionCost (halve P (2^k)) k

/-- Actual product of the backward-error factors `6 |S|`. -/
def errorCost (P : Polynomial (GroupWord α n)) : ℕ → ℕ
  | 0 => 1
  | k+1 => 6 * (splitSupport P.support (2^k)).card * errorCost (halve P (2^k)) k

theorem dimensionCost_pos (P : Polynomial (GroupWord α n)) (k : ℕ) :
    0 < dimensionCost P k := by
  induction k generalizing P with
  | zero => simp [dimensionCost]
  | succ k ih =>
    have hB := Finset.card_pos.mpr (show (splitSupport P.support (2^k)).Nonempty from
      ⟨1, one_mem_splitSupport _ _⟩)
    exact Nat.mul_pos (Nat.mul_pos (by omega) hB) (ih _)

theorem errorCost_eq (P : Polynomial (GroupWord α n)) (k : ℕ) :
    errorCost P k = 3^k * dimensionCost P k := by
  induction k generalizing P with
  | zero => simp [errorCost, dimensionCost]
  | succ k ih => simp only [errorCost, dimensionCost, ih, pow_succ]; ring

theorem errorCost_pos (P : Polynomial (GroupWord α n)) (k : ℕ) : 0 < errorCost P k := by
  rw [errorCost_eq]
  exact Nat.mul_pos (by positivity) (dimensionCost_pos P k)

theorem reduce_dimension (P : Polynomial (GroupWord α n)) (k : ℕ) :
    Fintype.card (reduce P k).Index = Fintype.card P.Index * dimensionCost P k := by
  induction k generalizing P with
  | zero => simp [reduce, dimensionCost]
  | succ k ih =>
    rw [reduce, ih]
    change Fintype.card (P.step _ _).Index * _ = _
    rw [Polynomial.step_dimension]
    simp only [dimensionCost]
    ring

theorem reduce_degree (P : Polynomial (GroupWord α n)) (k : ℕ)
    (hP : ∀ w ∈ P.support, degree w ≤ 2^k) :
    ∀ w ∈ (reduce P k).support, degree w ≤ 1 := by
  induction k generalizing P with
  | zero => simpa only [reduce, pow_zero] using hP
  | succ k ih =>
    apply ih (halve P (2^k))
    apply halve_degree
    simpa only [pow_succ, Nat.mul_comm] using hP

/-- Every error-transfer hypothesis is discharged by the constructed factors.
Only the comparison for the final linear polynomial is supplied. -/
theorem reduce_error_transfer (P : Polynomial (GroupWord α n)) (k : ℕ)
    {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (π : GroupWord α n →* unitary (Matrix ν ν ℂ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfinal : ‖(reduce P k).finiteEval π‖ ≤
      (1+ε/(errorCost P k:ℝ))*‖(reduce P k).regularEval‖) :
    ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  induction k generalizing P ε with
  | zero => simpa only [reduce, errorCost, Nat.cast_one, div_one] using hfinal
  | succ k ih =>
    let B := (splitSupport P.support (2^k)).card
    have hB : 1 ≤ B := Finset.one_le_card.mpr ⟨1, one_mem_splitSupport _ _⟩
    have hBreal : (1:ℝ) ≤ B := by exact_mod_cast hB
    have h6B : (0:ℝ) < 6*(B:ℝ) := by positivity
    have hδ0 : 0 ≤ ε/(6*(B:ℝ)) := div_nonneg hε h6B.le
    have hδ1 : ε/(6*(B:ℝ)) ≤ 1 := by
      apply (div_le_iff₀ h6B).mpr
      nlinarith
    have hnorm := ih (halve P (2^k)) (ε/(6*(B:ℝ))) hδ0 hδ1 (by
      simpa only [reduce, errorCost, Nat.cast_mul, Nat.cast_ofNat, div_div,
        mul_assoc, B] using hfinal)
    have hstep := Polynomial.step_error_transfer P (splitSupport P.support (2^k))
      (one_mem_splitSupport _ _) (subset_difference_splitSupport _ _) π
      (ε/(6*(B:ℝ))) hδ0 hδ1 hnorm
    have heq : 6*(B:ℝ)*(ε/(6*(B:ℝ))) = ε := mul_div_cancel₀ ε h6B.ne'
    change ‖P.finiteEval π‖ ≤ (1 + 6*(B:ℝ)*(ε/(6*(B:ℝ)))) * ‖P.regularEval‖ at hstep
    simpa only [heq] using hstep

/-- Complete deterministic reduction of a degree `2^k` polynomial to a linear one.
The output coefficients, exact dimension cost, and comparison transfer are
constructed, without any assumed family of intermediate polynomials. -/
theorem constructed_linear_reduction (P : Polynomial (GroupWord α n)) (k : ℕ)
    (hP : ∀ w ∈ P.support, degree w ≤ 2^k) :
    ∃ Q : Polynomial (GroupWord α n),
      (∀ w ∈ Q.support, degree w ≤ 1) ∧
      Fintype.card Q.Index = Fintype.card P.Index * dimensionCost P k ∧
      errorCost P k = 3^k * dimensionCost P k ∧
      ∀ {ν : Type} [Fintype ν] [DecidableEq ν] [Nonempty ν]
        (π : GroupWord α n →* unitary (Matrix ν ν ℂ)) (ε : ℝ),
        0 ≤ ε → ε ≤ 1 →
        ‖Q.finiteEval π‖ ≤ (1+ε/(errorCost P k:ℝ))*‖Q.regularEval‖ →
        ‖P.finiteEval π‖ ≤ (1+ε)*‖P.regularEval‖ := by
  refine ⟨reduce P k, reduce_degree P k hP, reduce_dimension P k,
    errorCost_eq P k, ?_⟩
  intro ν _ _ _ π ε hε hε1 hfinal
  exact reduce_error_transfer P k π ε hε hε1 hfinal

/-- Safe closed-form bound on the actual coefficient enlargement. This deliberately
uses the constructed support cardinalities, not the sharper manuscript counts. -/
theorem dimensionCost_le (P : Polynomial (GroupWord α n)) (k : ℕ) :
    dimensionCost P k ≤ (2 * 3^k * max 1 P.support.card)^k := by
  induction k generalizing P with
  | zero => simp [dimensionCost]
  | succ k ih =>
    let M := max 1 P.support.card
    let B := (splitSupport P.support (2^k)).card
    have hM : 1 ≤ M := le_max_left _ _
    have hT : P.support.card ≤ M := le_max_right _ _
    have hB : B ≤ 3*M := by
      have hc := splitSupport_card P.support (2^k)
      dsimp [B]
      omega
    have hmax : max 1 (halve P (2^k)).support.card ≤ 3*M := by
      change max 1 B ≤ 3*M
      exact max_le (by omega) hB
    have hp : 1 ≤ 3^k := Nat.one_le_pow k 3 (by omega)
    have hbase : 2*B ≤ 2*3^(k+1)*M := by
      rw [pow_succ]
      nlinarith
    calc
      dimensionCost P (k+1) = 2*B*dimensionCost (halve P (2^k)) k := rfl
      _ ≤ 2*B*(2*3^k*max 1 (halve P (2^k)).support.card)^k :=
        Nat.mul_le_mul_left _ (ih _)
      _ ≤ 2*B*(2*3^(k+1)*M)^k := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        calc
          2*3^k*max 1 (halve P (2^k)).support.card ≤ 2*3^k*(3*M) :=
            Nat.mul_le_mul_left _ hmax
          _ = _ := by rw [pow_succ]; ring
      _ ≤ (2*3^(k+1)*M)*(2*3^(k+1)*M)^k := Nat.mul_le_mul_right _ hbase
      _ = (2*3^(k+1)*M)^(k+1) := by rw [pow_succ]; ring

theorem errorCost_le (P : Polynomial (GroupWord α n)) (k : ℕ) :
    errorCost P k ≤ (6 * 3^k * max 1 P.support.card)^k := by
  rw [errorCost_eq]
  calc
    3^k * dimensionCost P k ≤ 3^k * (2*3^k*max 1 P.support.card)^k :=
      Nat.mul_le_mul_left _ (dimensionCost_le P k)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Nonadditivity.ProductPolynomialReduction
