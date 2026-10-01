/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathWeights

/-! # Row and column phase balance for literal Haar entry lists -/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathLocalPhase
open MeasureTheory HaarModel HaarFourthMoments HaarInvariantTensor HaarMixedMoments HaarPathWeights
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {N : ℕ}

@[simp] theorem mul_rowPhase_entry (i r s : Fin (N+1)) (z : ℂ)
    (hz : star z*z=1) (U : LocalUnitary N) :
    ((U * rowPhase i z hz : LocalUnitary N) : Mat N) r s =
      (if s=i then z else 1) * (U : Mat N) r s := by
  change ((U : Mat N) * Matrix.diagonal (fun a : Fin (N+1) => if a=i then z else 1)) r s = _
  simp [Matrix.mul_diagonal,mul_comm]

theorem integral_eq_zero_of_column_phase (f : LocalUnitary N → ℂ)
    (i : Fin (N+1)) (p q : ℕ) (hpq : p ≠ q)
    (hf : ∀ z : ℂ, ∀ hz : star z*z=1, ∀ U : LocalUnitary N,
      f (U * rowPhase i z hz) = (z^p * (star z)^q) * f U) :
    (∫ U, f U ∂haar N) = 0 := by
  let m := p+q+1
  have hm : m ≠ 0 := by dsimp [m]; omega
  let z := Complex.exp (2 * Real.pi * Complex.I / m)
  have hzprim : IsPrimitiveRoot z m := Complex.isPrimitiveRoot_exp m hm
  have hznorm : ‖z‖ = 1 := hzprim.norm'_eq_one hm
  have hz : star z*z=1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hznorm]
    norm_num
  have hne : z^p ≠ z^q := fun h => hpq (hzprim.pow_inj (by dsimp [m]; omega)
    (by dsimp [m]; omega) h)
  have h := integral_mul_right_eq_self (μ := haar N) f (rowPhase i z hz)
  simp_rw [hf, integral_const_mul] at h
  have hzq : (star z)^q * z^q = 1 := by rw [← mul_pow, hz, one_pow]
  have he : z^p * (∫ U, f U ∂haar N) = z^q * (∫ U, f U ∂haar N) := by
    calc
      _ = z^p * (((star z)^q * z^q) * (∫ U, f U ∂haar N)) := by rw [hzq, one_mul]
      _ = z^q * ((z^p * (star z)^q) * (∫ U, f U ∂haar N)) := by ring
      _ = _ := by rw [h]
  exact (mul_eq_mul_right_iff.mp he).resolve_left hne


lemma entryMonomial_column_phase {p q : ℕ}
    (i j : Tuple N p) (k l : Tuple N q)
    (r : Fin (N+1)) (z : ℂ) (hz : star z*z=1) (U : LocalUnitary N) :
    entryMonomial i j k l (U * rowPhase r z hz) =
      (z^(multiplicity j r) * (star z)^(multiplicity l r)) * entryMonomial i j k l U := by
  simp only [entryMonomial, mul_rowPhase_entry, star_mul, apply_ite star, star_one,
    Finset.prod_mul_distrib, prod_row_phase]
  ring

theorem integral_entryMonomial_eq_zero_of_column_mismatch {p q : ℕ}
    (i j : Tuple N p) (k l : Tuple N q) (r : Fin (N+1))
    (hr : multiplicity j r ≠ multiplicity l r) :
    (∫ U : LocalUnitary N, entryMonomial i j k l U ∂haar N)=0 :=
  integral_eq_zero_of_column_phase _ r _ _ hr (entryMonomial_column_phase i j k l r)

def rowCount (L : List (Entry N)) (r : Fin (N+1)) := (L.map Prod.fst).count r
def columnCount (L : List (Entry N)) (r : Fin (N+1)) := (L.map Prod.snd).count r

lemma rowCount_eq_multiplicity (L : List (Entry N)) (r : Fin (N+1)) :
    rowCount L r = multiplicity (fun a => (L.get a).1) r := by
  have h := HaarMatchingCount.count_ofFn_eq_card (fun a => (L.get a).1) r
  simpa only [rowCount, List.ofFn_comp', List.ofFn_get,
    HaarMixedMoments.multiplicity] using h

lemma columnCount_eq_multiplicity (L : List (Entry N)) (r : Fin (N+1)) :
    columnCount L r = multiplicity (fun a => (L.get a).2) r := by
  have h := HaarMatchingCount.count_ofFn_eq_card (fun a => (L.get a).2) r
  simpa only [columnCount, List.ofFn_comp', List.ofFn_get,
    HaarMixedMoments.multiplicity] using h

/-- Nonzero Haar monomials have identical row and column multiplicities in
the positive and negative lists, with no restriction on their degrees. -/
theorem counts_eq_of_integral_ne_zero (L R : List (Entry N))
    (h : (∫ U : LocalUnitary N, listMonomial L R U ∂haar N) ≠ 0) (r : Fin (N+1)) :
    rowCount L r=rowCount R r ∧ columnCount L r=columnCount R r := by
  simp_rw [listMonomial_eq_entryMonomial] at h
  constructor
  · by_contra hn
    rw [rowCount_eq_multiplicity, rowCount_eq_multiplicity] at hn
    exact h (HaarMixedMoments.integral_entryMonomial_eq_zero_of_row_mismatch _ _ _ _ r hn)
  · by_contra hn
    rw [columnCount_eq_multiplicity, columnCount_eq_multiplicity] at hn
    exact h (integral_entryMonomial_eq_zero_of_column_mismatch _ _ _ _ r hn)

lemma selected_rowCount_ofFn {m : ℕ} (f : Fin m → SignedEntry N)
    (c : HaarPathProfiles.Color 2) (v : Fin (N+1)) :
    rowCount (selected c (List.ofFn f)) v =
      (Finset.univ.filter (fun i => (f i).1=c ∧ (f i).2.1=v)).card := by
  have h : rowCount (selected c (List.ofFn f)) v =
      ∑ i, if (f i).1=c ∧ (f i).2.1=v then 1 else 0 := by
    induction m with
    | zero => simp [rowCount,selected]
    | succ m ih =>
      rw [List.ofFn_succ,Fin.sum_univ_succ]
      simp only [rowCount,selected,List.filter_cons] at ih ⊢
      by_cases hc : (f 0).1=c <;> by_cases hv : (f 0).2.1=v <;>
        simp_all [Nat.add_comm]
  simpa using h

lemma selected_columnCount_ofFn {m : ℕ} (f : Fin m → SignedEntry N)
    (c : HaarPathProfiles.Color 2) (v : Fin (N+1)) :
    columnCount (selected c (List.ofFn f)) v =
      (Finset.univ.filter (fun i => (f i).1=c ∧ (f i).2.2=v)).card := by
  have h : columnCount (selected c (List.ofFn f)) v =
      ∑ i, if (f i).1=c ∧ (f i).2.2=v then 1 else 0 := by
    induction m with
    | zero => simp [columnCount,selected]
    | succ m ih =>
      rw [List.ofFn_succ,Fin.sum_univ_succ]
      simp only [columnCount,selected,List.filter_cons] at ih ⊢
      by_cases hc : (f 0).1=c <;> by_cases hv : (f 0).2.2=v <;>
        simp_all [Nat.add_comm]
  simpa using h

end Nonadditivity.HaarPathLocalPhase
