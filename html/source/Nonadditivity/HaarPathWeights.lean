/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPairEntryBound
import Nonadditivity.HaarPathGraph
import Nonadditivity.HaarWordPhase

/-! # Actual two-generator path weights

A literal path contributes a product of ordinary and conjugated Haar entries.
This file connects those products to the proved Weingarten entry estimate.
-/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarPathWeights
open MeasureTheory HaarModel HaarInvariantTensor HaarPathMultiplicity HaarFourthMoments
open scoped BigOperators Matrix Matrix.Norms.L2Operator

abbrev Entry (N : ℕ) := Fin (N+1) × Fin (N+1)
abbrev SignedEntry (N : ℕ) := (Fin 2 × Bool) × Entry N

def selected {N : ℕ} (c : Fin 2 × Bool) (L : List (SignedEntry N)) : List (Entry N) :=
  (L.filter (fun e => e.1=c)).map Prod.snd

def entryProduct {N : ℕ} (L : List (Entry N)) (U : LocalUnitary N) : ℂ :=
  (L.map (fun e => (U : Mat N) e.1 e.2)).prod

def listMonomial {N : ℕ} (L R : List (Entry N)) (U : LocalUnitary N) : ℂ :=
  entryProduct L U * star (entryProduct R U)

def signedProduct {N : ℕ} (L : List (SignedEntry N)) (U : LocalUnitary N × LocalUnitary N) : ℂ :=
  (L.map (fun e => if e.1.2 then
    ((if e.1.1=0 then U.1 else U.2) : Mat N) e.2.1 e.2.2 else
    star (((if e.1.1=0 then U.1 else U.2) : Mat N) e.2.1 e.2.2))).prod

/-- Sorting entries by their generator and sign does not change the scalar
product associated with the original ordered path. -/
theorem signedProduct_eq {N : ℕ} (L : List (SignedEntry N))
    (U : LocalUnitary N × LocalUnitary N) :
    signedProduct L U =
      listMonomial (selected (0,true) L) (selected (0,false) L) U.1 *
      listMonomial (selected (1,true) L) (selected (1,false) L) U.2 := by
  induction L with
  | nil => simp [signedProduct, listMonomial, selected, entryProduct]
  | cons e L ih =>
    obtain ⟨⟨a,b⟩,x⟩ := e
    fin_cases a <;> cases b <;>
      simp [signedProduct, listMonomial, selected, entryProduct,
        star_mul] at ih ⊢ <;> rw [ih] <;> ring

/-- List and tuple presentations are definitionally the same Haar monomial
up to the standard finite-product enumeration. -/
theorem listMonomial_eq_entryMonomial {N : ℕ} (L R : List (Entry N))
    (U : LocalUnitary N) :
    listMonomial L R U = HaarMixedMoments.entryMonomial
      (fun a => (L.get a).1) (fun a => (L.get a).2)
      (fun a => (R.get a).1) (fun a => (R.get a).2) U := by
  simp only [listMonomial, entryProduct, HaarMixedMoments.entryMonomial]
  have hp (S : List (Entry N)) (f : Entry N → ℂ) :
      (S.map f).prod = ∏ a : Fin S.length, f (S.get a) := by
    rw [← List.prod_ofFn, List.ofFn_comp', List.ofFn_get]
  rw [hp L, hp R]
  simp only [star_prod]

/-- A Haar monomial with unequal total positive and negative degrees vanishes. -/
theorem integral_entryMonomial_eq_zero_of_degree_ne {N p q : ℕ}
    (i j : Tuple N p) (k l : Tuple N q) (hpq : p ≠ q) :
    (∫ U : LocalUnitary N, HaarMixedMoments.entryMonomial i j k l U ∂haar N)=0 := by
  have hsum (x : Fin p → Fin (N+1)) :
      (∑ r, HaarMixedMoments.multiplicity x r)=p := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ) (f := x) (fun _ _ => Finset.mem_univ _)
    simpa [HaarMixedMoments.multiplicity] using h.symm
  have hsumq (x : Fin q → Fin (N+1)) :
      (∑ r, HaarMixedMoments.multiplicity x r)=q := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
      (t := Finset.univ) (f := x) (fun _ _ => Finset.mem_univ _)
    simpa [HaarMixedMoments.multiplicity] using h.symm
  have hex : ∃ r, HaarMixedMoments.multiplicity i r ≠ HaarMixedMoments.multiplicity k r := by
    by_contra! h
    exact hpq ((hsum i).symm.trans ((Finset.sum_congr rfl (fun r _ => h r)).trans (hsumq k)))
  obtain ⟨r,hr⟩ := hex
  exact HaarMixedMoments.integral_entryMonomial_eq_zero_of_row_mismatch i j k l r hr

/-- Exact zero for an unbalanced literal entry list. -/
theorem integral_listMonomial_eq_zero_of_length_ne {N : ℕ} (L R : List (Entry N))
    (h : L.length ≠ R.length) :
    (∫ U : LocalUnitary N, listMonomial L R U ∂haar N)=0 := by
  simp_rw [listMonomial_eq_entryMonomial]
  exact integral_entryMonomial_eq_zero_of_degree_ne _ _ _ _ h

/-- The established entry bound in a literal-list presentation. -/
theorem norm_listMonomial_integral_le {N P : ℕ} (L R : List (Entry N))
    (hbal : L.length=R.length) (hP : L.length ≤ P)
    (hN : 16*(P:ℝ)^4 ≤ N+1) :
    ‖∫ U : LocalUnitary N, listMonomial L R U ∂haar N‖ ≤
      (2/(N+1:ℝ)^L.length) * (P:ℝ)^(highMultiplicityOccurrences (L++R)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(singletonEdges (L++R)).card := by
  induction L using List.ofFnRec with
  | h p f =>
    induction R using List.ofFnRec with
    | h q g =>
      simp only [List.length_ofFn] at hbal hP ⊢
      subst q
      have h := norm_entry_moment_le_uniform hP hN
        (fun a => (f a).1) (fun a => (f a).2)
        (fun a => (g a).1) (fun a => (g a).2)
      simpa only [listMonomial, entryProduct, List.map_ofFn, List.prod_ofFn,
        star_prod, HaarMixedMoments.entryMonomial, entryList, Function.comp_apply,
        Prod.mk.eta] using h

/-- The actual path integral vanishes if either generator has unequal numbers
of ordinary and conjugated entries. -/
theorem integral_signedProduct_eq_zero_of_unbalanced {N : ℕ}
    (L : List (SignedEntry N)) (a : Fin 2)
    (h : (selected (a,true) L).length ≠ (selected (a,false) L).length) :
    (∫ U : LocalUnitary N × LocalUnitary N, signedProduct L U ∂(haar N).prod (haar N))=0 := by
  simp_rw [signedProduct_eq]
  rw [integral_prod_mul]
  fin_cases a
  · change (selected (0,true) L).length ≠ (selected (0,false) L).length at h
    rw [integral_listMonomial_eq_zero_of_length_ne _ _ h, zero_mul]
  · change (selected (1,true) L).length ≠ (selected (1,false) L).length at h
    rw [integral_listMonomial_eq_zero_of_length_ne _ _ h, mul_zero]

def familyList {N : ℕ} (a : Fin 2) (L : List (SignedEntry N)) : List (Entry N) :=
  selected (a,true) L ++ selected (a,false) L

def edgeList {N : ℕ} (L : List (SignedEntry N)) : List (HaarPathGraph.Edge (Fin (N+1)) 2) :=
  L.map (fun e => (e.2.1,e.1.1,e.2.2))

/-- The unsigned colored edge multiplicity is exactly its positive plus
negative entry multiplicity in the corresponding Haar family. -/
theorem count_edgeList {N : ℕ} (L : List (SignedEntry N))
    (x y : Fin (N+1)) (a : Fin 2) :
    (edgeList L).count (x,a,y) = (familyList a L).count (x,y) := by
  simp only [familyList, List.count_append]
  induction L with
  | nil => simp [edgeList, selected]
  | cons e L ih =>
    obtain ⟨⟨b,c⟩,u,v⟩ := e
    cases c <;> by_cases hba : b=a <;> by_cases hx : u=x <;> by_cases hy : v=y <;>
      simp_all [edgeList, selected] <;> omega

/-- Singleton counting can equivalently be performed over the full finite
edge alphabet; absent edges make zero contribution. -/
theorem singleton_card_eq_sum {E : Type*} [Fintype E] [DecidableEq E] (L : List E) :
    (singletonEdges L).card = ∑ e : E, if L.count e=1 then 1 else 0 := by
  rw [singletonEdges, Finset.card_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  have hz : L.count e=0 := List.count_eq_zero.mpr
    (fun h => he (List.mem_toFinset.mpr h))
  simp [hz]

/-- Different Haar families have disjoint colored edges. -/
theorem singleton_card_edgeList {N : ℕ} (L : List (SignedEntry N)) :
    (singletonEdges (edgeList L)).card =
      (singletonEdges (familyList 0 L)).card + (singletonEdges (familyList 1 L)).card := by
  simp only [singleton_card_eq_sum, Fintype.sum_prod_type,
    Fin.sum_univ_two, Finset.sum_add_distrib]
  simp_rw [count_edgeList (N := N) L]

/-- Fourth-and-higher multiplicities split exactly across independent colors. -/
theorem highMultiplicity_edgeList {N : ℕ} (L : List (SignedEntry N)) :
    highMultiplicityOccurrences (edgeList L) =
      highMultiplicityOccurrences (familyList 0 L) +
        highMultiplicityOccurrences (familyList 1 L) := by
  simp only [← HaarMatchingSharp.sum_high_multiplicity, Fintype.sum_prod_type,
    Fin.sum_univ_two, Finset.sum_add_distrib]
  simp_rw [count_edgeList (N := N) L]

/-- Splitting a literal word into the four signed colors preserves its length. -/
theorem selected_lengths {N : ℕ} (L : List (SignedEntry N)) :
    (selected (0,true) L).length + (selected (0,false) L).length +
      (selected (1,true) L).length + (selected (1,false) L).length = L.length := by
  induction L with
  | nil => simp [selected]
  | cons e L ih =>
    obtain ⟨⟨a,b⟩,x⟩ := e
    fin_cases a <;> cases b <;>
      simp [selected] at ih ⊢ <;> omega

/-- A singleton-sensitive estimate for the actual product of entries in an
arbitrarily ordered balanced word; no matching enumeration is assumed. -/
theorem norm_signedProduct_integral_le {N P : ℕ} (L : List (SignedEntry N))
    (hP : 1 ≤ P) (hbal : ∀ a : Fin 2,
      (selected (a,true) L).length=(selected (a,false) L).length)
    (hlen : L.length ≤ 2*P) (hN : 16*(P:ℝ)^4 ≤ N+1) :
    ‖∫ U : LocalUnitary N × LocalUnitary N, signedProduct L U ∂(haar N).prod (haar N)‖ ≤
      (4/(N+1:ℝ)^(L.length/2)) * (P:ℝ)^(highMultiplicityOccurrences (edgeList L)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(singletonEdges (edgeList L)).card := by
  have hs := selected_lengths L
  have hb0 := hbal 0
  have hb1 := hbal 1
  have h0P : (selected (0,true) L).length ≤ P := by omega
  have h1P : (selected (1,true) L).length ≤ P := by omega
  have hdeg : (selected (0,true) L).length + (selected (1,true) L).length=L.length/2 := by omega
  have h0 := norm_listMonomial_integral_le _ _ hb0 h0P hN
  have h1 := norm_listMonomial_integral_le _ _ hb1 h1P hN
  simp_rw [signedProduct_eq]
  rw [integral_prod_mul, norm_mul]
  apply (mul_le_mul h0 h1 (norm_nonneg _) (by positivity)).trans
  have heq :
      (2/(N+1:ℝ)^(selected (0,true) L).length *
        (P:ℝ)^(highMultiplicityOccurrences (familyList 0 L)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(singletonEdges (familyList 0 L)).card) *
      (2/(N+1:ℝ)^(selected (1,true) L).length *
        (P:ℝ)^(highMultiplicityOccurrences (familyList 1 L)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(singletonEdges (familyList 1 L)).card) =
      (4/(N+1:ℝ)^(L.length/2)) *
        (P:ℝ)^(highMultiplicityOccurrences (familyList 0 L)/2+
          highMultiplicityOccurrences (familyList 1 L)/2) *
        (2*(P:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(singletonEdges (edgeList L)).card := by
    rw [singleton_card_edgeList, ←hdeg]
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [familyList] at heq
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_right₀ (by exact_mod_cast hP)
  rw [highMultiplicity_edgeList]
  simp only [familyList]
  omega

/-- The oriented entries of a literal path, with negative letters represented
by conjugated entries in the reverse direction. -/
def pathEntries {N m : ℕ} (P : HaarPathGraph.Path (Fin (N+1)) 2 m) : List (SignedEntry N) :=
  List.ofFn fun i => (P.colors i, if (P.colors i).2 then
    (P.vertex i.castSucc,P.vertex i.succ) else (P.vertex i.succ,P.vertex i.castSucc))

def pathProduct {N m : ℕ} (P : HaarPathGraph.Path (Fin (N+1)) 2 m)
    (U : LocalUnitary N × LocalUnitary N) : ℂ :=
  ∏ i : Fin m, (if (P.colors i).2 then
    ((if (P.colors i).1=0 then U.1 else U.2) : Mat N) else
    ((if (P.colors i).1=0 then U.1 else U.2) : Mat N)ᴴ)
      (P.vertex i.castSucc) (P.vertex i.succ)

@[simp] theorem pathEntries_length {N m : ℕ} (P : HaarPathGraph.Path (Fin (N+1)) 2 m) :
    (pathEntries P).length=m := by simp [pathEntries]

/-- The edge list used by the graph defect is the literal entry list used by
Weingarten integration; loops and parallel colors retain their multiplicities. -/
@[simp] theorem edgeList_pathEntries {N m : ℕ} (P : HaarPathGraph.Path (Fin (N+1)) 2 m) :
    edgeList (pathEntries P)=P.edgeList := by
  simp only [edgeList, pathEntries, List.map_ofFn, HaarPathGraph.Path.edgeList]
  congr 1
  funext i
  cases hb : (P.colors i).2 <;> simp [HaarPathGraph.edge, hb]

/-- The matrix-entry product of the path is exactly the signed scalar product. -/
theorem pathProduct_eq {N m : ℕ} (P : HaarPathGraph.Path (Fin (N+1)) 2 m)
    (U : LocalUnitary N × LocalUnitary N) :
    pathProduct P U=signedProduct (pathEntries P) U := by
  simp only [pathProduct, signedProduct, pathEntries, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  cases hb : (P.colors i).2 <;> simp [hb, Matrix.conjTranspose_apply]

/-- The probabilistic BC path weight estimate for the actual pair of independent
Haar matrices. The graph defect and singleton count are computed from `P`.
The prefactor `4` improves the published `25/4`; no probabilistic input remains. -/
theorem norm_pathProduct_integral_le {N m : ℕ}
    (P : HaarPathGraph.Path (Fin (N+1)) 2 m) (hm : 0 < m)
    (hN : 16*((m/2:ℕ):ℝ)^4 ≤ N+1) :
    ‖∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N)‖ ≤
      (4/(N+1:ℝ)^(m/2)) * (m:ℝ)^P.defectTwice *
        ((m:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(singletonEdges P.edgeList).card := by
  by_cases hbal : ∀ a : Fin 2,
      (selected (a,true) (pathEntries P)).length=(selected (a,false) (pathEntries P)).length
  · have hs := selected_lengths (pathEntries P)
    have hb0 := hbal 0
    have hb1 := hbal 1
    rw [pathEntries_length] at hs
    have hhalf : 1 ≤ m/2 := by omega
    have hlen : (pathEntries P).length ≤ 2*(m/2) := by rw [pathEntries_length]; omega
    have h := norm_signedProduct_integral_le (pathEntries P) hhalf hbal hlen hN
    simp only [pathEntries_length, edgeList_pathEntries] at h
    simp_rw [pathProduct_eq]
    apply h.trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hhigh := P.highMultiplicityOccurrences_le_twice_defect
      calc
        ((m/2:ℕ):ℝ)^(highMultiplicityOccurrences P.edgeList/2) ≤
            (m:ℝ)^(highMultiplicityOccurrences P.edgeList/2) := by
          gcongr
          exact_mod_cast (Nat.div_le_self m 2)
        _ ≤ (m:ℝ)^P.defectTwice := by
          apply pow_le_pow_right₀ (by exact_mod_cast hm)
          omega
    · apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (by omega : 2*(m/2) ≤ m)
    · positivity
    · positivity
  · push_neg at hbal
    obtain ⟨a,ha⟩ := hbal
    simp_rw [pathProduct_eq]
    rw [integral_signedProduct_eq_zero_of_unbalanced _ a ha, norm_zero]
    positivity

end Nonadditivity.HaarPathWeights
