/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.Net
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat

/-! # Sharp finite-dimensional nets

The cardinality estimate is proved by comparing disjoint Haar-measurable
balls. Maximality is taken among symmetric separated sets, so imposing
negation symmetry does not double the volume bound.
-/

noncomputable section

namespace Nonadditivity.QuantitativeNet

open Metric MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The usual packing bound, with its exact radius and dimension. -/
theorem card_le_of_separated (s : Finset E) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) :
    (s.card : ℝ) ≤ (1 + 2 * R / δ) ^ finrank ℝ E := by
  classical
  borelize E
  let μ : Measure E := Measure.addHaar
  let r : ℝ := δ / 2
  let ρ : ℝ := R + δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let A : Set E := ⋃ x ∈ s, ball x r
  have hdisj : Set.Pairwise (s : Set E) (fun x y => Disjoint (ball x r) (ball y r)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    calc
      r + r = δ := by dsimp [r]; ring
      _ ≤ dist x y := hsep x hx y hy hxy
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine Set.iUnion₂_subset fun x hx => ball_subset_ball' ?_
    change r + dist x 0 ≤ ρ
    rw [dist_zero_right]
    dsimp [r, ρ]
    linarith [hs x hx]
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [show A = ⋃ x ∈ s, ball x r from rfl,
          measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hcancel : (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvol
  have hreal : (s.card : ℝ) * r ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
  have hratio : ρ / r = 1 + 2 * R / δ := by
    dsimp [ρ, r]
    field_simp
    ring
  calc
    (s.card : ℝ) ≤ ρ ^ finrank ℝ E / r ^ finrank ℝ E :=
      (le_div_iff₀ (pow_pos hr _)).mpr hreal
    _ = (1 + 2 * R / δ) ^ finrank ℝ E := by rw [← div_pow, hratio]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Strict separation permits adding a point outside all closed net balls. -/
private theorem separated_insert [DecidableEq E] {s : Finset E} {δ : ℝ} {x : E}
    (hs : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → δ < dist y z)
    (hx : ∀ y ∈ s, δ < dist x y) :
    ∀ y ∈ insert x s, ∀ z ∈ insert x s, y ≠ z → δ < dist y z := by
  classical
  intro y hy z hz hyz
  rcases Finset.mem_insert.mp hy with rfl | hys
  · rcases Finset.mem_insert.mp hz with rfl | hzs
    · exact (hyz rfl).elim
    · exact hx z hzs
  · rcases Finset.mem_insert.mp hz with rfl | hzs
    · simpa only [dist_comm] using hx y hys
    · exact hs y hys z hzs hyz

/-- A symmetric separated seed extends to a symmetric unit-sphere net,
without increasing the sharp packing bound. -/
theorem exists_symmetric_unitSphereNet_containing (seeds : Finset E) {δ : ℝ}
    (hδ : 0 < δ) (hδtwo : δ < 2)
    (hseed_norm : ∀ x ∈ seeds, ‖x‖ = 1)
    (hseed_neg : ∀ x ∈ seeds, -x ∈ seeds)
    (hseed_sep : ∀ x ∈ seeds, ∀ y ∈ seeds, x ≠ y → δ < dist x y) :
    ∃ tests : Finset E, seeds ⊆ tests ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      (∀ x ∈ tests, ∀ y ∈ tests, x ≠ y → δ < dist x y) ∧
      UnitSphereNet tests δ ∧
      (tests.card : ℝ) ≤ (1 + 2 / δ) ^ finrank ℝ E := by
  classical
  let admissible : Finset E → Prop := fun s => seeds ⊆ s ∧
    (∀ x ∈ s, ‖x‖ = 1) ∧ (∀ x ∈ s, -x ∈ s) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ < dist x y)
  have hcard (s : Finset E) (hs : admissible s) :
      (s.card : ℝ) ≤ (1 + 2 / δ) ^ finrank ℝ E := by
    simpa only [mul_one] using card_le_of_separated s hδ (by norm_num : (0 : ℝ) ≤ 1)
      (fun x hx => (hs.2.1 x hx).le) (fun x hx y hy hxy => (hs.2.2.2 x hx y hy hxy).le)
  let cards : Set ℕ := {m | ∃ s : Finset E, admissible s ∧ s.card = m}
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + 2 / δ) ^ finrank ℝ E)
  have hcards_finite : cards.Finite := by
    apply (Set.finite_Iic N).subset
    rintro m ⟨s, hs, rfl⟩
    exact (Nat.cast_lt.mp ((hcard s hs).trans_lt hN)).le
  have hcards_nonempty : cards.Nonempty :=
    ⟨seeds.card, seeds, ⟨Finset.Subset.refl seeds, hseed_norm, hseed_neg, hseed_sep⟩, rfl⟩
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image cards id hcards_finite hcards_nonempty
  obtain ⟨s, hs, hsm⟩ := hm
  have hnet : UnitSphereNet s δ := by
    intro x hx
    by_contra hnot
    have hfar : ∀ y ∈ s, δ < dist x y := by
      intro y hy
      exact lt_of_not_ge (fun hxy => hnot ⟨y, hy, hxy⟩)
    have hxnot : x ∉ s := by
      intro hxs
      have := hfar x hxs
      rw [dist_self] at this
      exact (not_lt_of_ge hδ.le) this
    have hnormneg : ‖-x‖ = 1 := by simpa only [norm_neg]
    have hfarneg : ∀ y ∈ s, δ < dist (-x) y := by
      intro y hy
      simpa only [← dist_neg_neg (-x) y, neg_neg] using hfar (-y) (hs.2.2.1 y hy)
    have hdistneg : dist x (-x) = 2 := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_two, hx]
      ring
    let t : Finset E := insert x (insert (-x) s)
    have hst : s ⊆ t := fun y hy => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)
    have ht : admissible t := by
      refine ⟨hs.1.trans hst, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hnormneg
        · exact hs.2.1 y hy
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa only [neg_neg] using Finset.mem_insert_self x (insert (-x) s)
        · exact hst (hs.2.2.1 y hy)
      · apply separated_insert (separated_insert hs.2.2.2 hfarneg)
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa only [hdistneg] using hδtwo
        · exact hfar y hy
    have hmax' : t.card ≤ s.card := by
      have := hmax t.card ⟨t, ht, rfl⟩
      simpa only [id_eq, ← hsm] using this
    have hstrict : s.card < t.card := by
      calc
        s.card < (insert x s).card := by rw [Finset.card_insert_of_notMem hxnot]; omega
        _ ≤ t.card := Finset.card_le_card (by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_insert_self _ _
          · exact hst hy)
    exact (not_lt_of_ge hmax') hstrict
  exact ⟨s, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hnet, hcard s hs⟩

/-- The prescribed test and its negative can be included without any
cardinality overhead. -/
theorem exists_symmetric_unitSphereNet_with_test (a : E) (ha : ‖a‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδtwo : δ < 2) :
    ∃ tests : Finset E, a ∈ tests ∧ -a ∈ tests ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      (∀ x ∈ tests, ∀ y ∈ tests, x ≠ y → δ < dist x y) ∧
      UnitSphereNet tests δ ∧
      (tests.card : ℝ) ≤ (1 + 2 / δ) ^ finrank ℝ E := by
  classical
  have hd : dist a (-a) = 2 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul, Real.norm_two, ha]
    ring
  have hn : ∀ x ∈ ({a, -a} : Finset E), ‖x‖ = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa only [norm_neg] using ha
  have hneg : ∀ x ∈ ({a, -a} : Finset E), -x ∈ ({a, -a} : Finset E) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg a)
  have hsep : ∀ x ∈ ({a, -a} : Finset E), ∀ y ∈ ({a, -a} : Finset E),
      x ≠ y → δ < dist x y := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · simpa only [hd] using hδtwo
    · rw [dist_comm, hd]
      exact hδtwo
    · exact (hxy rfl).elim
  obtain ⟨tests, hmem, htests⟩ :=
    exists_symmetric_unitSphereNet_containing {a, -a} hδ hδtwo hn hneg hsep
  exact ⟨tests, hmem (by simp), hmem (by simp), htests⟩

/-- Exact appendix net bound at radius `1/n`. -/
theorem exists_symmetric_inverse_nat_net (a : E) (ha : ‖a‖ = 1)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ tests : Finset E, a ∈ tests ∧ -a ∈ tests ∧
      (∀ x ∈ tests, ‖x‖ = 1) ∧ (∀ x ∈ tests, -x ∈ tests) ∧
      (∀ x ∈ tests, ∀ y ∈ tests, x ≠ y → 1 / (n : ℝ) < dist x y) ∧
      UnitSphereNet tests (1 / (n : ℝ)) ∧
      (tests.card : ℝ) ≤ (1 + 2 * (n : ℝ)) ^ finrank ℝ E := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hδ : 0 < 1 / (n : ℝ) := by positivity
  have hδtwo : 1 / (n : ℝ) < 2 := by
    apply (div_lt_iff₀ hn0).mpr
    linarith
  obtain ⟨tests, ha, hneg, hnorm, hsymm, hsep, hnet, hcard⟩ :=
    exists_symmetric_unitSphereNet_with_test a ha hδ hδtwo
  refine ⟨tests, ha, hneg, hnorm, hsymm, hsep, hnet, ?_⟩
  simpa only [div_eq_mul_inv, one_mul, inv_inv] using hcard

end Nonadditivity.QuantitativeNet
