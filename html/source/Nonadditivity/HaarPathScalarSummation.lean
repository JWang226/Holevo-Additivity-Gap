/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarEncodingSlack

/-! # Scalar summation of the corrected two-generator path bounds

The input bounds retain their literal combinatorial factors: the coarse
class count, refinement count, coefficient cost, and Haar entry cost.
Their finite sum is bounded by the tracked prescribed-dimension majorant.
No path counting or operator estimate is postulated by this module.
-/
noncomputable section
namespace Nonadditivity.HaarMomentConstants
open scoped BigOperators

/-- Coarse classes times refinements at singleton count `e` and vertex
deficit `r`; the graph defect is exactly `e + 2*r`. -/
def refinedClassCountMajorant (t : ℝ) (e r : ℕ) : ℝ :=
  128^(e+2*r+2) * t^(3*(e+2*r)+6) * (4*t^2)^(3*(e+2*r)+4)

/-- The normalized entry bound times the grouped coefficient bound after
the `N^v` vertex-label count cancels `N^(t/2)`. -/
def refinedClassWeightMajorant (p N t : ℝ) (e r : ℕ) : ℝ :=
  (4/N^(r+1))*t^(e+2*r)*(t/N^(1/4:ℝ))^e * 2^e*p^(9*(e+2*r)+11)

def localEncodingAlpha (p N t : ℝ) : ℝ :=
  16384*t^11*p^9/N^(1/4:ℝ)

def localEncodingBeta (p N t : ℝ) : ℝ :=
  67108864*t^20*p^18/N

theorem refinedClassCountMajorant_nonneg {t : ℝ} (ht : 0 ≤ t) (e r : ℕ) :
    0 ≤ refinedClassCountMajorant t e r := by
  unfold refinedClassCountMajorant
  positivity

theorem refinedClassWeightMajorant_nonneg {p N t : ℝ}
    (hp : 0 ≤ p) (hN : 0 ≤ N) (ht : 0 ≤ t) (e r : ℕ) :
    0 ≤ refinedClassWeightMajorant p N t e r := by
  unfold refinedClassWeightMajorant
  positivity

/-- Exact collection of all constants and all powers, including the
corrected extra factor `128` per important event. -/
theorem refinedClass_product_eq (p N t : ℝ) (e r : ℕ) :
    refinedClassCountMajorant t e r * refinedClassWeightMajorant p N t e r =
      (4*16384*256*t^14*p^11/N) *
        localEncodingAlpha p N t ^ e * localEncodingBeta p N t ^ r := by
  unfold refinedClassCountMajorant refinedClassWeightMajorant
    localEncodingAlpha localEncodingBeta
  have h3 : 3*(e+2*r)+6=e*3+r*6+6 := by omega
  have h4 : 3*(e+2*r)+4=e*3+r*6+4 := by omega
  have h9 : 9*(e+2*r)+11=e*9+r*18+11 := by omega
  rw [h3,h4,h9]
  rw [show (16384:ℝ)=128*4^3*2 by norm_num,
    show (67108864:ℝ)=128^2*4^6 by norm_num]
  simp only [pow_add, pow_mul, mul_pow, div_pow, pow_succ]
  ring

theorem localEncodingAlpha_le {p N t : ℝ} (hp : 0 ≤ p)
    (hN : 0 ≤ N) (ht0 : 0 ≤ t) (ht : t ≤ p) :
    localEncodingAlpha p N t ≤ 128*alpha p N := by
  have h := mul_le_mul_of_nonneg_left (local_alpha_le hp hN ht0 ht)
    (by norm_num : (0:ℝ) ≤ 128)
  unfold localEncodingAlpha
  convert h using 1 <;> ring

theorem localEncodingBeta_le {p N t : ℝ}
    (hN : 0 ≤ N) (ht0 : 0 ≤ t) (ht : t ≤ p) :
    localEncodingBeta p N t ≤ 16384*beta p N := by
  have h := mul_le_mul_of_nonneg_left (local_beta_le hN ht0 ht)
    (by norm_num : (0:ℝ) ≤ 16384)
  unfold localEncodingBeta
  convert h using 1 <;> ring

/-- A single pair of graph statistics contributes one term of the two
finite geometric sums in the encoding majorant. -/
theorem refinedClass_product_le {p N t : ℝ}
    (hp : 0 ≤ p) (hN : 0 < N) (ht1 : 1 ≤ t) (ht : t ≤ p) (e r : ℕ) :
    refinedClassCountMajorant t e r * refinedClassWeightMajorant p N t e r ≤
      (16384*t^3*((25/4)*(4*t^3)^4*p^11/N*
        Real.exp (t^2/N^(1/4:ℝ)))) *
        (128*alpha p N)^e*(16384*beta p N)^r := by
  have ht0 : 0 ≤ t := by linarith
  have ha0 : 0 ≤ localEncodingAlpha p N t := by
    unfold localEncodingAlpha
    positivity
  have hb0 : 0 ≤ localEncodingBeta p N t := by
    unfold localEncodingBeta
    positivity
  have ht14 : t^14 ≤ t^15 := pow_le_pow_right₀ ht1 (by norm_num)
  have he : 1 ≤ Real.exp (t^2/N^(1/4:ℝ)) := Real.one_le_exp (by positivity)
  have hbase : 4*16384*256*t^14*p^11/N ≤
      16384*t^3*((25/4)*(4*t^3)^4*p^11/N*
        Real.exp (t^2/N^(1/4:ℝ))) := by
    calc
      _ ≤ (25/4)*16384*256*t^15*p^11/N*Real.exp (t^2/N^(1/4:ℝ)) := by
        calc
          _ ≤ (25/4)*16384*256*t^15*p^11/N := by gcongr <;> norm_num
          _ ≤ _ := le_mul_of_one_le_right (by positivity) he
      _ = _ := by ring
  rw [refinedClass_product_eq]
  have ha' : 0 ≤ 128*alpha p N := by unfold alpha; positivity
  exact mul_le_mul
    (mul_le_mul hbase (pow_le_pow_left₀ ha0 (localEncodingAlpha_le hp hN.le ht0 ht) e)
      (pow_nonneg ha0 e) (by positivity))
    (pow_le_pow_left₀ hb0 (localEncodingBeta_le hN.le ht0 ht) r)
    (pow_nonneg hb0 r) (by positivity)

/-- Summing every admissible singleton/vertex-deficit pair yields exactly
the finite majorant required by the later error estimate. -/
theorem sum_refinedClass_products_le {p N t : ℝ}
    (hp : 0 ≤ p) (hN : 0 < N) (ht1 : 1 ≤ t) (ht : t ≤ p) (a b : ℕ) :
    (∑ e ∈ Finset.range a, ∑ r ∈ Finset.range b,
      refinedClassCountMajorant t e r * refinedClassWeightMajorant p N t e r) ≤
        encodingMajorant p N t a b := by
  calc
    _ ≤ ∑ e ∈ Finset.range a, ∑ r ∈ Finset.range b,
        (16384*t^3*((25/4)*(4*t^3)^4*p^11/N*
          Real.exp (t^2/N^(1/4:ℝ)))) *
          (128*alpha p N)^e*(16384*beta p N)^r := by
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun r _ =>
        refinedClass_product_le hp hN ht1 ht e r
    _ = _ := by
      simp only [encodingMajorant, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Finite classes may be indexed by any concrete type. Their actual
singleton and vertex-deficit fibres supply the counting hypotheses. -/
theorem sum_class_weights_le_encodingMajorant {C : Type*} [DecidableEq C]
    (s : Finset C) (singleton deficit : C → ℕ) (weight : C → ℝ)
    {p N t : ℝ} (hp : 0 ≤ p) (hN : 0 < N) (ht1 : 1 ≤ t) (ht : t ≤ p)
    (a b : ℕ)
    (hstats : ∀ c ∈ s, singleton c < a ∧ deficit c < b)
    (hcard : ∀ e ∈ Finset.range a, ∀ r ∈ Finset.range b,
      ((s.filter (fun c => singleton c=e ∧ deficit c=r)).card:ℝ) ≤
        refinedClassCountMajorant t e r)
    (hweight : ∀ c ∈ s, weight c ≤
      refinedClassWeightMajorant p N t (singleton c) (deficit c)) :
    (∑ c ∈ s, weight c) ≤ encodingMajorant p N t a b := by
  classical
  have hm : ∀ c ∈ s, (singleton c,deficit c) ∈
      (Finset.range a).product (Finset.range b) := by
    intro c hc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hstats c hc).1, Finset.mem_range.mpr (hstats c hc).2⟩
  calc
    _ ≤ ∑ c ∈ s, refinedClassWeightMajorant p N t (singleton c) (deficit c) :=
      Finset.sum_le_sum hweight
    _ = ∑ e ∈ Finset.range a, ∑ r ∈ Finset.range b,
        ((s.filter (fun c => singleton c=e ∧ deficit c=r)).card:ℝ) *
          refinedClassWeightMajorant p N t e r := by
      have hh := Finset.sum_fiberwise_of_maps_to' hm
        (fun q : ℕ × ℕ => refinedClassWeightMajorant p N t q.1 q.2)
      rw [Finset.product_eq_sprod, Finset.sum_product] at hh
      simpa only [Finset.sum_product, Prod.mk.injEq, Finset.sum_const,
        nsmul_eq_mul] using hh.symm
    _ ≤ ∑ e ∈ Finset.range a, ∑ r ∈ Finset.range b,
        refinedClassCountMajorant t e r * refinedClassWeightMajorant p N t e r := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right (hcard e he r hr)
        (refinedClassWeightMajorant_nonneg hp hN.le (by linarith) e r)
    _ ≤ _ := sum_refinedClass_products_le hp hN ht1 ht a b

/-- The same finite class sum with the common polynomial norm factor. -/
theorem sum_class_weights_le_encodingMajorant_mul {C : Type*} [DecidableEq C]
    (s : Finset C) (singleton deficit : C → ℕ) (weight : C → ℝ)
    {p N t scale : ℝ} (hp : 0 ≤ p) (hN : 0 < N)
    (ht1 : 1 ≤ t) (ht : t ≤ p) (hscale : 0 ≤ scale) (a b : ℕ)
    (hstats : ∀ c ∈ s, singleton c < a ∧ deficit c < b)
    (hcard : ∀ e ∈ Finset.range a, ∀ r ∈ Finset.range b,
      ((s.filter (fun c => singleton c=e ∧ deficit c=r)).card:ℝ) ≤
        refinedClassCountMajorant t e r)
    (hweight : ∀ c ∈ s, weight c ≤
      refinedClassWeightMajorant p N t (singleton c) (deficit c)*scale) :
    (∑ c ∈ s, weight c) ≤ encodingMajorant p N t a b*scale := by
  calc
    _ ≤ ∑ c ∈ s,
        refinedClassWeightMajorant p N t (singleton c) (deficit c)*scale :=
      Finset.sum_le_sum hweight
    _ = (∑ c ∈ s, refinedClassWeightMajorant p N t (singleton c) (deficit c))*scale :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_class_weights_le_encodingMajorant s singleton deficit _ hp hN ht1 ht a b
        hstats hcard (fun _ _ => le_rfl)) hscale

/-- Operator-valued grouped class sums use exactly the same scalar bound. -/
theorem norm_sum_classes_le_encodingMajorant {C E : Type*} [DecidableEq C]
    [NormedAddCommGroup E] (s : Finset C) (singleton deficit : C → ℕ) (term : C → E)
    {p N t scale : ℝ} (hp : 0 ≤ p) (hN : 0 < N)
    (ht1 : 1 ≤ t) (ht : t ≤ p) (hscale : 0 ≤ scale) (a b : ℕ)
    (hstats : ∀ c ∈ s, singleton c < a ∧ deficit c < b)
    (hcard : ∀ e ∈ Finset.range a, ∀ r ∈ Finset.range b,
      ((s.filter (fun c => singleton c=e ∧ deficit c=r)).card:ℝ) ≤
        refinedClassCountMajorant t e r)
    (hterm : ∀ c ∈ s, ‖term c‖ ≤
      refinedClassWeightMajorant p N t (singleton c) (deficit c)*scale) :
    ‖∑ c ∈ s, term c‖ ≤ encodingMajorant p N t a b*scale := by
  exact (norm_sum_le s term).trans
    (sum_class_weights_le_encodingMajorant_mul s singleton deficit (fun c => ‖term c‖)
      hp hN ht1 ht hscale a b hstats hcard hterm)

/-- The trace normalization and vertex-label count leave precisely one
dimension denominator for each deficit and one for the normalized trace. -/
theorem vertex_dimension_cancellation {N : ℝ} (hN : N ≠ 0) (v r : ℕ) :
    (N^v/N) * (4/N^(v+r)) = 4/N^(r+1) := by
  rw [pow_add, pow_succ]
  field_simp

theorem graph_defect_eq_singletons_add_twice_deficit
    {t v e r : ℕ} (hlen : t=2*(v+r)) :
    t+e-2*v=e+2*r := by omega

theorem even_length_deficit_identity {t v : ℕ} (ht : Even t) (hv : v ≤ t/2) :
    t=2*(v+(t/2-v)) := by
  obtain ⟨k,hk⟩ := ht
  omega

end Nonadditivity.HaarMomentConstants
