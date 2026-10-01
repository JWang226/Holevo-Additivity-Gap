/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarSharpCounting
import Nonadditivity.HaarSharpConstants
import Nonadditivity.HaarSharpPathWeight

/-! Weighted chronological counts recover the original dimension range. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarSharpSummation
open HaarPathClasses HaarOperatorPathBridge HaarMomentConstants
open scoped BigOperators

def countMajorant (p : ℕ) (e r : ℕ) : ℝ :=
  (1+64/(p:ℝ))^p * (4*(p:ℝ)^2)^(3*(e+2*r)+4) * ((p:ℝ)^3)^(e+2*r+2)

theorem countMajorant_nonneg (p e r : ℕ) : 0 ≤ countMajorant p e r := by
  unfold countMajorant; positivity

theorem card_fibre_le {N p t : ℕ} (hp : 2≤p) (ht : 0<t) (htp : t≤p) (e r : ℕ) :
    (((activeRefinedClasses N t).filter (fun C =>
      refinedSingletonCount C=e ∧ refinedVertexDeficit C=r)).card:ℝ) ≤
      countMajorant p e r := by
  classical
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have htpR : (t:ℝ)≤p := by exact_mod_cast htp
  have hz : 1/(p:ℝ)^3≤1 := by
    apply (div_le_iff₀ (by positivity)).2
    simpa using one_le_pow₀ hp1
  have h := card_refined_subfamily_weighted_le ht (e+2*r)
    ((activeRefinedClasses N t).filter (fun C =>
      refinedSingletonCount C=e ∧ refinedVertexDeficit C=r))
    (by
      intro C hC
      obtain ⟨hC,he,hr⟩ := Finset.mem_filter.mp hC
      rw [active_refined_defect_identity ht hC,he,hr])
    (by positivity : 0≤1/(p:ℝ)^3) hz
  have hb : 1+64*(t:ℝ)^2*(1/(p:ℝ)^3) ≤ 1+64/(p:ℝ) := by
    calc
      _ ≤ 1+64*(p:ℝ)^2*(1/(p:ℝ)^3) := by gcongr
      _ = _ := by field_simp
  have hf : (1+64*(t:ℝ)^2*(1/(p:ℝ)^3))^t ≤ (1+64/(p:ℝ))^p :=
    (pow_le_pow_left₀ (by positivity) hb t).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) htp)
  have hu := h.trans (mul_le_mul hf
    (pow_le_pow_left₀ (by positivity) (by gcongr : 4*(t:ℝ)^2≤4*(p:ℝ)^2) _)
    (by positivity) (by positivity))
  simp only [one_div_pow, mul_one_div] at hu
  exact (div_le_iff₀ (by positivity)).mp hu

theorem weight_mono {N p t : ℝ} (hN : 0≤N) (hp : 0≤p) (ht : 0≤t) (htp : t≤p)
    (e r : ℕ) : refinedClassWeightMajorant p N t e r ≤
      refinedClassWeightMajorant p N p e r := by
  unfold refinedClassWeightMajorant
  gcongr

theorem product_eq (p : ℕ) (N : ℝ) (e r : ℕ) :
    countMajorant p e r * refinedClassWeightMajorant p N p e r =
      (1024*(p:ℝ)^25/N*(1+64/(p:ℝ))^p) *
        (alpha p N)^e * (beta p N)^r := by
  unfold countMajorant refinedClassWeightMajorant alpha beta
  have h3 : 3*(e+2*r)+4=e*3+r*6+4 := by omega
  have h9 : 9*(e+2*r)+11=e*9+r*18+11 := by omega
  rw [h3,h9, show (128:ℝ)=2*4^3 by norm_num,
    show (4096:ℝ)=4^6 by norm_num]
  simp only [pow_add,pow_mul,mul_pow,div_pow,pow_succ]
  ring

theorem sum_products_le {p : ℕ} {N : ℝ} (hp : 2≤p)
    (hN : 2^32*(p:ℝ)^80≤N) (a b : ℕ) :
    (∑ e ∈ Finset.range a, ∑ r ∈ Finset.range b,
      countMajorant p e r * refinedClassWeightMajorant p N p e r) ≤
        4096*(p:ℝ)^25/N*(1+64/(p:ℝ))^p := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hN0 := dimension_pos hpR hN
  have ha := alpha_bounds hpR hN
  have hb := beta_bounds hpR hN
  simp_rw [product_eq]
  have heq : (∑ e ∈ Finset.range a, ∑ r ∈ Finset.range b,
      1024*(p:ℝ)^25/N*(1+64/(p:ℝ))^p * (alpha p N)^e * (beta p N)^r) =
      (1024*(p:ℝ)^25/N*(1+64/(p:ℝ))^p) *
        (∑ e ∈ Finset.range a, (alpha p N)^e) *
        (∑ r ∈ Finset.range b, (beta p N)^r) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [heq]
  have hsumA := geometric_sum_bound ha.1 ha.2 a
  have hsumB := geometric_sum_bound hb.1 hb.2 b
  calc
    _ ≤ (1024*(p:ℝ)^25/N*(1+64/(p:ℝ))^p)*2*2 := by
      gcongr
      exact Finset.sum_nonneg (fun r _ => pow_nonneg hb.1 r)
    _ = _ := by ring



theorem sum_active_weights_le {N p t : ℕ} (hp : 2≤p) (ht : 0<t) (htp : t≤p)
    (hN : 2^32*(p:ℝ)^80≤N+1) :
    (∑ C ∈ activeRefinedClasses N t,
      refinedClassWeightMajorant p (N+1) t (refinedSingletonCount C) (refinedVertexDeficit C)) ≤
        4096*(p:ℝ)^25/(N+1)*(1+64/(p:ℝ))^p := by
  classical
  let s := activeRefinedClasses N t
  have hm : ∀ C ∈ s, (refinedSingletonCount C,refinedVertexDeficit C) ∈
      (Finset.range (p+1)).product (Finset.range (p+1)) := by
    intro C hC
    have he := refinedSingletonCount_le C
    have hr := refinedVertexDeficit_le C
    have hh := Nat.div_le_self t 2
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
  calc
    _ ≤ ∑ C ∈ s, refinedClassWeightMajorant p (N+1) p
        (refinedSingletonCount C) (refinedVertexDeficit C) := by
      apply Finset.sum_le_sum
      intro C _
      exact weight_mono (by positivity) (by positivity) (by positivity) (by exact_mod_cast htp) _ _
    _ = ∑ e ∈ Finset.range (p+1), ∑ r ∈ Finset.range (p+1),
        ((s.filter (fun C => refinedSingletonCount C=e ∧ refinedVertexDeficit C=r)).card:ℝ) *
          refinedClassWeightMajorant p (N+1) p e r := by
      have hh := Finset.sum_fiberwise_of_maps_to' hm
        (fun q : ℕ × ℕ => refinedClassWeightMajorant p (N+1) p q.1 q.2)
      rw [Finset.product_eq_sprod, Finset.sum_product] at hh
      simpa only [Finset.sum_product, Prod.mk.injEq, Finset.sum_const,nsmul_eq_mul] using hh.symm
    _ ≤ ∑ e ∈ Finset.range (p+1), ∑ r ∈ Finset.range (p+1),
        countMajorant p e r * refinedClassWeightMajorant p (N+1) p e r := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right (card_fibre_le hp ht htp e r)
        (refinedClassWeightMajorant_nonneg (by positivity) (by positivity) (by positivity) e r)
    _ ≤ _ := sum_products_le hp hN _ _

end Nonadditivity.HaarSharpSummation
