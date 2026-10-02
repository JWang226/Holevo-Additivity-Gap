/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarOperatorPathSum
import Nonadditivity.HaarPathScalarSummation

/-! # Actual Haar path weights under the original 2^32 dimension hypothesis -/
noncomputable section
namespace Nonadditivity.HaarSharpPathWeight
open HaarPathGraph HaarPathWeights HaarMomentConstants HaarOperatorPathBridge
open scoped BigOperators

theorem strong_path_moment_dimension {N p t : ℕ} (hp : 2≤p) (ht : t≤p)
    (hN : 2^32*(p:ℝ)^80 ≤ N+1) :
    16*((t/2:ℕ):ℝ)^4 ≤ N+1 := by
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  have ht' : ((t/2:ℕ):ℝ)≤p := by exact_mod_cast (Nat.div_le_self t 2).trans ht
  calc
    _ ≤ 16*(p:ℝ)^4 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) ht' 4) (by norm_num)
    _ ≤ 2^32*(p:ℝ)^80 := mul_le_mul (by norm_num)
      (pow_le_pow_right₀ hp1 (by norm_num)) (by positivity) (by norm_num)
    _ ≤ _ := hN

theorem norm_pathWeight_le {N p t : ℕ} (hp : 2≤p) (ht0 : 0<t) (ht : t≤p)
    (hN : 2^32*(p:ℝ)^80 ≤ N+1) (P : Path (Fin (N+1)) 2 t) :
    ‖pathWeight P‖ ≤
      (4/(N+1:ℝ)^(t/2))*(t:ℝ)^P.defectTwice *
        ((t:ℝ)/(N+1:ℝ)^(1/4:ℝ))^(HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  have h := norm_pathProduct_integral_le P ht0 (strong_path_moment_dimension hp ht hN)
  have hr : Real.sqrt (Real.sqrt (N+1:ℝ))=(N+1:ℝ)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity)]
    norm_num
  simpa only [pathWeight,hr] using h

theorem pathWeight_support {N t : ℕ} (P : Path (Fin (N+1)) 2 t)
    (hP : pathWeight P≠0) : Even t ∧ P.vertices.card≤t/2 := by
  have he := even_length_of_integral_ne_zero P hP
  exact ⟨he,P.vertices_le_half_of_balanced (locallyBalanced_of_integral_ne_zero P hP) he⟩

/-- Multiplying an actual Haar weight by its grouped coefficient budget
leaves exactly the scalar cost indexed by singletons and vertex deficit. -/
theorem normalized_pathWeight_smul_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N p t : ℕ} (hp : 2≤p) (ht0 : 0<t) (ht : t≤p)
    (hN : 2^32*(p:ℝ)^80 ≤ N+1) (P : Path (Fin (N+1)) 2 t)
    (hP : pathWeight P≠0) (B : E) {scale : ℝ} (_hs : 0≤scale)
    (hb : ‖B‖ ≤ (N+1:ℝ)^P.vertices.card *
      (2^(HaarPathMultiplicity.singletonEdges P.edgeList).card *
        (p:ℝ)^(9*P.defectTwice+11)*scale)) :
    ‖(1/(N+1:ℂ)) • (pathWeight P • B)‖ ≤
      refinedClassWeightMajorant p (N+1) t
        (HaarPathMultiplicity.singletonEdges P.edgeList).card (t/2-P.vertices.card)*scale := by
  let e := (HaarPathMultiplicity.singletonEdges P.edgeList).card
  let v := P.vertices.card
  let r := t/2-v
  have hsupp := pathWeight_support P hP
  have hhalf : t/2=v+r := by dsimp [v,r]; omega
  have hlen : t=2*(v+r) := by
    obtain ⟨k,hk⟩ := hsupp.1
    omega
  have hdef : P.defectTwice=e+2*r := by
    exact graph_defect_eq_singletons_add_twice_deficit hlen
  have hw := norm_pathWeight_le hp ht0 ht hN P
  change ‖pathWeight P‖ ≤ (4/(N+1:ℝ)^(t/2))*(t:ℝ)^P.defectTwice *
    ((t:ℝ)/(N+1:ℝ)^(1/4:ℝ))^e at hw
  rw [hdef,hhalf] at hw
  change ‖B‖ ≤ (N+1:ℝ)^v * (2^e*(p:ℝ)^(9*P.defectTwice+11)*scale) at hb
  rw [hdef] at hb
  have hnorm : ‖(N:ℂ)+1‖=(N:ℝ)+1 := by
    exact_mod_cast Complex.norm_natCast (N+1)
  rw [norm_smul,norm_div,norm_one,hnorm,norm_smul]
  calc
    _ ≤ (1/(N+1:ℝ))*
        (((4/(N+1:ℝ)^(v+r))*(t:ℝ)^(e+2*r)*
          ((t:ℝ)/(N+1:ℝ)^(1/4:ℝ))^e) *
          ((N+1:ℝ)^v*(2^e*(p:ℝ)^(9*(e+2*r)+11)*scale))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hw hb (norm_nonneg _) (by positivity)) (by positivity)
    _ = (((N+1:ℝ)^v/(N+1))*(4/(N+1:ℝ)^(v+r)))*
        (t:ℝ)^(e+2*r)*((t:ℝ)/(N+1:ℝ)^(1/4:ℝ))^e*
        2^e*(p:ℝ)^(9*(e+2*r)+11)*scale := by ring
    _ = _ := by
      rw [vertex_dimension_cancellation (by positivity)]
      rfl

end Nonadditivity.HaarSharpPathWeight
