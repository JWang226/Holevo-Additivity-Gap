/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathSupport

/-! # Path estimates on the manuscript's canonical Haar sample space -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathWeights
open MeasureTheory HaarModel HaarInvariantTensor
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- Two distinct coordinates of the canonical sample have exactly the product
Haar expectation, for arbitrary continuous scalar factors. -/
theorem integral_sample_pair_eq_integral_prod {N : ℕ} (K n : ℕ)
    (x y : Fin n × Fin K) (hxy : x ≠ y)
    (f g : LocalUnitary N → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ ω : Sample K n N, f (ω x)*g (ω y) ∂sampleMeasure K n N) =
      ∫ U : LocalUnitary N × LocalUnitary N, f U.1*g U.2 ∂(haar N).prod (haar N) := by
  have hind := ((independent_coordinates K n N).indepFun hxy).comp hf.measurable hg.measurable
  have he := hind.integral_fun_mul_eq_mul_integral
    (hf.comp (continuous_apply x)).aestronglyMeasurable
    (hg.comp (continuous_apply y)).aestronglyMeasurable
  have hx := integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := x)
    hf.aestronglyMeasurable
  have hy := integral_comp_eval (μ := fun _ : Fin n × Fin K => haar N) (i := y)
    hg.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [he]
  simp only [sampleMeasure]
  rw [hx,hy,integral_prod_mul]

lemma continuous_listMonomial {N : ℕ} (L R : List (Entry N)) : Continuous (listMonomial L R) := by
  change Continuous (fun U => listMonomial L R U)
  simp_rw [listMonomial_eq_entryMonomial]
  exact continuous_entryMonomial _ _ _ _

/-- Exact transfer of each closed-path weight to two canonical coordinates. -/
theorem integral_sample_pathProduct_eq {N m : ℕ} (K n : ℕ)
    (x y : Fin n × Fin K) (hxy : x ≠ y)
    (P : HaarPathGraph.Path (Fin (N+1)) 2 m) :
    (∫ ω : Sample K n N, pathProduct P (ω x,ω y) ∂sampleMeasure K n N) =
      ∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N) := by
  simp_rw [pathProduct_eq,signedProduct_eq]
  exact integral_sample_pair_eq_integral_prod K n x y hxy _ _
    (continuous_listMonomial _ _) (continuous_listMonomial _ _)

/-- The explicit singleton-sensitive bound on the existing sample model. -/
theorem norm_sample_pathProduct_integral_le {N m : ℕ} (K n : ℕ)
    (x y : Fin n × Fin K) (hxy : x ≠ y)
    (P : HaarPathGraph.Path (Fin (N+1)) 2 m) (hm : 0 < m)
    (hN : 16*((m/2:ℕ):ℝ)^4 ≤ N+1) :
    ‖∫ ω : Sample K n N, pathProduct P (ω x,ω y) ∂sampleMeasure K n N‖ ≤
      (4/(N+1:ℝ)^(m/2)) * (m:ℝ)^P.defectTwice *
        ((m:ℝ)/Real.sqrt (Real.sqrt (N+1)))^(HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  rw [integral_sample_pathProduct_eq K n x y hxy]
  exact norm_pathProduct_integral_le P hm hN

/-- Paths with too many vertices contribute exactly zero on the same model. -/
theorem integral_sample_pathProduct_eq_zero_of_vertices_gt {N m : ℕ} (K n : ℕ)
    (x y : Fin n × Fin K) (hxy : x ≠ y)
    (P : HaarPathGraph.Path (Fin (N+1)) 2 m) (hv : m/2 < P.vertices.card) :
    (∫ ω : Sample K n N, pathProduct P (ω x,ω y) ∂sampleMeasure K n N)=0 := by
  rw [integral_sample_pathProduct_eq K n x y hxy]
  exact integral_pathProduct_eq_zero_of_vertices_gt P hv

end Nonadditivity.HaarPathWeights
