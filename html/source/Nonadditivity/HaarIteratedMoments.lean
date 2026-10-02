/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarHybridMoments
import Nonadditivity.HaarTensorConstants

/-! # Iterating the actual Haar replacements

The recursively integrated quantity uses the canonical Haar law at every
coordinate, literal finite matrix substitutions, and the actual regular norm
on the remaining free factors. The induction only assumes the one-pair trace
comparison, uniformly in those remaining free factors.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Nonadditivity.HaarIteratedMoments
open MeasureTheory HaarModel HaarWordExpansion HaarTensorReplacement
open HaarHybridMoments HaarTensorConstants ProductHaagerupProduct
open scoped BigOperators Matrix Matrix.Norms.L2Operator

abbrev Pair (N : ℕ) := Fin 2 → LocalUnitary N

def pairMeasure (N : ℕ) : Measure (Pair N) := Measure.pi (fun _ => haar N)

instance pairProbability (N : ℕ) : IsProbabilityMeasure (pairMeasure N) := by
  unfold pairMeasure
  infer_instance

def pairRepresentation (N : ℕ) (U : Pair N) :
    FreeGroup (Fin 2) →* LocalUnitary N := FreeGroup.lift U

theorem continuous_pairRepresentation (N : ℕ) (g : FreeGroup (Fin 2)) :
    Continuous (fun U : Pair N => (pairRepresentation N U g : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)) := by
  have hl : ∀ l : List (Fin 2 × Bool), Continuous
      (fun U : Pair N => pairRepresentation N U (FreeGroup.mk l)) := by
    intro l
    induction l with
    | nil => simpa using (continuous_const : Continuous (fun _ : Pair N => (1 : LocalUnitary N)))
    | cons x l ih =>
      simp only [pairRepresentation, FreeGroup.lift_mk, List.map_cons, List.prod_cons] at ih ⊢
      apply Continuous.mul _ ih
      cases hx : x.2
      · exact (continuous_apply x.1).inv
      · exact continuous_apply x.1
  exact continuous_subtype_val.comp (by simpa only [FreeGroup.mk_toWord] using hl g.toWord)

def iteratedMoment (N p : ℕ) : (j : ℕ) →
    {ι : Type} → [Fintype ι] → [DecidableEq ι] →
    MatrixPolynomial (GroupIndex (Fin 2) j) ι → ℝ
  | 0, _, _, _, f => ‖regularEval f‖^p
  | j+1, _, _, _, f => ∫ U : Pair N,
      iteratedMoment N p j (partialEval (representationMatrix (pairRepresentation N U)) f)
        ∂pairMeasure N

theorem iteratedMoment_nonneg (N p j : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) j) ι) : 0 ≤ iteratedMoment N p j f := by
  induction j generalizing ι with
  | zero => exact pow_nonneg (norm_nonneg _) _
  | succ j ih => exact integral_nonneg (fun U => ih _)

/-- The one-pair analytic input, with actual remaining free factors as
coefficients. This is a single trace comparison, not an assumed norm estimate. -/
def OnePairTraceBound (N p : ℕ) : Prop :=
  ∀ (j : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) (j+1)) ι),
    IsSelfAdjoint (regularEval f) →
    (∀ w ∈ f.support, RadiusLe 1 w) →
    (∫ U : Pair N,
      (vacuumTrace ((partialEval (representationMatrix (pairRepresentation N U)) f)^p)).re
        ∂pairMeasure N) ≤
      (vacuumTrace (f^p)).re + (N+1 : ℝ)^(-(1/2 : ℝ))*‖regularEval f‖^p

/-- Every replacement contributes its enlarged matrix dimension and the
number of still-free coordinates. This yields the explicit triangular powers. -/
theorem iteratedMoment_le (N p : ℕ) (hp : Even p) (hp2 : 2 ≤ p)
    (hone : OnePairTraceBound N p) (j : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : MatrixPolynomial (GroupIndex (Fin 2) j) ι)
    (hf : IsSelfAdjoint (regularEval f))
    (hlinear : ∀ w ∈ f.support, RadiusLe 1 w) :
    iteratedMoment N p j f ≤
      replacementMultiplier (Fintype.card ι) (N+1) p j * ‖regularEval f‖^p := by
  induction j generalizing ι with
  | zero => simp [iteratedMoment, replacementMultiplier, triangle]
  | succ j ih =>
    let C := replacementMultiplier ((Fintype.card ι : ℝ)*(N+1)) (N+1) p j
    have hC : 0 ≤ C := by unfold C replacementMultiplier; positivity
    have hi : ∀ U : Pair N,
        iteratedMoment N p j
          (partialEval (representationMatrix (pairRepresentation N U)) f) ≤
        C * ‖regularEval (partialEval (representationMatrix (pairRepresentation N U)) f)‖^p := by
      intro U
      have hl : ∀ w ∈ (partialEval (representationMatrix (pairRepresentation N U)) f).support,
          RadiusLe 1 w := by
        intro w hw
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (partialEval_support _ f hw)
        exact (hlinear v hv).2
      simpa only [C, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one] using ih _ (partialEval_selfAdjoint _ f hf) hl
    have hint := integrable_partial_regularNorm_pow (pairMeasure N)
      (fun U => representationMatrix (pairRepresentation N U))
      (continuous_pairRepresentation N) f p
    have hstep := replacement_norm_moment_le (pairMeasure N) (pairRepresentation N)
      (continuous_pairRepresentation N) f hf (fun w hw => (hlinear w hw).2)
      hp hp2 ((N+1:ℝ)^(-(1/2:ℝ))) (hone j ι f hf hlinear)
    have hle := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun U => iteratedMoment_nonneg N p j _))
      (hint.const_mul C) (Filter.Eventually.of_forall hi)
    rw [integral_const_mul] at hle
    apply hle.trans
    apply (mul_le_mul_of_nonneg_left hstep hC).trans_eq
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    calc
      _ = (C * (2*(Fintype.card ι:ℝ)*(N+1)*(p:ℝ)^(3*j)*(1+(N+1:ℝ)^(-(1/2:ℝ))))) *
          ‖regularEval f‖^p := by ring_nf; rfl
      _ = _ := by rw [show C = replacementMultiplier ((Fintype.card ι:ℝ)*(N+1)) (N+1) p j from rfl,
          replacementMultiplier_succ]

end Nonadditivity.HaarIteratedMoments
