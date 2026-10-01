/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarOperatorPathBridge
import Nonadditivity.HaarPathSupport

/-! # Exact grouped operator sum over all literal Haar paths -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Nonadditivity.HaarOperatorPathBridge
open MeasureTheory HaarModel HaarWordExpansion HaarOperatorCurry
open HaarIteratedMoments HaarOnePairAssembly HaarPathExpansion HaarPathWeights
open HaarPathGraph HaarPathProfiles HaarVacuumFunctional RegularCoefficientEnergy
open scoped BigOperators Matrix Matrix.Norms.L2Operator

theorem exists_reducedWord {t : ℕ} (g : FreeGroup (Fin 2))
    (hg : FreeGroup.norm g=t) : ∃ c : ReducedColors t, reducedWord c=g := by
  subst t
  exact ⟨colorsOfWord g,colorsOfWord_word g⟩

def pathWeight {N t : ℕ} (P : Path (Fin (N+1)) 2 t) : ℂ :=
  ∫ U : LocalUnitary N × LocalUnitary N, pathProduct P U ∂(haar N).prod (haar N)

def pathOperatorSum {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (N : ℕ)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p t : ℕ) :
    E →L[ℂ] E :=
  ∑ P : Path (Fin (N+1)) 2 t,
    pathWeight P • (A^p) (FreeGroup.mk (List.ofFn P.colors))

theorem pathWeight_eq_zero_of_not_even {N t : ℕ}
    (P : Path (Fin (N+1)) 2 t) (ht : ¬Even t) : pathWeight P=0 := by
  by_contra hn
  exact ht (even_length_of_integral_ne_zero P hn)

theorem pathOperatorSum_eq_zero_of_not_even {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (N : ℕ)
    (A : HaarOperatorPolynomial.Polynomial (FreeGroup (Fin 2)) E) (p t : ℕ)
    (ht : ¬Even t) : pathOperatorSum N A p t=0 := by
  apply Finset.sum_eq_zero
  intro P hP
  rw [pathWeight_eq_zero_of_not_even P ht,zero_smul]

variable {H ι : Type} [Group H] [DecidableEq H] [Fintype ι] [DecidableEq ι]

theorem operatorLengthContribution_eq_colorSum (N p t : ℕ) (ht : 0<t)
    (f : MatrixPolynomial (FreeGroup (Fin 2) × H) ι) :
    operatorLengthContribution (pairMeasure N) (pairMatrix N) f p t =
      ∑ c : ReducedColors t,
        (∫ U : Pair N, normalizedTrace (pairMatrix N U (reducedWord c)) ∂pairMeasure N) •
          operatorCurry (f^p) (reducedWord c) := by
  classical
  let W : Finset (FreeGroup (Fin 2)) := Finset.univ.image (@reducedWord t)
  have hmem (g : FreeGroup (Fin 2)) : g ∈ W ↔ FreeGroup.norm g=t := by
    constructor
    · intro hg
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hg
      exact reducedWord_norm c
    · intro hg
      obtain ⟨c,rfl⟩ := exists_reducedWord g hg
      exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩
  have he := Finset.sum_image (s := (Finset.univ : Finset (ReducedColors t)))
    (g := @reducedWord t)
    (f := fun g => (∫ U : Pair N, normalizedTrace (pairMatrix N U g) ∂pairMeasure N) •
      operatorCurry (f^p) g)
    (fun _ _ _ _ h => reducedWord_injective h)
  rw [←he]
  unfold operatorLengthContribution
  apply Finset.sum_subset
  · intro g hg
    exact (hmem g).mpr (Finset.mem_filter.mp hg).2
  · intro g hg hn
    have hgt := (hmem g).mp hg
    have hne : g ≠ 1 := by
      intro heq
      simp only [heq,FreeGroup.norm_one] at hgt
      omega
    have hn' : g ∉ (MonoidAlgebra.curryRingEquiv (f^p)).support := by
      intro hs
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne,hs⟩,hgt⟩)
    have hz := Finsupp.notMem_support_iff.mp hn'
    rw [operatorCurry_apply,hz,map_zero,smul_zero]

/-- The exact normalized grouped trace contribution; all paths are literal,
and operator coefficients are kept together before taking norms. -/
theorem operatorLengthContribution_eq_pathSum (N p t : ℕ) (ht : 0<t)
    (f : MatrixPolynomial (FreeGroup (Fin 2) × H) ι) :
    operatorLengthContribution (pairMeasure N) (pairMatrix N) f p t =
      (1/(N+1:ℂ)) • pathOperatorSum N (operatorCurry f) p t := by
  rw [operatorLengthContribution_eq_colorSum N p t ht f]
  have hw (c : ReducedColors t) := integral_normalized_word (N := N) c.val c.property
  change ∀ c : ReducedColors t,
    (∫ U : Pair N, normalizedTrace (pairMatrix N U (reducedWord c)) ∂pairMeasure N) = _ at hw
  simp_rw [hw, mul_smul, Finset.sum_smul,
    ←Finset.smul_sum]
  congr 1
  unfold pathOperatorSum
  rw [←(pathEquiv (V := Fin (N+1)) t).sum_comp]
  simp only [Fintype.sum_prod_type,pathEquiv,assignmentPath,pathWeight,map_pow]
  rfl

theorem norm_operatorLengthContribution_eq (N p t : ℕ) (ht : 0<t)
    (f : MatrixPolynomial (FreeGroup (Fin 2) × H) ι) :
    ‖operatorLengthContribution (pairMeasure N) (pairMatrix N) f p t‖ =
      ‖pathOperatorSum N (operatorCurry f) p t‖ / (N+1:ℝ) := by
  rw [operatorLengthContribution_eq_pathSum N p t ht f,norm_smul,norm_div,norm_one]
  have hnorm : ‖(N:ℂ)+1‖ = (N:ℝ)+1 := by
    exact_mod_cast Complex.norm_natCast (N+1)
  rw [hnorm]
  ring

theorem mixedLengthContribution_le_of_pathSum [Nonempty ι]
    (N p t : ℕ) (ht : 0<t)
    (f : MatrixPolynomial (FreeGroup (Fin 2) × H) ι) {B : ℝ}
    (hb : ‖pathOperatorSum N (operatorCurry f) p t‖ ≤ (N+1:ℝ)*B) :
    ‖HaarMixedWordExpansion.mixedLengthContribution (pairMeasure N) (pairMatrix N) f p t‖ ≤ B := by
  apply (norm_mixedLengthContribution_le (pairMeasure N) (pairMatrix N) f p t).trans
  rw [norm_operatorLengthContribution_eq N p t ht f]
  exact (div_le_iff₀ (by positivity : (0:ℝ)<N+1)).mpr (by simpa only [mul_comm] using hb)

end Nonadditivity.HaarOperatorPathBridge
