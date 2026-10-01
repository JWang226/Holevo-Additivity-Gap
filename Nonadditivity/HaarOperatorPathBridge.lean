/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarVacuumFunctional
import Nonadditivity.HaarOnePairAssembly
import Nonadditivity.HaarPathExpansion
import Nonadditivity.HaarPathVertexFibre
import Nonadditivity.HaarPathCoefficientWords

/-! # Actual operator coefficients and the closed-path expansion

This connects the canonical `Fin 2` Haar sample and the curried operator
polynomial to the product-Haar closed-path model.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Nonadditivity.HaarOperatorPathBridge
open MeasureTheory HaarModel HaarFourthMoments HaarWordExpansion HaarOperatorCurry
open HaarIteratedMoments HaarOnePairAssembly HaarPathExpansion HaarPathWeights
open HaarPathGraph HaarPathProfiles HaarVacuumFunctional
open scoped BigOperators Matrix Matrix.Norms.L2Operator

theorem operatorCurry_support {G H ι : Type} [Group G] [Group H]
    [DecidableEq G] [DecidableEq H] [Fintype ι] [DecidableEq ι]
    (f : MatrixPolynomial (G × H) ι) {g : G} (hg : g ∈ (operatorCurry f).support) :
    ∃ h : H, (g,h) ∈ f.support := by
  classical
  by_contra hn
  have hz : MonoidAlgebra.curryRingEquiv f g = 0 := by
    apply Finsupp.ext
    intro h
    change f (g,h)=0
    exact Finsupp.notMem_support_iff.mp (fun hh => hn ⟨h,hh⟩)
  apply Finsupp.mem_support_iff.mp hg
  rw [operatorCurry_apply,hz,map_zero]

theorem operatorCurry_linear {H ι : Type} [Group H] [DecidableEq H]
    [Fintype ι] [DecidableEq ι]
    (f : MatrixPolynomial (FreeGroup (Fin 2) × H) ι)
    (hf : ∀ w ∈ f.support, FreeGroup.norm w.1 ≤ 1) :
    ∀ g ∈ (operatorCurry f).support, g.toWord.length ≤ 1 := by
  intro g hg
  obtain ⟨h,hh⟩ := operatorCurry_support f hg
  exact hf (g,h) hh

theorem integral_pair_eq_prod {N : ℕ} (F : LocalUnitary N × LocalUnitary N → ℂ) :
    (∫ U : Pair N, F (U 0,U 1) ∂pairMeasure N) =
      ∫ U : LocalUnitary N × LocalUnitary N, F U ∂(haar N).prod (haar N) := by
  exact (measurePreserving_finTwoArrow (haar N)).integral_comp' F

theorem pairGenerator_eq {N : ℕ} (U : Pair N) : pairGenerator (U 0,U 1) = U := by
  funext a
  fin_cases a <;> simp [pairGenerator]

theorem integral_normalized_word {N t : ℕ} (c : Fin t → Color 2)
    (hc : ∀ i j : Fin t, i.val+1=j.val → c j ≠ flipColor (c i)) :
    (∫ U : Pair N, normalizedTrace (pairMatrix N U (FreeGroup.mk (List.ofFn c)))
      ∂pairMeasure N) =
      (1 / (N+1 : ℂ)) * ∑ x : ClosedAssignment (Fin (N+1)) t,
        ∫ U : LocalUnitary N × LocalUnitary N,
          pathProduct (assignmentPath c hc x) U ∂(haar N).prod (haar N) := by
  have he : (fun U : Pair N => normalizedTrace (pairMatrix N U (FreeGroup.mk (List.ofFn c)))) =
      (fun U : Pair N =>
        (((FreeGroup.lift (pairGenerator (U 0,U 1)) (FreeGroup.mk (List.ofFn c)) :
          LocalUnitary N) : Mat N).trace) / (N+1:ℂ)) := by
    funext U
    rw [pairGenerator_eq]
    simp only [normalizedTrace,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    rfl
  rw [he,integral_pair_eq_prod (fun U =>
    (((FreeGroup.lift (pairGenerator U) (FreeGroup.mk (List.ofFn c)) :
      LocalUnitary N) : Mat N).trace) / (N+1:ℂ)),integral_div,
    integral_word_trace_eq_sum_pathProduct c hc]
  ring

/-- The finite alphabet of actual reduced color words of fixed length. -/
def ReducedColors (t : ℕ) :=
  {c : Fin t → Color 2 // ∀ i j : Fin t, i.val+1=j.val → c j ≠ flipColor (c i)}

instance (t : ℕ) : Fintype (ReducedColors t) := by
  classical
  unfold ReducedColors
  infer_instance

def reducedWord {t : ℕ} (c : ReducedColors t) : FreeGroup (Fin 2) :=
  FreeGroup.mk (List.ofFn c.val)

theorem reducedWord_toWord {t : ℕ} (c : ReducedColors t) :
    (reducedWord c).toWord = List.ofFn c.val := by
  let P : Path Unit 2 t := ⟨fun _ => (),c.val,rfl,c.property⟩
  exact FreeGroup.toWord_mk.trans P.colorList_reduced.reduce_eq

theorem reducedWord_norm {t : ℕ} (c : ReducedColors t) :
    FreeGroup.norm (reducedWord c) = t := by
  change (reducedWord c).toWord.length=t
  rw [reducedWord_toWord,List.length_ofFn]

theorem reducedWord_injective {t : ℕ} : Function.Injective (@reducedWord t) := by
  intro c c' he
  apply Subtype.ext
  apply List.ofFn_injective
  simpa only [reducedWord_toWord] using congrArg FreeGroup.toWord he

def colorsOfWord (g : FreeGroup (Fin 2)) : ReducedColors (FreeGroup.norm g) :=
  ⟨fun i => g.toWord[i.val],by
    intro i j hij hbad
    have hred := List.isChain_iff_getElem.mp
      (show FreeGroup.IsReduced g.toWord from FreeGroup.isReduced_toWord)
    have hij' : i.val+1<g.toWord.length := by simpa [←hij] using j.isLt
    have hh := hred i.val hij'
    have hbad' : g.toWord[i.val+1] = flipColor (g.toWord[i.val]) := by
      simpa only [hij] using hbad
    rw [hbad'] at hh
    have hx := hh rfl
    change (g.toWord[i.val]).2 = !(g.toWord[i.val]).2 at hx
    cases hb : (g.toWord[i.val]).2 <;>
      simp only [hb,Bool.not_false,Bool.not_true] at hx <;> contradiction⟩

@[simp] theorem colorsOfWord_word (g : FreeGroup (Fin 2)) :
    reducedWord (colorsOfWord g) = g := by
  change FreeGroup.mk (List.ofFn (fun i : Fin g.toWord.length => g.toWord[i.val])) = g
  rw [List.ofFn_getElem,FreeGroup.mk_toWord]

/-- Closed assignments and reduced color words parametrize every literal path. -/
def pathEquiv {V : Type*} (t : ℕ) :
    ReducedColors t × ClosedAssignment V t ≃ Path V 2 t where
  toFun z := assignmentPath z.1.val z.1.property z.2
  invFun P := (⟨P.colors,P.reduced⟩,⟨P.vertex,P.closed⟩)
  left_inv z := rfl
  right_inv P := Path.ext_data rfl rfl

end Nonadditivity.HaarOperatorPathBridge
