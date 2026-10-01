/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarTensorReplacement

/-! # Word-length expansion for one mixed tensor replacement

Taking the vacuum trace in the untouched group extracts its identity
coefficient. Thus the one-pair mixed trace error has exactly the same finite
word expansion as the scalar Haar trace, with genuine remaining-group
coefficients retained until the trace is taken.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarMixedWordExpansion
open MeasureTheory HaarWordExpansion HaarTensorReplacement
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker

variable {G H ι ν : Type} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

def identitySlice (f : MatrixPolynomial (G × H) ι) : MatrixPolynomial G ι :=
  Finsupp.mapRange (fun h : MatrixPolynomial H ι => h 1) rfl
    (MonoidAlgebra.curryRingEquiv f)

omit [DecidableEq G] [DecidableEq H] in
@[simp] theorem identitySlice_apply (f : MatrixPolynomial (G × H) ι) (g : G) :
    identitySlice f g = f (g,1) := rfl

omit [DecidableEq G] [DecidableEq H] in
@[simp] theorem identitySlice_zero : identitySlice (0 : MatrixPolynomial (G × H) ι) = 0 := by
  apply Finsupp.ext
  intro g
  rfl

omit [DecidableEq G] [DecidableEq H] in
@[simp] theorem identitySlice_add (f k : MatrixPolynomial (G × H) ι) :
    identitySlice (f+k) = identitySlice f + identitySlice k := by
  apply Finsupp.ext
  intro g
  rfl

theorem identitySlice_single (g : G) (h : H) (A : Matrix ι ι ℂ) :
    identitySlice (MonoidAlgebra.single (g,h) A) =
      if h=1 then MonoidAlgebra.single g A else 0 := by
  apply Finsupp.ext
  intro a
  rw [identitySlice_apply]
  by_cases hh : h=1
  · subst h
    simp [MonoidAlgebra.single_apply]
  · simp [hh, Prod.ext_iff]

omit [DecidableEq G] [DecidableEq H] in
theorem vacuumTrace_identitySlice (f : MatrixPolynomial (G × H) ι) :
    vacuumTrace (identitySlice f) = vacuumTrace f := rfl

omit [DecidableEq H] in
theorem vacuumTrace_add (f k : MatrixPolynomial H ι) :
    vacuumTrace (f+k) = vacuumTrace f + vacuumTrace k := by
  change normalizedTrace (f 1 + k 1) = _
  simp [normalizedTrace, Matrix.trace_add, add_div, vacuumTrace]

/-- A partial finite evaluation followed by the remaining vacuum state is
the ordinary finite trace of the actual identity slice. -/
theorem vacuumTrace_partialEval_eq (ρ : G →* Matrix ν ν ℂ)
    (f : MatrixPolynomial (G × H) ι) :
    vacuumTrace (partialEval ρ f) = normalizedTrace (finiteEval ρ (identitySlice f)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [vacuumTrace, normalizedTrace]
  | add f k hf hk =>
      change vacuumTrace (partialEval ρ ((f : MatrixPolynomial (G × H) ι)+k)) = _
      rw [map_add, vacuumTrace_add, identitySlice_add, map_add, hf, hk]
      simp [normalizedTrace, Matrix.trace_add, add_div]
  | single w A =>
      obtain ⟨g,h⟩ := w
      rw [partialEval_single, identitySlice_single]
      by_cases hh : h=1
      · simp [hh, vacuumTrace]
      · simp [hh, vacuumTrace, normalizedTrace]

section Integration
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ρ : Ω → G →* Matrix ν ν ℂ) [Nonempty ν]

/-- Exact mixed moment error before any estimate or coefficient scalarization. -/
theorem integral_mixed_moment_error (f : MatrixPolynomial (G × H) ι) (p : ℕ)
    (hint : ∀ g, Integrable (fun ω => normalizedTrace (ρ ω g)) μ) :
    (∫ ω, vacuumTrace ((partialEval (ρ ω) f)^p) ∂μ) - vacuumTrace (f^p) =
      ∑ g ∈ (identitySlice (f^p)).support.erase 1,
        normalizedTrace ((f^p) (g,1)) * ∫ ω, normalizedTrace (ρ ω g) ∂μ := by
  simp_rw [← map_pow, vacuumTrace_partialEval_eq]
  have h := integral_moment_error μ ρ (identitySlice (f^p)) 1 hint
  simpa only [pow_one, vacuumTrace_identitySlice, identitySlice_apply] using h

end Integration

section Length
variable {α Ω : Type} [DecidableEq α] [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ρ : Ω → FreeGroup α →* Matrix ν ν ℂ) [Nonempty ν]

def mixedLengthContribution (f : MatrixPolynomial (FreeGroup α × H) ι) (p t : ℕ) : ℂ :=
  ∑ g ∈ ((identitySlice (f^p)).support.erase 1).filter (fun g => FreeGroup.norm g=t),
    normalizedTrace ((f^p) (g,1)) * ∫ ω, normalizedTrace (ρ ω g) ∂μ

/-- The exact mixed error decomposes over lengths `1,...,p` when the replaced
coordinate of the original polynomial is linear. -/
theorem integral_mixed_error_by_length (f : MatrixPolynomial (FreeGroup α × H) ι) (p : ℕ)
    (hlinear : ∀ w ∈ f.support, FreeGroup.norm w.1 ≤ 1)
    (hint : ∀ g, Integrable (fun ω => normalizedTrace (ρ ω g)) μ) :
    (∫ ω, vacuumTrace ((partialEval (ρ ω) f)^p) ∂μ) - vacuumTrace (f^p) =
      ∑ t ∈ Finset.Icc 1 p, mixedLengthContribution μ ρ f p t := by
  rw [integral_mixed_moment_error μ ρ f p hint]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro g hg
  have hs := (Finset.mem_erase.mp hg).2
  have hn := (Finset.mem_erase.mp hg).1
  have h0 : 0 < FreeGroup.norm g := Nat.pos_of_ne_zero (by
    intro hz
    exact hn (FreeGroup.norm_eq_zero.mp hz))
  have hs' : (g,1) ∈ (f^p).support := by
    exact Finsupp.mem_support_iff.mpr (by
      simpa only [identitySlice_apply] using Finsupp.mem_support_iff.mp hs)
  have hp := support_pow_length_le f (fun w => FreeGroup.norm w.1) (by simp)
    (fun a b => FreeGroup.norm_mul_le a.1 b.1) 1 hlinear p (g,1) hs'
  exact Finset.mem_Icc.mpr ⟨h0, by simpa using hp⟩

end Length
end Nonadditivity.HaarMixedWordExpansion
