/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Nonadditivity.StateEnsembles
import Nonadditivity.Channels

/-!
# Explicit finite Weyl twirling

The basis is indexed by `ZMod d`.  The family consists of exactly `d²`
unitary matrices.  No random-matrix or channel theorem is assumed here.
-/

noncomputable section

namespace Nonadditivity.Weyl

open scoped BigOperators ComplexConjugate

variable {d : ℕ} [NeZero d]

def phase (t : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal (fun i => ZMod.stdAddChar (t * i))

def shift (s : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight s).permMatrix ℂ

theorem char_star (a : ZMod d) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

theorem char_mul_star (a : ZMod d) :
    ZMod.stdAddChar a * star (ZMod.stdAddChar a) = 1 := by
  rw [char_star, ← AddChar.map_add_eq_mul]
  simp

theorem phase_unitary (t : ZMod d) : phase t ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose]
  simp only [phase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
    exact char_mul_star _
  · simp [hij]

theorem shift_unitary (s : ZMod d) : shift s ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [shift, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

def unitaryMatrix (s t : ZMod d) : Matrix.unitaryGroup (ZMod d) ℂ :=
  ⟨phase t * shift s, (Matrix.unitaryGroup (ZMod d) ℂ).mul_mem
    (phase_unitary t) (shift_unitary s)⟩

theorem shifted_conjugation_apply (s : ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (i j : ZMod d) :
    (shift s * A * (shift s).conjTranspose) i j = A (i + s) (j + s) := by
  simp only [shift, Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, Equiv.Perm.inv_def, Equiv.symm_symm, id_eq]
  rfl

theorem conjugation_apply (s t : ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) (i j : ZMod d) :
    ((unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ) * A *
      (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) i j =
    ZMod.stdAddChar (t * (i - j)) * A (i + s) (j + s) := by
  change ((phase t * shift s) * A * (phase t * shift s).conjTranspose) i j = _
  rw [Matrix.conjTranspose_mul]
  have hmat : (phase t * shift s) * A * ((shift s).conjTranspose * (phase t).conjTranspose) =
      phase t * (shift s * A * (shift s).conjTranspose) * (phase t).conjTranspose := by
    simp only [Matrix.mul_assoc]
  rw [hmat]
  simp only [phase, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_conjTranspose, Pi.star_apply, shifted_conjugation_apply]
  rw [char_star]
  have he : t * (i - j) = t * i + -(t * j) := by ring
  rw [he, AddChar.map_add_eq_mul]
  ring

/-- Weyl conjugations form a finite group action; their scalar commutation
phases cancel exactly in the conjugation. -/
theorem conjugation_comp (s t r u : ZMod d)
    (A : Matrix (ZMod d) (ZMod d) ℂ) :
    (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ) *
      ((unitaryMatrix r u : Matrix (ZMod d) (ZMod d) ℂ) * A *
        (unitaryMatrix r u : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) *
      (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose =
    (unitaryMatrix (s + r) (t + u) : Matrix (ZMod d) (ZMod d) ℂ) * A *
      (unitaryMatrix (s + r) (t + u) : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose := by
  ext i j
  rw [conjugation_apply, conjugation_apply, conjugation_apply]
  have hsub : (i + s) - (j + s) = i - j := by ring
  rw [hsub, ← mul_assoc, ← AddChar.map_add_eq_mul, ← add_mul]
  simp only [add_assoc]

theorem character_orthogonality (a : ZMod d) :
    (∑ t : ZMod d, ZMod.stdAddChar (t * a)) = if a = 0 then (d : ℂ) else 0 := by
  simpa [ZMod.card] using
    AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar d)

def twirlSum (A : Matrix (ZMod d) (ZMod d) ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  ∑ s : ZMod d, ∑ t : ZMod d,
    (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ) * A *
      (unitaryMatrix s t : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose

/-- Exact unnormalized Weyl twirl for every complex matrix. -/
theorem twirl_sum_eq (A : Matrix (ZMod d) (ZMod d) ℂ) :
    twirlSum A = Matrix.diagonal (fun _ => (d : ℂ) * Matrix.trace A) := by
  ext i j
  simp only [twirlSum, Matrix.sum_apply, conjugation_apply, ← Finset.sum_mul,
    character_orthogonality]
  by_cases hij : i = j
  · subst j
    simp only [sub_self, if_pos]
    rw [← Finset.mul_sum]
    have htrace : (∑ s : ZMod d, A (i + s) (i + s)) = Matrix.trace A := by
      exact Fintype.sum_bijective _ (AddGroup.addLeft_bijective i) _ _ (fun _ => rfl)
    rw [htrace]
    simp
  · simp [sub_ne_zero.mpr hij, hij]

def uniformAverage (A : Matrix (ZMod d) (ZMod d) ℂ) : Matrix (ZMod d) (ZMod d) ℂ :=
  (1 / ((d : ℂ) * d)) • twirlSum A

/-- The normalized twirl is the completely depolarizing map. -/
theorem uniform_average_eq (A : Matrix (ZMod d) (ZMod d) ℂ) :
    uniformAverage A = (Matrix.trace A / (d : ℂ)) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  ext i j
  rw [uniformAverage, twirl_sum_eq]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    field_simp
  · simp [Matrix.smul_apply, hij]

theorem uniform_average_trace_one (A : Matrix (ZMod d) (ZMod d) ℂ)
    (hA : Matrix.trace A = 1) :
    uniformAverage A = (1 / (d : ℂ)) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  rw [uniform_average_eq, hA]

def family (q : ZMod d × ZMod d) : Matrix.unitaryGroup (ZMod d) ℂ :=
  unitaryMatrix q.1 q.2

theorem family_card : Fintype.card (ZMod d × ZMod d) = d ^ 2 := by
  simp [pow_two]

theorem uniform_average_eq_family_sum (A : Matrix (ZMod d) (ZMod d) ℂ) :
    uniformAverage A = ∑ q : ZMod d × ZMod d,
      (1 / ((d : ℂ) * d)) •
        ((family q : Matrix (ZMod d) (ZMod d) ℂ) * A *
          (family q : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) := by
  simp only [uniformAverage, twirlSum, family, Fintype.sum_prod_type, Finset.smul_sum]

def uniformWeight (_ : ZMod d × ZMod d) : ℝ := 1 / ((d : ℝ) * d)

omit [NeZero d] in
theorem uniformWeight_nonneg (q : ZMod d × ZMod d) : 0 ≤ uniformWeight q := by
  dsimp [uniformWeight]
  positivity

theorem uniformWeight_sum : (∑ q : ZMod d × ZMod d, uniformWeight q) = 1 := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [uniformWeight, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card, nsmul_eq_mul, Nat.cast_mul]
  field_simp

omit [NeZero d] in
theorem uniformWeight_complex (q : ZMod d × ZMod d) :
    (uniformWeight q : ℂ) = 1 / ((d : ℂ) * d) := by
  simp [uniformWeight]

theorem uniform_average_eq_weighted_sum (A : Matrix (ZMod d) (ZMod d) ℂ) :
    uniformAverage A = ∑ q : ZMod d × ZMod d,
      (uniformWeight q : ℂ) •
        ((family q : Matrix (ZMod d) (ZMod d) ℂ) * A *
          (family q : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose) := by
  simp only [uniformWeight_complex, uniform_average_eq_family_sum]

/-- The completely depolarizing channel as an actual normalized Kraus family
of `d²` explicit unitaries. -/
def depolarizingChannel :
    Channels.KrausChannel (ZMod d) (ZMod d) (ZMod d × ZMod d) :=
  Channels.KrausChannel.randomUnitary uniformWeight uniformWeight_nonneg uniformWeight_sum family

theorem depolarizingChannel_map (A : Matrix (ZMod d) (ZMod d) ℂ) :
    (depolarizingChannel (d := d)).map A =
      (Matrix.trace A / (d : ℂ)) • (1 : Matrix (ZMod d) (ZMod d) ℂ) := by
  rw [depolarizingChannel, Channels.KrausChannel.randomUnitary_map,
    ← uniform_average_eq_weighted_sum, uniform_average_eq]

theorem depolarizingChannel_output (ρ : Entropy.DensityMatrix (ZMod d)) :
    (depolarizingChannel (d := d)).output ρ = Entropy.maximallyMixed (ZMod d) := by
  apply Entropy.DensityMatrix.ext
  change (depolarizingChannel (d := d)).map ρ.matrix = _
  rw [depolarizingChannel_map, ρ.normalized]
  simp [Entropy.maximallyMixed, ZMod.card]

theorem depolarizingChannel_output_entropy (ρ : Entropy.DensityMatrix (ZMod d)) :
    ((depolarizingChannel (d := d)).output ρ).vonNeumann = Real.log d := by
  rw [depolarizingChannel_output, Entropy.maximallyMixed_entropy, ZMod.card]

def orbitIndex : Fin (d ^ 2) ≃ (ZMod d × ZMod d) :=
  (Fintype.equivFinOfCardEq family_card).symm

theorem density_conjugation_comp (ρ : Entropy.DensityMatrix (ZMod d))
    (q r : ZMod d × ZMod d) :
    (ρ.unitaryConjugate (family r)).unitaryConjugate (family q) =
      ρ.unitaryConjugate (family (q.1 + r.1, q.2 + r.2)) := by
  apply Entropy.DensityMatrix.ext
  exact conjugation_comp q.1 q.2 r.1 r.2 ρ.matrix

theorem density_conjugation_apply (ρ : Entropy.DensityMatrix (ZMod d))
    (q : ZMod d × ZMod d) (i j : ZMod d) :
    (ρ.unitaryConjugate (family q)).matrix i j =
      ZMod.stdAddChar (q.2 * (i - j)) * ρ.matrix (i + q.1) (j + q.1) :=
  conjugation_apply q.1 q.2 ρ.matrix i j

theorem density_conjugation_zero (ρ : Entropy.DensityMatrix (ZMod d)) :
    ρ.unitaryConjugate (family (0, 0)) = ρ := by
  apply Entropy.DensityMatrix.ext
  ext i j
  rw [density_conjugation_apply]
  simp only [zero_mul, AddChar.map_zero_eq_one, add_zero, one_mul]

def orbitClosure (outputs : Set (Entropy.DensityMatrix (ZMod d))) :
    Set (Entropy.DensityMatrix (ZMod d)) :=
  {ρ | ∃ σ ∈ outputs, ∃ q : ZMod d × ZMod d, ρ = σ.unitaryConjugate (family q)}

theorem subset_orbitClosure (outputs : Set (Entropy.DensityMatrix (ZMod d))) :
    outputs ⊆ orbitClosure outputs := by
  intro ρ hρ
  exact ⟨ρ, hρ, (0, 0), (density_conjugation_zero ρ).symm⟩

theorem orbitClosure_closed (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d)) (hρ : ρ ∈ orbitClosure outputs)
    (q : ZMod d × ZMod d) :
    ρ.unitaryConjugate (family q) ∈ orbitClosure outputs := by
  obtain ⟨σ, hσ, r, rfl⟩ := hρ
  exact ⟨σ, hσ, (q.1 + r.1, q.2 + r.2), density_conjugation_comp σ q r⟩

theorem orbitClosure_entropy_image (outputs : Set (Entropy.DensityMatrix (ZMod d))) :
    Entropy.DensityMatrix.vonNeumann '' orbitClosure outputs =
      Entropy.DensityMatrix.vonNeumann '' outputs := by
  ext s
  constructor
  · rintro ⟨ρ, ⟨σ, hσ, q, rfl⟩, hρ⟩
    exact ⟨σ, hσ, (σ.unitaryConjugate_entropy (family q)).symm.trans hρ⟩
  · rintro ⟨ρ, hρ, hs⟩
    exact ⟨ρ, subset_orbitClosure outputs hρ, hs⟩

theorem orbitClosure_minimumEntropy (outputs : Set (Entropy.DensityMatrix (ZMod d))) :
    StateEnsembles.minimumEntropy (orbitClosure outputs) =
      StateEnsembles.minimumEntropy outputs := by
  unfold StateEnsembles.minimumEntropy
  rw [orbitClosure_entropy_image]

/-- A concrete normalized orbit ensemble with exactly `d²` states. -/
def orbitEnsemble (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    StateEnsembles.Ensemble outputs where
  size := d ^ 2
  weight := fun i => uniformWeight (orbitIndex i)
  weight_nonneg := fun i => uniformWeight_nonneg _
  weight_sum := by
    have hs := Fintype.sum_equiv (orbitIndex (d := d))
      (fun i => uniformWeight (orbitIndex i)) uniformWeight (fun _ => rfl)
    exact hs.trans uniformWeight_sum
  state := fun i => ρ.unitaryConjugate (family (orbitIndex i))
  state_mem := fun i => hclosed (orbitIndex i)

theorem orbit_ensemble_average (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    (orbitEnsemble outputs ρ hclosed).average = Entropy.maximallyMixed (ZMod d) := by
  apply Entropy.DensityMatrix.ext
  change (∑ i : Fin (d ^ 2), (uniformWeight (orbitIndex i) : ℂ) •
    (ρ.unitaryConjugate (family (orbitIndex i))).matrix) = _
  have hs := Fintype.sum_equiv (orbitIndex (d := d))
    (fun i => (uniformWeight (orbitIndex i) : ℂ) •
      (ρ.unitaryConjugate (family (orbitIndex i))).matrix)
    (fun q => (uniformWeight q : ℂ) • (ρ.unitaryConjugate (family q)).matrix)
    (fun _ => rfl)
  rw [hs]
  change (∑ q : ZMod d × ZMod d, (uniformWeight q : ℂ) •
    ((family q : Matrix (ZMod d) (ZMod d) ℂ) * ρ.matrix *
      (family q : Matrix (ZMod d) (ZMod d) ℂ).conjTranspose)) = _
  rw [← uniform_average_eq_weighted_sum, uniform_average_trace_one _ ρ.normalized]
  simp [Entropy.maximallyMixed, ZMod.card]

theorem orbit_ensemble_entropy (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs)
    (i : Fin (d ^ 2)) :
    ((orbitEnsemble outputs ρ hclosed).state i).vonNeumann = ρ.vonNeumann :=
  ρ.unitaryConjugate_entropy _

theorem orbit_ensemble_information (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    (orbitEnsemble outputs ρ hclosed).information = Real.log d - ρ.vonNeumann := by
  unfold StateEnsembles.Ensemble.information
  simp_rw [orbit_ensemble_entropy]
  rw [← Finset.sum_mul, StateEnsembles.Ensemble.weight_sum, one_mul,
    orbit_ensemble_average, Entropy.maximallyMixed_entropy, ZMod.card]

/-- The Weyl orbit lower bound is proved from an actual finite ensemble,
not from a postulated orbit or maximally mixed average. -/
theorem orbit_information_lower_bound
    (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (ρ : Entropy.DensityMatrix (ZMod d))
    (hclosed : ∀ q : ZMod d × ZMod d, ρ.unitaryConjugate (family q) ∈ outputs) :
    Real.log d - ρ.vonNeumann ≤ StateEnsembles.quantity outputs := by
  simpa only [ZMod.card] using StateEnsembles.orbit_lower_bound
    (orbitEnsemble outputs ρ hclosed) ρ (orbit_ensemble_average outputs ρ hclosed)
    (orbit_ensemble_entropy outputs ρ hclosed)

/-- For any nonempty set of quantum outputs closed under the explicit Weyl
family, Holevo information equals log dimension minus minimum output entropy. -/
theorem quantity_eq_of_weyl_closed
    (outputs : Set (Entropy.DensityMatrix (ZMod d))) (hne : outputs.Nonempty)
    (hclosed : ∀ ρ ∈ outputs, ∀ q : ZMod d × ZMod d,
      ρ.unitaryConjugate (family q) ∈ outputs) :
    StateEnsembles.quantity outputs =
      Real.log d - StateEnsembles.minimumEntropy outputs := by
  have horbit : ∀ ρ ∈ outputs, ∃ e : StateEnsembles.Ensemble outputs,
      e.average = Entropy.maximallyMixed (ZMod d) ∧
      ∀ i, (e.state i).vonNeumann = ρ.vonNeumann := by
    intro ρ hρ
    exact ⟨orbitEnsemble outputs ρ (hclosed ρ hρ),
      orbit_ensemble_average outputs ρ (hclosed ρ hρ),
      orbit_ensemble_entropy outputs ρ (hclosed ρ hρ)⟩
  simpa only [ZMod.card] using StateEnsembles.quantity_eq_of_orbits hne horbit

/-- Exact Weyl conversion for the union of unitary orbits of a nonempty set
of genuine quantum outputs. -/
theorem quantity_orbitClosure (outputs : Set (Entropy.DensityMatrix (ZMod d)))
    (hne : outputs.Nonempty) :
    StateEnsembles.quantity (orbitClosure outputs) =
      Real.log d - StateEnsembles.minimumEntropy outputs := by
  have hne' : (orbitClosure outputs).Nonempty :=
    hne.mono (subset_orbitClosure outputs)
  rw [quantity_eq_of_weyl_closed (orbitClosure outputs) hne'
    (orbitClosure_closed outputs), orbitClosure_minimumEntropy]

end Nonadditivity.Weyl
