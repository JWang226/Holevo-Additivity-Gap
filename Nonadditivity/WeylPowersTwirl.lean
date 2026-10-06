/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.WeylPowersIndex

/-! Exact independent local Weyl twirls for every positive tensor power. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Nonadditivity.WeylPowersTwirl
open RegularizedHolevo
open scoped BigOperators Kronecker ComplexConjugate

abbrev Basis (d n : ℕ) := PositiveTensorIndex (ZMod d) n
abbrev Label (d n : ℕ) := PositiveTensorIndex (ZMod d × ZMod d) n

variable {d : ℕ} [NeZero d]

abbrev tensorFamily (n : ℕ) : Label d n → Matrix.unitaryGroup (Basis d n) ℂ :=
  WeylPowers.positiveUnitaryPower Weyl.family n

private theorem conjugate_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (i j a b : ι) :
    (U * Matrix.single a b (1 : ℂ) * U.conjTranspose) i j = U i a * star (U j b) := by
  simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

private theorem family_entry_moment (i j a b : ZMod d) :
    (∑ q : ZMod d × ZMod d,
      (Weyl.family q : Matrix _ _ ℂ) i a * star ((Weyl.family q : Matrix _ _ ℂ) j b)) =
      if i = j ∧ a = b then (d : ℂ) else 0 := by
  have h := congrArg (fun M : Matrix (ZMod d) (ZMod d) ℂ => M i j)
    (Weyl.twirl_sum_eq (Matrix.single a b 1))
  simp only [Weyl.twirlSum, Matrix.sum_apply, conjugate_single_apply] at h
  simp only [Fintype.sum_prod_type, Weyl.family]
  rw [h]
  by_cases hij : i = j <;> by_cases hab : a = b
  · subst j; subst b; simp
  · simp [hij, hab]
  · simp [hij, hab]
  · simp [hij, hab]

/-- Second-moment orthogonality for the product family. -/
theorem tensorFamily_entry_moment (n : ℕ) (i j a b : Basis d n) :
    (∑ q : Label d n,
      (tensorFamily n q : Matrix _ _ ℂ) i a *
        star ((tensorFamily n q : Matrix _ _ ℂ) j b)) =
      if i = j ∧ a = b then (Fintype.card (Basis d n) : ℂ) else 0 := by
  induction n with
  | zero => simpa [Basis, PositiveTensorIndex, tensorFamily, WeylPowers.positiveUnitaryPower, ZMod.card] using
      family_entry_moment i j a b
  | succ n ih =>
    change (∑ q : Label d n × (ZMod d × ZMod d),
      ((tensorFamily n q.1 : Matrix _ _ ℂ) i.1 a.1 *
        (Weyl.family q.2 : Matrix _ _ ℂ) i.2 a.2) *
      star ((tensorFamily n q.1 : Matrix _ _ ℂ) j.1 b.1 *
        (Weyl.family q.2 : Matrix _ _ ℂ) j.2 b.2)) = _
    rw [Fintype.sum_prod_type]
    have hfactor :
        (∑ q : Label d n, ∑ r : ZMod d × ZMod d,
          ((tensorFamily n q : Matrix _ _ ℂ) i.1 a.1 *
            (Weyl.family r : Matrix _ _ ℂ) i.2 a.2) *
          star ((tensorFamily n q : Matrix _ _ ℂ) j.1 b.1 *
            (Weyl.family r : Matrix _ _ ℂ) j.2 b.2)) =
        (∑ q : Label d n, (tensorFamily n q : Matrix _ _ ℂ) i.1 a.1 *
          star ((tensorFamily n q : Matrix _ _ ℂ) j.1 b.1)) *
        (∑ r : ZMod d × ZMod d, (Weyl.family r : Matrix _ _ ℂ) i.2 a.2 *
          star ((Weyl.family r : Matrix _ _ ℂ) j.2 b.2)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      simp only [star_mul]
      ring
    rw [hfactor]
    rw [ih, family_entry_moment]
    change (if i.1 = j.1 ∧ a.1 = b.1 then _ else 0) *
      (if i.2 = j.2 ∧ a.2 = b.2 then _ else 0) =
      if i = j ∧ a = b then (Fintype.card (Basis d n × ZMod d) : ℂ) else 0
    simp only [Fintype.card_prod, Nat.cast_mul, ZMod.card,
      show i = j ↔ i.1 = j.1 ∧ i.2 = j.2 from Prod.ext_iff,
      show a = b ↔ a.1 = b.1 ∧ a.2 = b.2 from Prod.ext_iff]
    split_ifs <;> simp_all

/-- The unnormalized local twirl applies to arbitrary joint matrices. -/
theorem twirl_sum_eq (n : ℕ) (A : Matrix (Basis d n) (Basis d n) ℂ) :
    (∑ q : Label d n, (tensorFamily n q : Matrix _ _ ℂ) * A *
      (tensorFamily n q : Matrix _ _ ℂ).conjTranspose) =
      Matrix.diagonal (fun _ => (Fintype.card (Basis d n) : ℂ) * Matrix.trace A) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
  simp_rw [mul_right_comm _ (A _ _), ← Finset.sum_mul, tensorFamily_entry_moment]
  by_cases hij : i = j
  · subst j
    simp [Matrix.trace, ← Finset.mul_sum]
  · simp [hij]


theorem label_card (n : ℕ) : Fintype.card (Label d n) = Fintype.card (Basis d n) ^ 2 := by
  simp only [Label, Basis, positiveTensorIndex_card, Fintype.card_prod, ZMod.card]
  rw [mul_pow, pow_two]

def uniformWeight (n : ℕ) (_ : Label d n) : ℝ :=
  1 / (Fintype.card (Label d n) : ℝ)

theorem uniformWeight_nonneg (n : ℕ) (q : Label d n) : 0 ≤ uniformWeight n q := by
  unfold uniformWeight
  positivity

theorem uniformWeight_sum (n : ℕ) : (∑ q : Label d n, uniformWeight n q) = 1 := by
  simp [uniformWeight]

/-- The normalized product twirl is completely depolarizing, including on entangled inputs. -/
theorem uniform_average_eq (n : ℕ) (A : Matrix (Basis d n) (Basis d n) ℂ) :
    (∑ q : Label d n, (uniformWeight n q : ℂ) •
      ((tensorFamily n q : Matrix _ _ ℂ) * A *
        (tensorFamily n q : Matrix _ _ ℂ).conjTranspose)) =
      (Matrix.trace A / (Fintype.card (Basis d n) : ℂ)) •
        (1 : Matrix (Basis d n) (Basis d n) ℂ) := by
  simp only [uniformWeight, Complex.ofReal_div, Complex.ofReal_one,
    ← Finset.smul_sum, twirl_sum_eq, label_card, Nat.cast_pow,
    Complex.ofReal_pow, Complex.ofReal_natCast]
  have hc : (Fintype.card (Basis d n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
    field_simp
  · simp [Matrix.smul_apply, hij]

def orbitIndex (n : ℕ) : Fin (Fintype.card (Label d n)) ≃ Label d n :=
  (Fintype.equivFin (Label d n)).symm

/-- The complete finite local orbit, with an explicit normalized distribution. -/
def orbitEnsemble (n : ℕ) (outputs : Set (Entropy.DensityMatrix (Basis d n)))
    (ρ : Entropy.DensityMatrix (Basis d n))
    (hclosed : ∀ q : Label d n, ρ.unitaryConjugate (tensorFamily n q) ∈ outputs) :
    StateEnsembles.Ensemble outputs where
  size := Fintype.card (Label d n)
  weight := fun i => uniformWeight n (orbitIndex n i)
  weight_nonneg := fun _ => uniformWeight_nonneg _ _
  weight_sum := by
    exact (Fintype.sum_equiv (orbitIndex (d := d) n)
      (fun i => uniformWeight n (orbitIndex n i)) (uniformWeight n) (fun _ => rfl)).trans
        (uniformWeight_sum n)
  state := fun i => ρ.unitaryConjugate (tensorFamily n (orbitIndex n i))
  state_mem := fun i => hclosed (orbitIndex n i)

theorem orbit_ensemble_average (n : ℕ) (outputs : Set (Entropy.DensityMatrix (Basis d n)))
    (ρ : Entropy.DensityMatrix (Basis d n))
    (hclosed : ∀ q : Label d n, ρ.unitaryConjugate (tensorFamily n q) ∈ outputs) :
    (orbitEnsemble n outputs ρ hclosed).average = Entropy.maximallyMixed (Basis d n) := by
  apply Entropy.DensityMatrix.ext
  change (∑ i : Fin (Fintype.card (Label d n)), (uniformWeight n (orbitIndex n i) : ℂ) •
    (ρ.unitaryConjugate (tensorFamily n (orbitIndex n i))).matrix) = _
  rw [Fintype.sum_equiv (orbitIndex (d := d) n)
    (fun i => (uniformWeight n (orbitIndex n i) : ℂ) •
      (ρ.unitaryConjugate (tensorFamily n (orbitIndex n i))).matrix)
    (fun q => (uniformWeight n q : ℂ) • (ρ.unitaryConjugate (tensorFamily n q)).matrix)
    (fun _ => rfl)]
  change (∑ q : Label d n, (uniformWeight n q : ℂ) •
    ((tensorFamily n q : Matrix _ _ ℂ) * ρ.matrix *
      (tensorFamily n q : Matrix _ _ ℂ).conjTranspose)) = _
  rw [uniform_average_eq, ρ.normalized]
  simp [Entropy.maximallyMixed]

theorem orbit_ensemble_entropy (n : ℕ) (outputs : Set (Entropy.DensityMatrix (Basis d n)))
    (ρ : Entropy.DensityMatrix (Basis d n))
    (hclosed : ∀ q : Label d n, ρ.unitaryConjugate (tensorFamily n q) ∈ outputs)
    (i : Fin (Fintype.card (Label d n))) :
    ((orbitEnsemble n outputs ρ hclosed).state i).vonNeumann = ρ.vonNeumann :=
  ρ.unitaryConjugate_entropy _

/-- Every state whose full local orbit is available gives the exact dimensional lower bound. -/
theorem orbit_information_lower_bound (n : ℕ)
    (outputs : Set (Entropy.DensityMatrix (Basis d n)))
    (ρ : Entropy.DensityMatrix (Basis d n))
    (hclosed : ∀ q : Label d n, ρ.unitaryConjugate (tensorFamily n q) ∈ outputs) :
    Real.log (Fintype.card (Basis d n)) - ρ.vonNeumann ≤ StateEnsembles.quantity outputs :=
  StateEnsembles.orbit_lower_bound (orbitEnsemble n outputs ρ hclosed) ρ
    (orbit_ensemble_average n outputs ρ hclosed) (orbit_ensemble_entropy n outputs ρ hclosed)

theorem orbit_information_lower_bound_log (n : ℕ)
    (outputs : Set (Entropy.DensityMatrix (Basis d n)))
    (ρ : Entropy.DensityMatrix (Basis d n))
    (hclosed : ∀ q : Label d n, ρ.unitaryConjugate (tensorFamily n q) ∈ outputs) :
    ((n + 1 : ℕ) : ℝ) * Real.log d - ρ.vonNeumann ≤ StateEnsembles.quantity outputs := by
  simpa only [Basis, positiveTensorIndex_card, ZMod.card, Nat.cast_pow, Real.log_pow] using
    orbit_information_lower_bound n outputs ρ hclosed

end Nonadditivity.WeylPowersTwirl
