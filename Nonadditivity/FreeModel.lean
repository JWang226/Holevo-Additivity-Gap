/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.AdjointPurity
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The concrete product-free-group reference model

The left regular representation is constructed as actual bounded operators
on the square-summable complex functions on the group. The Collins--Youn
statement below is a precise hypothesis predicate about those operators;
it is not asserted as an axiom or a proved imported theorem.
-/

noncomputable section

namespace Nonadditivity.FreeModel

open scoped BigOperators ENNReal

abbrev Hilbert (G : Type*) := lp (fun _ : G => ℂ) 2

section Reindex

variable {G : Type*}

/-- Reindexing by a genuine bijection preserves square summability. -/
def reindexFunction (e : G ≃ G) (f : Hilbert G) : Hilbert G :=
  ⟨fun g => f (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr (f.property.summable (by norm_num))⟩

@[simp] theorem reindexFunction_apply (e : G ≃ G) (f : Hilbert G) (g : G) :
    reindexFunction e f g = f (e g) := rfl

theorem reindexFunction_norm (e : G ≃ G) (f : Hilbert G) :
    ‖reindexFunction e f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [reindexFunction_apply]
  rw [e.tsum_eq (fun i : G => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)]

/-- The actual Hilbert-space isometry associated with an index permutation. -/
def reindexIsometry (e : G ≃ G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G where
  toFun := reindexFunction e
  invFun := reindexFunction e.symm
  left_inv := by intro f; ext g; simp
  right_inv := by intro f; ext g; simp
  map_add' := by intro f h; ext g; rfl
  map_smul' := by intro c f; ext g; rfl
  norm_map' := reindexFunction_norm e

end Reindex

section Regular

variable {G : Type*} [Group G]

/-- The left regular representation, as an actual bounded complex-linear map. -/
def leftRegular (g : G) : Hilbert G →L[ℂ] Hilbert G :=
  (reindexIsometry (Equiv.mulLeft g⁻¹)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem leftRegular_apply (g : G) (f : Hilbert G) (h : G) :
    leftRegular g f h = f (g⁻¹ * h) := rfl

theorem leftRegular_preserves_norm (g : G) (f : Hilbert G) :
    ‖leftRegular g f‖ = ‖f‖ := (reindexIsometry (Equiv.mulLeft g⁻¹)).norm_map f

@[simp] theorem leftRegular_one :
    leftRegular (1 : G) = ContinuousLinearMap.id ℂ (Hilbert G) := by
  ext f h
  simp

/-- These bounded shifts form the regular representation of the group. -/
theorem leftRegular_mul (g h : G) :
    leftRegular (g * h) = (leftRegular g).comp (leftRegular h) := by
  ext f x
  simp [mul_assoc]

/-- The left regular shifts act on the actual coordinate basis by group multiplication. -/
theorem leftRegular_single [DecidableEq G] (g h : G) :
    leftRegular g (lp.single 2 h (1 : ℂ)) = lp.single 2 (g * h) (1 : ℂ) := by
  classical
  ext x
  simp only [leftRegular_apply, lp.single_apply, Pi.single_apply]
  have heq : g⁻¹ * x = h ↔ x = g * h := by
    constructor
    · intro hh
      have hm := congrArg (fun z => g * z) hh
      simpa [mul_assoc] using hm
    · intro hh
      rw [hh]
      simp
  simp only [heq]

end Regular

abbrev ProductFreeGroup (K n : ℕ) := Fin n → FreeGroup (Fin K)
abbrev Branch (K n : ℕ) := Fin n → Fin K

/-- A branch word contains one canonical generator in each free-group factor. -/
def branchWord {K n : ℕ} (a : Branch K n) : ProductFreeGroup K n :=
  fun j => FreeGroup.of (a j)

/-- The normalized free-group polynomial in the manuscript's adjoint map. -/
def gamma {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) :
    Hilbert (ProductFreeGroup K n) →L[ℂ] Hilbert (ProductFreeGroup K n) :=
  (1 / ((K : ℂ) ^ n)) •
    ∑ a : Branch K n, ∑ b : Branch K n,
      A a b • leftRegular ((branchWord a)⁻¹ * branchWord b)

/-- The comparison norm is the operator norm of an actual regular-representation polynomial. -/
def freeNorm {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) : ℝ := ‖gamma A‖

theorem freeNorm_nonneg {K n : ℕ} (A : Matrix (Branch K n) (Branch K n) ℂ) :
    0 ≤ freeNorm A := norm_nonneg _

/-- The exact normalized Collins--Youn constant. -/
def c (K n : ℕ) : ℝ := Real.sqrt (((1 + 9 / (K : ℝ)) ^ n - 1) / (K : ℝ) ^ n)

theorem c_pos {K n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) : 0 < c K n := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hbase : (1 : ℝ) < 1 + 9 / (K : ℝ) := by
    have h9 : 0 < 9 / (K : ℝ) := by positivity
    linarith
  have hp := one_lt_pow₀ hbase (by omega : n ≠ 0)
  exact Real.sqrt_pos.mpr (div_pos (sub_pos.mpr hp) (pow_pos hKpos n))

theorem c_sq {K n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) :
    c K n ^ 2 = ((1 + 9 / (K : ℝ)) ^ n - 1) / (K : ℝ) ^ n :=
  Real.sq_sqrt ((Real.sqrt_pos.mp (c_pos hK hn)).le)

/-- An explicit external analytic hypothesis about the concrete regular model.
No channel or Holevo conclusion is present in this predicate. -/
def CollinsYounBound (K n : ℕ) : Prop :=
  ∀ A : Matrix (Branch K n) (Branch K n) ℂ, A.trace = 0 →
    freeNorm A ≤ c K n * Nonadditivity.AdjointPurity.hsLength A

theorem freeNorm_le_of_collinsYoun {K n : ℕ} (hCY : CollinsYounBound K n)
    (A : Matrix (Branch K n) (Branch K n) ℂ) (htrace : A.trace = 0)
    (hunit : Nonadditivity.AdjointPurity.hsLength A = 1) :
    freeNorm A ≤ c K n := by
  simpa [hunit] using hCY A htrace

end Nonadditivity.FreeModel
