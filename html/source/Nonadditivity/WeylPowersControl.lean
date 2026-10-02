/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.ChannelTensorControl
import Nonadditivity.ChannelReindex
import Nonadditivity.ConjugateChannel

/-!
# Tensor products of measured unitary extensions

These are equalities of the actual Kraus tensors, including their measured
classical registers. All input and environment permutations are explicit.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Entropy
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

variable {ι ο κ ζ μ ν η ξ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype ζ] [DecidableEq ζ]
variable [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
variable [Fintype η] [Fintype ξ] [DecidableEq ξ]

omit [DecidableEq ο] in
/-- A measured Kraus matrix has one nonzero classical input block. -/
theorem controlled_kraus_apply (T : ζ → KrausChannel ι ο κ)
    (z : ζ) (k : κ) (a : ο) (w : ζ) (b : ι) :
    (controlled T).kraus (z,k) a (w,b) = if w=z then (T z).kraus k a b else 0 := by
  simp [controlled, Matrix.mul_apply, selector, Prod.mk.injEq, ite_and]

/-- Concrete coefficient formula for a measured output-unitary extension. -/
theorem covariantExtension_kraus_apply (T : KrausChannel ι ο κ)
    (U : ζ → unitary (Matrix ο ο ℂ))
    (z : ζ) (k : κ) (a : ο) (w : ζ) (b : ι) :
    (T.covariantExtension U).kraus (z,k) a (w,b) =
      if w=z then ((U z : Matrix ο ο ℂ) * T.kraus k) a b else 0 :=
  controlled_kraus_apply _ _ _ _ _ _

/-- Tensoring the channels that conjugate outputs is exactly tensoring their
unitaries, already at the level of Kraus operators. -/
theorem outputUnitary_tensor_eq (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (U : unitary (Matrix ο ο ℂ)) (V : unitary (Matrix ν ν ℂ)) :
    (T.outputUnitary U).tensor (S.outputUnitary V) =
      (T.tensor S).outputUnitary (tensorUnitary U V) := by
  apply ext
  funext k
  exact Matrix.mul_kronecker_mul _ _ _ _

omit [DecidableEq ο] [DecidableEq ν] in
/-- The tensor of two controlled channels measures the pair of classical labels.
The index shuffle groups both labels before both quantum inputs. -/
theorem controlled_tensor_reindex (T : ζ → KrausChannel ι ο κ)
    (S : ξ → KrausChannel μ ν η) :
    ((((controlled T).tensor (controlled S)).reindex
      (Equiv.prodProdProdComm ζ ι ξ μ) (Equiv.refl (ο × ν))).reindexKraus
      (Equiv.prodProdProdComm ζ κ ξ η)) =
      controlled (fun z : ζ × ξ => (T z.1).tensor (S z.2)) := by
  apply ext
  funext k
  rcases k with ⟨⟨z,w⟩,⟨k,l⟩⟩
  ext a b
  rcases a with ⟨a,c⟩
  rcases b with ⟨⟨z',w'⟩,⟨b,d⟩⟩
  change (controlled T).kraus (z,k) a (z',b) *
      (controlled S).kraus (w,l) c (w',d) = _
  rw [controlled_kraus_apply, controlled_kraus_apply, controlled_kraus_apply]
  simp only [tensor, Matrix.kroneckerMap_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Two covariant extensions are the covariant extension of the tensor channel,
with independent local output unitaries and an explicitly regrouped register. -/
theorem covariantExtension_tensor_reindex (T : KrausChannel ι ο κ)
    (S : KrausChannel μ ν η) (U : ζ → unitary (Matrix ο ο ℂ))
    (V : ξ → unitary (Matrix ν ν ℂ)) :
    ((((T.covariantExtension U).tensor (S.covariantExtension V)).reindex
      (Equiv.prodProdProdComm ζ ι ξ μ) (Equiv.refl (ο × ν))).reindexKraus
      (Equiv.prodProdProdComm ζ κ ξ η)) =
      (T.tensor S).covariantExtension
        (fun z : ζ × ξ => tensorUnitary (U z.1) (V z.2)) := by
  simp only [covariantExtension, controlled_tensor_reindex, outputUnitary_tensor_eq]

end Nonadditivity.Channels.KrausChannel
