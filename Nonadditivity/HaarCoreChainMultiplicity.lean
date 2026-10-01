/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathTransport

/-! # Exact multiplicities along a suppressed chain -/
noncomputable section
attribute [local instance 2000] instBEqOfDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

/-- A dart in one oriented core chain occurs once in that chain and in no
other oriented core chain. -/
theorem coreChain_count_dart (c c' : P.CoreChain) {q : Dart V d} (hq : q ∈ c.val) :
    c'.val.count q = if c'=c then 1 else 0 := by
  classical
  by_cases hc : c'=c
  · subst c'
    simp only [ite_true]
    exact List.count_eq_one_of_mem (P.toCore_nodup c.property.1) hq
  · rw [if_neg hc]
    apply List.count_eq_zero.mpr
    intro hq'
    exact hc (P.coreChain_eq_of_common_dart c' c hq' hq)

/-- All darts of one oriented compressed edge have exactly the same number
of occurrences in the original path. -/
theorem traversal_count_eq_chain_count (cs : List P.CoreChain)
    (hcs : (cs.map Subtype.val).flatten=P.traversalList)
    (c : P.CoreChain) {q : Dart V d} (hq : q ∈ c.val) :
    P.traversalList.count q=cs.count c := by
  classical
  rw [←hcs]
  clear hcs
  induction cs with
  | nil => simp
  | cons c' cs ih =>
    simp only [List.map_cons,List.flatten_cons,List.count_append]
    rw [P.coreChain_count_dart c c' hq]
    have ht : (List.map Subtype.val cs).flatten.count q=cs.count c := by
      apply ih
    rw [ht]
    by_cases hc : c'=c <;> simp [hc,Nat.add_comm]

/-- Any two positions along a chain carry identical directed multiplicity. -/
theorem traversal_count_constant_on_chain (hm : 0 < m) (c : P.CoreChain)
    {q r : Dart V d} (hq : q ∈ c.val) (hr : r ∈ c.val) :
    P.traversalList.count q=P.traversalList.count r := by
  obtain ⟨cs,hcs⟩ := P.exists_traversal_chain_decomposition hm
  rw [P.traversal_count_eq_chain_count cs hcs c hq,
    P.traversal_count_eq_chain_count cs hcs c hr]

end Nonadditivity.HaarPathGraph.Path
