/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChains

/-! # Actual decomposition into degree-two core chains -/
noncomputable section
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

def Step (a b : Dart V d) : Prop := source (reverse a)=source b ∧ b ≠ reverse a

/-- Stop at the first core vertex. The returned suffix begins at a core
vertex whenever it is nonempty. -/
theorem exists_initial_chain (a : Dart V d) (l : List (Dart V d))
    (hmem : ∀ q ∈ a::l, q ∈ P.darts) (hstep : (a::l).IsChain Step)
    (hend : source (reverse ((a::l).getLast (by simp))) ∈ P.coreVertices) :
    ∃ t s, l=t++s ∧ P.ToCore (a::t) ∧
      ∀ b r, s=b::r → source b ∈ P.coreVertices := by
  induction l generalizing a with
  | nil =>
      refine ⟨[],[],rfl,ToCore.last a (hmem a (by simp)) (by simpa using hend),?_⟩
      intro b r he
      cases he
  | cons b l ih =>
      have hpair := (List.isChain_cons_cons.mp hstep).1
      have htail := (List.isChain_cons_cons.mp hstep).2
      by_cases hc : source (reverse a) ∈ P.coreVertices
      · refine ⟨[],b::l,rfl,ToCore.last a (hmem a (by simp)) hc,?_⟩
        intro c r he
        have hbc : b=c := (List.cons.inj he).1
        rw [←hbc,←hpair.1]
        exact hc
      · obtain ⟨t,s,he,ht,hs⟩ := ih b
          (fun q hq => hmem q (List.mem_cons_of_mem a hq))
          htail (by simpa using hend)
        refine ⟨b::t,s,?_,ToCore.cons a b t (hmem a (by simp)) hc hpair.1 hpair.2 ht,hs⟩
        simp [he]

/-- Any reduced graph walk with endpoints at core vertices is a concatenation
of the actual first-hit chains. No decomposition hypothesis is supplied. -/
theorem exists_chain_decomposition (l : List (Dart V d)) (hne : l ≠ [])
    (hmem : ∀ q ∈ l, q ∈ P.darts) (hstep : l.IsChain Step)
    (hstart : source (l.head hne) ∈ P.coreVertices)
    (hend : source (reverse (l.getLast hne)) ∈ P.coreVertices) :
    ∃ cs : List P.CoreChain, (cs.map Subtype.val).flatten = l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
      cases l with
      | nil => exact (hne rfl).elim
      | cons a l =>
          obtain ⟨t,s,he,ht,hs⟩ := P.exists_initial_chain a l hmem hstep hend
          let c : P.CoreChain := ⟨a::t,ht,⟨a,t,rfl,by simpa using hstart⟩⟩
          have hefull : a::l=(a::t)++s := by simp [he]
          by_cases hsn : s=[]
          · refine ⟨[c],?_⟩
            change (a::t)++[]=a::l
            rw [List.append_nil]
            simpa only [hsn,List.append_nil] using hefull.symm
          · have hslen : s.length < n := by
              rw [←hn,hefull,List.length_append,List.length_cons]
              omega
            have hsmem : ∀ q ∈ s, q ∈ P.darts := by
              intro q hq
              apply hmem q
              rw [hefull]
              exact List.mem_append_right _ hq
            have hsstep : s.IsChain Step := by
              rw [hefull] at hstep
              exact hstep.right_of_append
            have hsstart : source (s.head hsn) ∈ P.coreVertices :=
              hs _ _ (List.cons_head_tail hsn).symm
            have hsend : source (reverse (s.getLast hsn)) ∈ P.coreVertices := by
              simpa only [hefull,List.getLast_append_of_ne_nil _ hsn] using hend
            obtain ⟨cs,hcs⟩ := ih s.length hslen s hsn hsmem hsstep hsstart hsend rfl
            refine ⟨c::cs,?_⟩
            change (a::t)++(cs.map Subtype.val).flatten=a::l
            rw [hcs]
            exact hefull.symm

/-- The literal oriented dart sequence of the original path. -/
def traversalList : List (Dart V d) := List.ofFn P.traversal

omit [DecidableEq V] in
@[simp] theorem traversalList_length : P.traversalList.length=m := by simp [traversalList]

omit [DecidableEq V] in
theorem traversalList_step : P.traversalList.IsChain Step := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hi' : i+1<m := by simpa [traversalList] using hi
  simp only [traversalList,List.getElem_ofFn]
  constructor
  · simp only [traversal,source_reverse_dart,source_dart]
    rfl
  · intro h
    have hc := congrArg color h
    simp only [traversal,color_dart,color_reverse_dart] at hc
    exact P.reduced _ _ rfl hc

/-- The original nonempty reduced path, with no extra graph hypotheses,
admits a successive core-chain occurrence list. -/
theorem exists_traversal_chain_decomposition (hm : 0 < m) :
    ∃ cs : List P.CoreChain, (cs.map Subtype.val).flatten=P.traversalList := by
  have hne : P.traversalList ≠ [] := by
    intro he
    have h := congrArg List.length he
    simp only [traversalList_length,List.length_nil] at h
    omega
  have hroot : P.vertex 0 ∈ P.coreVertices :=
    Finset.mem_filter.mpr ⟨P.start_mem ⟨0,hm⟩,Or.inl rfl⟩
  apply P.exists_chain_decomposition P.traversalList hne
  · intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact P.traversal_mem i
  · exact P.traversalList_step
  · simpa [traversalList,List.head_ofFn,traversal] using hroot
  · have hlast : (⟨m-1,Nat.sub_one_lt (by omega)⟩ : Fin m).succ=Fin.last m := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      omega
    simpa [traversalList,List.getLast_ofFn,traversal,hlast,P.closed] using hroot

end Nonadditivity.HaarPathGraph.Path
