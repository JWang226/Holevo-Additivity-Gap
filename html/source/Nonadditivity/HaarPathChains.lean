/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathGraph
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Chain

/-! # Deterministic chains between core vertices

A reduced chain cannot choose a branch before reaching a core vertex: at
an internal vertex of degree two the incoming dart excludes one incidence
and forces the next dart. This file formalizes that uniqueness for actual
colored graph darts, rather than assuming a chain reconstruction oracle.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph
open HaarPathProfiles
variable {V : Type*} {d m : ℕ}

@[simp] theorem reverse_reverse (q : Dart V d) : reverse (reverse q) = q := by
  simp [reverse]

theorem reverse_ne_self (q : Dart V d) : reverse q ≠ q := by
  obtain ⟨e,b⟩ := q
  cases b <;> simp [reverse]

/-- A nonempty reduced dart word cannot equal its reverse with all
orientations reversed. The middle dart or middle pair would backtrack. -/
theorem reduced_ne_reverse (l : List (Dart V d)) (hne : l ≠ [])
    (hred : l.IsChain fun a b => b ≠ reverse a) : l.reverse.map reverse ≠ l := by
  induction l using List.bidirectionalRecOn with
  | H0 => exact (hne rfl).elim
  | H1 a =>
      simpa using reverse_ne_self a
  | Hn a l b ih =>
      intro he
      have hba : reverse b=a := by
        simpa using congrArg List.head? he
      have hab : reverse a=b := by rw [←hba,reverse_reverse]
      have he' : l.reverse.map reverse=l := by
        simp only [List.reverse_cons,List.reverse_append,
          List.map_append,List.map_cons,List.map_nil,
          hba,hab] at he
        exact List.append_cancel_right (List.cons.inj he).2
      by_cases hl : l=[]
      · subst l
        have hr : b ≠ reverse a := by simpa using hred
        exact hr hab.symm
      · exact ih hl hred.tail.left_of_append he'

namespace Path
variable [DecidableEq V] (P : Path V d m)

lemma reverse_mem {q : Dart V d} (hq : q ∈ P.darts) : reverse q ∈ P.darts := by
  simpa only [darts, Finset.mem_product, Finset.mem_univ, and_true, reverse] using hq

/-- The degree-two condition uniquely determines the continuation away from
an incoming incidence. -/
theorem next_dart_unique {a b c : Dart V d}
    (ha : a ∈ P.darts) (hb : b ∈ P.darts) (hc : c ∈ P.darts)
    (hcore : source a ∉ P.coreVertices)
    (hab : source a=source b) (hac : source a=source c)
    (hba : b ≠ a) (hca : c ≠ a) : b=c := by
  have hv := P.source_mem ha
  have hdeg : P.degree (source a)=2 := by
    by_contra h
    exact hcore (Finset.mem_filter.mpr ⟨hv,Or.inr h⟩)
  let S := P.darts.filter fun q => source q=source a
  have hsub : {a,b} ⊆ S := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨ha,rfl⟩
    · rw [Finset.mem_singleton] at hq
      subst q
      exact Finset.mem_filter.mpr ⟨hb,hab.symm⟩
  have heq : {a,b}=S := Finset.eq_of_subset_of_card_le hsub (by
    change P.degree (source a) ≤ _
    simp [hdeg,Ne.symm hba])
  have hcm : c ∈ ({a,b} : Finset (Dart V d)) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨hc,hac.symm⟩
  exact (by simpa [hca] using hcm : c=b).symm

/-- A chain stopped on first arrival at a core vertex. Its initial vertex may
be arbitrary; the complete chains later require a core initial vertex too. -/
inductive ToCore : List (Dart V d) → Prop
  | last (a : Dart V d) (ha : a ∈ P.darts)
      (hcore : source (reverse a) ∈ P.coreVertices) : ToCore [a]
  | cons (a b : Dart V d) (l : List (Dart V d))
      (ha : a ∈ P.darts) (hcore : source (reverse a) ∉ P.coreVertices)
      (hjoin : source (reverse a)=source b) (hred : b ≠ reverse a)
      (htail : ToCore (b::l)) : ToCore (a::b::l)

lemma toCore_nonempty {l : List (Dart V d)} (h : P.ToCore l) : l ≠ [] := by
  cases h <;> simp

lemma toCore_head_mem {a : Dart V d} {l : List (Dart V d)} (h : P.ToCore (a::l)) :
    a ∈ P.darts := by cases h <;> assumption

/-- Exact deterministic reconstruction from the initial dart. -/
theorem toCore_unique {l : List (Dart V d)} (h : P.ToCore l) :
    ∀ {l' : List (Dart V d)}, P.ToCore l' → l.head?=l'.head? → l=l' := by
  induction h with
  | last a ha hcore =>
      intro l' h' hhead
      cases h' with
      | last b hb hbcore => simpa using hhead
      | cons b c l hb hbcore hjoin hred htail =>
          have hab : a=b := by simpa using hhead
          subst b
          exact (hbcore hcore).elim
  | cons a b l ha hcore hjoin hred htail ih =>
      intro l' h' hhead
      cases h' with
      | last c hc hccore =>
          have hac : a=c := by simpa using hhead
          subst c
          exact (hcore hccore).elim
      | cons c e s hc hccore hcjoin hcred hctail =>
          have hac : a=c := by simpa using hhead
          subst c
          have hbe : b=e := P.next_dart_unique (P.reverse_mem ha)
            (P.toCore_head_mem htail) (P.toCore_head_mem hctail) hcore hjoin hcjoin hred hcred
          subst e
          exact congrArg (List.cons a) (ih hctail rfl)

/-- The same reduced chains before specifying their terminal vertex. -/
inductive InternalChain : List (Dart V d) → Prop
  | single (a : Dart V d) (ha : a ∈ P.darts) : InternalChain [a]
  | cons (a b : Dart V d) (l : List (Dart V d))
      (ha : a ∈ P.darts) (hcore : source (reverse a) ∉ P.coreVertices)
      (hjoin : source (reverse a)=source b) (hred : b ≠ reverse a)
      (htail : InternalChain (b::l)) : InternalChain (a::b::l)

lemma internalChain_nonempty {l : List (Dart V d)} (h : P.InternalChain l) : l ≠ [] := by
  cases h <;> simp

lemma ToCore.internalChain {l : List (Dart V d)} (h : P.ToCore l) : P.InternalChain l := by
  induction h with
  | last a ha hc => exact InternalChain.single a ha
  | cons a b l ha hc hj hr ht ih => exact InternalChain.cons a b l ha hc hj hr ih

lemma toCore_last_core {l : List (Dart V d)} (h : P.ToCore l) :
    source (reverse (l.getLast (P.toCore_nonempty h))) ∈ P.coreVertices := by
  induction h with
  | last a ha hc => simpa using hc
  | cons a b l ha hc hj hr ht ih => simpa using ih

lemma internalChain_toCore {l : List (Dart V d)} (h : P.InternalChain l)
    (hc : source (reverse (l.getLast (P.internalChain_nonempty h))) ∈ P.coreVertices) :
    P.ToCore l := by
  induction h with
  | single a ha => exact ToCore.last a ha (by simpa using hc)
  | cons a b l ha hcore hj hr ht ih =>
      exact ToCore.cons a b l ha hcore hj hr (ih (by simpa using hc))

/-- Appending one edge checks only the old final incidence. -/
theorem internalChain_append {l : List (Dart V d)} (h : P.InternalChain l)
    (b : Dart V d) (hb : b ∈ P.darts)
    (hcore : source (reverse (l.getLast (P.internalChain_nonempty h))) ∉ P.coreVertices)
    (hjoin : source (reverse (l.getLast (P.internalChain_nonempty h)))=source b)
    (hred : b ≠ reverse (l.getLast (P.internalChain_nonempty h))) :
    P.InternalChain (l++[b]) := by
  induction h with
  | single a ha =>
      exact InternalChain.cons a b [] ha (by simpa using hcore)
        (by simpa using hjoin) (by simpa using hred) (InternalChain.single b hb)
  | cons a c l ha hc hj hr ht ih =>
      exact InternalChain.cons a c (l++[b]) ha hc hj hr
        (ih (by simpa using hcore) (by simpa using hjoin) (by simpa using hred))

/-- A reversed internal chain is still reduced and has the same internal
vertices. This proves reversal compatibility for actual graph chains. -/
theorem internalChain_reverse {l : List (Dart V d)} (h : P.InternalChain l) :
    P.InternalChain (l.reverse.map reverse) := by
  induction h with
  | single a ha =>
      exact InternalChain.single (reverse a) (P.reverse_mem ha)
  | cons a b l ha hc hj hr ht ih =>
      rw [List.reverse_cons, List.map_append, List.map_singleton]
      apply P.internalChain_append ih (reverse a) (P.reverse_mem ha)
      · simpa [List.getLast_map, List.getLast_reverse, reverse_reverse, ←hj] using hc
      · simpa [List.getLast_map, List.getLast_reverse, reverse_reverse] using hj.symm
      · simpa [List.getLast_map, List.getLast_reverse, reverse_reverse] using Ne.symm hr

/-- Chains that both start and end at core vertices. -/
def CoreChain := {l : List (Dart V d) // P.ToCore l ∧
  ∃ a t, l=a::t ∧ source a ∈ P.coreVertices}

/-- Literal incidences at core vertices. -/
def coreDarts : Finset (Dart V d) := P.darts.filter fun q => source q ∈ P.coreVertices

/-- Encoding by the first incidence proves finiteness without assuming any
bound on the length of a chain. -/
def coreChainEncode (c : P.CoreChain) : {q // q ∈ P.coreDarts} := by
  let a := c.val.head (P.toCore_nonempty c.property.1)
  refine ⟨a,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
  · obtain ⟨b,t,he,hcore⟩ := c.property.2
    simpa [a,he] using P.toCore_head_mem (he ▸ c.property.1)
  · obtain ⟨b,t,he,hcore⟩ := c.property.2
    simpa [a,he] using hcore

theorem coreChainEncode_injective : Function.Injective P.coreChainEncode := by
  intro c c' h
  apply Subtype.ext
  apply P.toCore_unique c.property.1 c'.property.1
  have hh := congrArg Subtype.val h
  change c.val.head (P.toCore_nonempty c.property.1) =
    c'.val.head (P.toCore_nonempty c'.property.1) at hh
  rw [List.head?_eq_some_head (P.toCore_nonempty c.property.1),
    List.head?_eq_some_head (P.toCore_nonempty c'.property.1), hh]

instance coreChainFintype : Fintype P.CoreChain :=
  Fintype.ofInjective P.coreChainEncode P.coreChainEncode_injective

lemma internalChain_isChain {l : List (Dart V d)} (h : P.InternalChain l) :
    l.IsChain fun a b => b ≠ reverse a := by
  induction h with
  | single a ha => simp
  | cons a b l ha hc hj hr ht ih => exact List.isChain_cons_cons.mpr ⟨hr,ih⟩

/-- Actual reversal of a complete core chain. -/
def coreChainReverse (c : P.CoreChain) : P.CoreChain := by
  let l := c.val.reverse.map reverse
  have hi : P.InternalChain l := P.internalChain_reverse c.property.1.internalChain
  have hstart : source (c.val.head (P.toCore_nonempty c.property.1)) ∈ P.coreVertices := by
    obtain ⟨a,t,he,hc⟩ := c.property.2
    simpa [he] using hc
  have ht : P.ToCore l := P.internalChain_toCore hi (by
    simpa [l,List.getLast_map,List.getLast_reverse] using hstart)
  refine ⟨l,ht,⟨l.head (P.toCore_nonempty ht),l.tail,
    (List.cons_head_tail (P.toCore_nonempty ht)).symm,?_⟩⟩
  simpa [l,List.head_map,List.head_reverse] using P.toCore_last_core c.property.1

@[simp] theorem coreChainReverse_involutive (c : P.CoreChain) :
    P.coreChainReverse (P.coreChainReverse c)=c := by
  apply Subtype.ext
  change (c.val.reverse.map reverse).reverse.map reverse=c.val
  simp [List.map_reverse,List.map_map,Function.comp_def]

theorem coreChainReverse_ne_self (c : P.CoreChain) : P.coreChainReverse c ≠ c := by
  intro h
  have he := congrArg Subtype.val h
  exact reduced_ne_reverse c.val (P.toCore_nonempty c.property.1)
    (P.internalChain_isChain c.property.1.internalChain) he

/-- Every actual chain has a different initial core incidence. -/
theorem card_coreChain_le_coreDarts : Fintype.card P.CoreChain ≤ P.coreDarts.card := by
  simpa using Fintype.card_le_of_injective P.coreChainEncode P.coreChainEncode_injective

end Path
end Nonadditivity.HaarPathGraph
