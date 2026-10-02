/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathChainCount

/-! # Core chains partition the oriented incidences they visit -/
noncomputable section
namespace Nonadditivity.HaarPathGraph.Path
variable {V : Type*} [DecidableEq V] {d m : ℕ} (P : Path V d m)

lemma toCore_drop {l : List (Dart V d)} (h : P.ToCore l) (n : ℕ) (hn : n<l.length) :
    P.ToCore (l.drop n) := by
  induction h generalizing n with
  | last a ha hc =>
      have hn0 : n=0 := by simpa using hn
      subst n
      exact ToCore.last a ha hc
  | cons a b l ha hc hj hr ht ih =>
      cases n with
      | zero => exact ToCore.cons a b l ha hc hj hr ht
      | succ n => simpa using ih n (by simpa using hn)

lemma internalChain_take {l : List (Dart V d)} (h : P.InternalChain l)
    (n : ℕ) (hn : 0<n) : P.InternalChain (l.take n) := by
  induction h generalizing n with
  | single a ha =>
      cases n with
      | zero => omega
      | succ n => simpa using InternalChain.single a ha
  | cons a b l ha hc hj hr ht ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero => exact InternalChain.single a ha
          | succ n =>
              simpa using InternalChain.cons a b (l.take n) ha hc hj hr (ih (n+1) (by omega))

lemma toCore_mem {l : List (Dart V d)} (h : P.ToCore l) {q : Dart V d} (hq : q ∈ l) :
    q ∈ P.darts := by
  induction h with
  | last a ha hc => simpa using (List.mem_singleton.mp hq) ▸ ha
  | cons a b l ha hc hj hr ht ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ha
      · exact ih hq

/-- A terminated deterministic chain never revisits the same oriented dart. -/
theorem toCore_nodup {l : List (Dart V d)} (h : P.ToCore l) : l.Nodup := by
  induction h with
  | last a ha hc => simp
  | cons a b l ha hc hj hr ht ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih⟩
      intro hmem
      obtain ⟨p,s,he⟩ := List.mem_iff_append.mp hmem
      have hs : P.ToCore (a::s) := by
        have hd := P.toCore_drop ht p.length (by rw [he]; simp)
        simpa [he] using hd
      have heq := P.toCore_unique (ToCore.cons a b l ha hc hj hr ht) hs rfl
      have hlen := congrArg List.length heq
      rw [he] at hlen
      simp only [List.length_cons,List.length_append] at hlen
      omega

/-- The suffix beginning at any occurrence of a dart is its unique route to
the next core vertex. -/
lemma suffix_toCore (c : P.CoreChain) (p : List (Dart V d)) (q : Dart V d)
    (s : List (Dart V d)) (he : c.val=p++q::s) : P.ToCore (q::s) := by
  have hd := P.toCore_drop c.property.1 p.length (by rw [he]; simp)
  simpa [he] using hd

/-- Reversing the prefix through a dart reaches the preceding core vertex. -/
lemma reversed_prefix_toCore (c : P.CoreChain) (p : List (Dart V d)) (q : Dart V d)
    (s : List (Dart V d)) (he : c.val=p++q::s) :
    P.ToCore ((p++[q]).reverse.map reverse) := by
  have hi : P.InternalChain (p++[q]) := by
    have ht := P.internalChain_take c.property.1.internalChain (p.length+1) (by omega)
    simpa [he,List.take_add] using ht
  have hr := P.internalChain_reverse hi
  apply P.internalChain_toCore hr
  have hc : source (c.val.head (P.toCore_nonempty c.property.1)) ∈ P.coreVertices := by
    obtain ⟨a,t,hat,hc⟩ := c.property.2
    simpa [hat] using hc
  cases p with
  | nil => simpa [he] using hc
  | cons a p => simpa [he,List.getLast_map,List.getLast_reverse] using hc

/-- Sharing an oriented incidence identifies the entire maximal core chain.
The forward and backward continuations are both forced. -/
theorem coreChain_eq_of_common_dart (c c' : P.CoreChain) {q : Dart V d}
    (hq : q ∈ c.val) (hq' : q ∈ c'.val) : c=c' := by
  obtain ⟨p,s,he⟩ := List.mem_iff_append.mp hq
  obtain ⟨p',s',he'⟩ := List.mem_iff_append.mp hq'
  have hs : s=s' := (List.cons.inj
    (P.toCore_unique (P.suffix_toCore c p q s he) (P.suffix_toCore c' p' q s' he') rfl)).2
  have hb := P.toCore_unique (P.reversed_prefix_toCore c p q s he)
    (P.reversed_prefix_toCore c' p' q s' he') (by simp)
  have hp : p=p' := by
    have hh := congrArg (fun l : List (Dart V d) => l.reverse.map reverse) hb
    simp only [List.map_reverse,List.reverse_reverse,List.map_map,Function.comp_def,
      reverse_reverse,List.map_id_fun'] at hh
    exact List.append_cancel_right hh
  apply Subtype.ext
  simp [he,he',hp,hs]

/-- A chain cannot traverse an edge in both orientations. -/
theorem coreChain_not_both_orientations (c : P.CoreChain) {q : Dart V d} (hq : q ∈ c.val) :
    reverse q ∉ c.val := by
  intro hrev
  have hmem : q ∈ (P.coreChainReverse c).val := by
    change q ∈ c.val.reverse.map reverse
    exact List.mem_map.mpr ⟨reverse q,List.mem_reverse.mpr hrev,reverse_reverse q⟩
  exact P.coreChainReverse_ne_self c (P.coreChain_eq_of_common_dart c (P.coreChainReverse c) hq hmem).symm

end Nonadditivity.HaarPathGraph.Path
