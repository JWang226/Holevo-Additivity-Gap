/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.NoncommutativeCSEndpointSkeleton

/-! # Singleton labels of closed endpoint skeletons

The endpoint compiler's singleton nodes are exactly the labels occurring
once in the literal visit word. The proof tracks the actual active layout;
it does not assume that the skeleton was built by a particular compiler.
-/
noncomputable section
namespace Nonadditivity.NoncommutativeCS.EndpointSkeleton
variable {I : Type*}

def singletonLabels {m n : ℕ} {a : Fin m → I} {b : Fin n → I} :
    EndpointSkeleton I a b → List I
  | .done _ => []
  | .first _ P => P.singletonLabels
  | .last _ P => P.singletonLabels
  | .middle _ P => P.singletonLabels
  | .singleton i P => i :: P.singletonLabels

theorem singletonLabels_sublist_profileLabels {m n : ℕ}
    {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b) :
    P.singletonLabels.Sublist P.profileLabels := by
  induction P with
  | done => simp [singletonLabels, profileLabels]
  | first i P ih => exact ih.cons _
  | last p P ih => exact ih
  | middle visits P ih => exact ih
  | singleton i P ih => exact ih.cons_cons _

theorem singletonLabels_nodup {m n : ℕ}
    {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b)
    (hP : P.profileLabels.Nodup) : P.singletonLabels.Nodup :=
  hP.sublist P.singletonLabels_sublist_profileLabels

/-- A visit uses an initially active label or a label introduced by the
skeleton itself. -/
theorem mem_word_range_or_profile {m n : ℕ}
    {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b) (i : I) :
    i ∈ P.word → i ∈ Set.range a ∨ i ∈ P.profileLabels := by
  induction P with
  | done => simp [word]
  | @first m n a b j P ih =>
      intro hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact Or.inr (List.mem_cons_self)
      · rcases ih hi with hi | hi
        · rcases (show i=j ∨ i ∈ Set.range a by simpa [Fin.range_cons] using hi) with rfl | hi
          · exact Or.inr (List.mem_cons_self)
          · exact Or.inl hi
        · exact Or.inr (List.mem_cons_of_mem _ hi)
  | @last m n a b p P ih =>
      intro hi
      rcases List.mem_cons.mp hi with hi | hi
      · exact Or.inl ⟨p,hi.symm⟩
      · rcases ih hi with ⟨q,hq⟩ | hi
        · exact Or.inl ⟨p.succAbove q,hq⟩
        · exact Or.inr hi
  | @middle m n a b visits P ih =>
      intro hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
        exact Or.inl ⟨p,rfl⟩
      · exact ih hi
  | singleton j P ih =>
      intro hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact Or.inr List.mem_cons_self
      · exact (ih hi).imp_right (List.mem_cons_of_mem _)

/-- An initially active label is eventually visited or remains in the final
layout. This is the finite register conservation property. -/
theorem mem_initial_range_word_or_final {m n : ℕ}
    {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b) (i : I) :
    i ∈ Set.range a → i ∈ P.word ∨ i ∈ Set.range b := by
  induction P with
  | done => exact Or.inr
  | @first m n a b j P ih =>
      intro hi
      have hi' : i ∈ Set.range (Fin.cons j a) := by
        simpa [Fin.range_cons] using (Or.inr hi : i=j ∨ i ∈ Set.range a)
      exact (ih hi').imp_left (List.mem_cons_of_mem _)
  | @last m n a b p P ih =>
      rintro ⟨q,rfl⟩
      by_cases hq : q=p
      · subst q
        exact Or.inl List.mem_cons_self
      · obtain ⟨r,hr⟩ := Fin.exists_succAbove_eq hq
        have hi : a q ∈ Set.range (p.removeNth a) := ⟨r,congrArg a hr⟩
        exact (ih hi).imp_left (List.mem_cons_of_mem _)
  | middle visits P ih =>
      intro hi
      exact (ih hi).imp_left (List.mem_append_right _)
  | singleton j P ih =>
      intro hi
      exact (ih hi).imp_left (List.mem_cons_of_mem _)

theorem mem_word_of_initial_closed {m n : ℕ}
    {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b)
    (hend : ∀ q : Fin n, False) (i : I) (hi : i ∈ Set.range a) :
    i ∈ P.word := by
  rcases P.mem_initial_range_word_or_final i hi with hi | ⟨q,hq⟩
  · exact hi
  · exact (hend q).elim

/-- Generic induction invariant: a singleton node accounts exactly for a
single visit of a label which was not active at the start. -/
theorem mem_singletonLabels_iff_count_eq_one_not_initial [DecidableEq I]
    {m n : ℕ} {a : Fin m → I} {b : Fin n → I} (P : EndpointSkeleton I a b)
    (hend : ∀ q : Fin n, False) (ha : Function.Injective a)
    (hP : P.profileLabels.Nodup)
    (hdisj : ∀ i ∈ P.profileLabels, i ∉ Set.range a) (i : I) :
    i ∈ P.singletonLabels ↔ P.word.count i=1 ∧ i ∉ Set.range a := by
  induction P with
  | done => simp [singletonLabels, word]
  | @first m n a b j P ih =>
      obtain ⟨hj,hP⟩ := List.nodup_cons.mp hP
      have hja : j ∉ Set.range a := hdisj j List.mem_cons_self
      have hd : ∀ k ∈ P.profileLabels, k ∉ Set.range (Fin.cons j a) := by
        intro k hk
        simp only [Fin.range_cons, Set.mem_insert_iff, not_or]
        exact ⟨fun he => hj (he ▸ hk), hdisj k (List.mem_cons_of_mem _ hk)⟩
      have hh := ih hend (Fin.cons_injective_of_injective hja ha) hP hd
      by_cases hij : i=j
      · subst i
        have hnot : j ∉ P.singletonLabels := fun h => hj
          (P.singletonLabels_sublist_profileLabels.subset h)
        have hpos : 0 < P.word.count j := List.count_pos_iff.mpr
          (P.mem_word_of_initial_closed hend j ⟨0,by simp⟩)
        simp only [singletonLabels, word, hnot, List.count_cons_self, false_iff, not_and]
        omega
      · simpa [singletonLabels, word, List.count_cons, hij, Ne.symm hij,
          Fin.range_cons] using hh
  | @last m n a b p P ih =>
      have hd : ∀ k ∈ P.profileLabels, k ∉ Set.range (p.removeNth a) := by
        intro k hk ⟨q,hq⟩
        exact hdisj k hk ⟨p.succAbove q,hq⟩
      have hh := ih hend (ha.comp Fin.succAbove_right_injective) hP hd
      by_cases hi : i=a p
      · subst i
        have hnot : a p ∉ P.singletonLabels := fun h =>
          hdisj _ (P.singletonLabels_sublist_profileLabels.subset h) ⟨p,rfl⟩
        simp [singletonLabels, word, hnot, show a p ∈ Set.range a from ⟨p,rfl⟩]
      · simpa [singletonLabels, word, List.count_cons, hi, Ne.symm hi,
          mem_range_removeNth ha p, not_and_or] using hh
  | @middle m n a b visits P ih =>
      have hh := ih hend ha hP hdisj
      by_cases hi : i ∈ Set.range a
      · have hnot : i ∉ P.singletonLabels := fun h =>
          hdisj _ (P.singletonLabels_sublist_profileLabels.subset h) hi
        simp [singletonLabels, hnot, hi]
      · have hm : i ∉ visits.map a := by
          rintro hi'
          obtain ⟨p,hp,hp'⟩ := List.mem_map.mp hi'
          exact hi ⟨p,hp'⟩
        simpa [singletonLabels, word, List.count_append,
          List.count_eq_zero.mpr hm, hi] using hh
  | @singleton m n a b j P ih =>
      obtain ⟨hj,hP⟩ := List.nodup_cons.mp hP
      have hd : ∀ k ∈ P.profileLabels, k ∉ Set.range a :=
        fun k hk => hdisj k (List.mem_cons_of_mem _ hk)
      have hh := ih hend ha hP hd
      have hja : j ∉ Set.range a := hdisj j List.mem_cons_self
      by_cases hij : i=j
      · subst i
        have hw : j ∉ P.word := fun h =>
          (P.mem_word_range_or_profile j h).elim hja hj
        simp [singletonLabels, word, List.count_eq_zero.mpr hw, hja]
      · simpa [singletonLabels, word, List.count_cons, hij, Ne.symm hij] using hh

theorem closed_mem_singletonLabels_iff_count_eq_one [DecidableEq I]
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.profileLabels.Nodup) (i : I) :
    i ∈ P.singletonLabels ↔ P.word.count i=1 := by
  simpa using P.mem_singletonLabels_iff_count_eq_one_not_initial Fin.elim0
    (Function.injective_of_subsingleton _) hP (by simp) i

theorem closed_singletonLabels_toFinset [DecidableEq I]
    (P : EndpointSkeleton I (Fin.elim0 : Fin 0 → I) (Fin.elim0 : Fin 0 → I))
    (hP : P.profileLabels.Nodup) :
    P.singletonLabels.toFinset=P.word.toFinset.filter (fun i => P.word.count i=1) := by
  ext i
  simp only [List.mem_toFinset, Finset.mem_filter,
    P.closed_mem_singletonLabels_iff_count_eq_one hP]
  constructor
  · intro hi
    exact ⟨List.count_pos_iff.mp (by omega),hi⟩
  · exact And.right

end Nonadditivity.NoncommutativeCS.EndpointSkeleton
