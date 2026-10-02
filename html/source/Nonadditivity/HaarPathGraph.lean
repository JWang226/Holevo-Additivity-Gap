/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/

import Nonadditivity.HaarPathMultiplicity

/-! # The colored multigraph of a closed reduced path

Edges are stored with the orientation of a positive generator. This is a
concrete representative of `[x,i,y] = [y,i*,x]`, and retains colored loops
and parallel edges. Degrees count both incidences of a loop. The results
prove BC equations (24)--(26) and the core-vertex estimate underlying (29)
for the actual graph extracted from the path.
-/
noncomputable section
namespace Nonadditivity.HaarPathGraph
open scoped BigOperators
open HaarPathProfiles
variable {V : Type*}

abbrev Edge (V : Type*) (d : ℕ) := V × Fin d × V
abbrev Dart (V : Type*) (d : ℕ) := Edge V d × Bool

def flipColor {d : ℕ} (c : Color d) : Color d := (c.1, !c.2)

def edge {d : ℕ} (x : V) (c : Color d) (y : V) : Edge V d :=
  if c.2 then (x,c.1,y) else (y,c.1,x)

def dart {d : ℕ} (x : V) (c : Color d) (y : V) : Dart V d := (edge x c y,c.2)
def reverse {d : ℕ} (q : Dart V d) : Dart V d := (q.1,!q.2)
def source {d : ℕ} (q : Dart V d) : V := if q.2 then q.1.1 else q.1.2.2
def color {d : ℕ} (q : Dart V d) : Color d := (q.1.2.1,q.2)

@[simp] theorem source_dart {d : ℕ} (x y : V) (c : Color d) :
    source (dart x c y) = x := by cases c with | mk i b => cases b <;> rfl
@[simp] theorem source_reverse_dart {d : ℕ} (x y : V) (c : Color d) :
    source (reverse (dart x c y)) = y := by cases c with | mk i b => cases b <;> rfl
@[simp] theorem color_dart {d : ℕ} (x y : V) (c : Color d) :
    color (dart x c y) = c := by cases c with | mk i b => cases b <;> rfl
@[simp] theorem color_reverse_dart {d : ℕ} (x y : V) (c : Color d) :
    color (reverse (dart x c y)) = flipColor c := by
  cases c with | mk i b => cases b <;> rfl

/-- A literal closed path whose generator word is reduced. No reduction is
required between the last and first colors, matching BC's path set. -/
structure Path (V : Type*) (d m : ℕ) where
  vertex : Fin (m+1) → V
  colors : Fin m → Color d
  closed : vertex (Fin.last m) = vertex 0
  reduced : ∀ i j : Fin m, i.val+1=j.val → colors j ≠ flipColor (colors i)

namespace Path
variable {d m : ℕ} [DecidableEq V] (P : Path V d m)

def edgeList : List (Edge V d) := List.ofFn fun i : Fin m =>
  edge (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ)
def edges : Finset (Edge V d) := P.edgeList.toFinset
def vertices : Finset V := Finset.univ.image fun i : Fin m => P.vertex i.castSucc
def darts : Finset (Dart V d) := P.edges ×ˢ Finset.univ
def degree (v : V) : ℕ := (P.darts.filter fun q => source q = v).card

def traversal (i : Fin m) : Dart V d :=
  dart (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ)

omit [DecidableEq V] in
@[simp] theorem edgeList_length : P.edgeList.length = m := by simp [edgeList]

lemma traversal_mem (i : Fin m) : P.traversal i ∈ P.darts := by
  simp only [darts, Finset.mem_product, Finset.mem_univ, and_true]
  apply List.mem_toFinset.mpr
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

lemma reverse_traversal_mem (i : Fin m) : reverse (P.traversal i) ∈ P.darts := by
  have h := P.traversal_mem i
  simpa only [darts, Finset.mem_product, Finset.mem_univ, and_true, reverse] using h

lemma start_mem (i : Fin m) : P.vertex i.castSucc ∈ P.vertices :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

lemma end_mem (i : Fin m) : P.vertex i.succ ∈ P.vertices := by
  by_cases hi : i.val+1 < m
  · have he : i.succ = (⟨i.val+1,hi⟩ : Fin m).castSucc := Fin.ext rfl
    rw [he]
    exact P.start_mem _
  · have he : i.succ = Fin.last m := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
    have hm : 0 < m := by omega
    rw [he, P.closed]
    exact P.start_mem ⟨0,hm⟩

lemma source_mem {q : Dart V d} (hq : q ∈ P.darts) : source q ∈ P.vertices := by
  obtain ⟨hq, _⟩ := Finset.mem_product.mp hq
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hq)
  obtain ⟨e,b⟩ := q
  change edge (P.vertex i.castSucc) (P.colors i) (P.vertex i.succ) = e at hi
  subst e
  obtain ⟨g,c⟩ := P.colors i
  cases b <;> cases c <;> simp only [source, edge, Bool.false_eq_true,
    ite_false, ite_true] <;> first | exact P.start_mem i | exact P.end_mem i

/-- The handshake identity includes loops with degree two. -/
theorem sum_degrees : ∑ v ∈ P.vertices, P.degree v = 2*P.edges.card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := P.darts) (t := P.vertices)
    (f := source) (fun q hq => P.source_mem hq)
  simpa [degree, darts, Finset.card_product, mul_comm] using h.symm

/-- Every visited vertex has an outgoing dart. -/
theorem degree_pos {v : V} (hv : v ∈ P.vertices) : 0 < P.degree v := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.card_pos.mpr
  exact ⟨P.traversal i, Finset.mem_filter.mpr
    ⟨P.traversal_mem i, source_dart _ _ _⟩⟩

/-- At every vertex other than the base, the reduced-word condition supplies
two distinct incidences. This does not assume cyclic reduction. -/
theorem two_le_degree {v : V} (hv : v ∈ P.vertices) (hne : v ≠ P.vertex 0) :
    2 ≤ P.degree v := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
  have hi0 : 0 < i.val := by
    by_contra h
    have he : i.castSucc = 0 := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero]; omega)
    exact hne (by rw [←hi,he])
  let j : Fin m := ⟨i.val-1,by omega⟩
  have hji : j.val+1=i.val := by dsimp [j]; omega
  have hjs : j.succ=i.castSucc := Fin.ext hji
  have hd : P.traversal i ≠ reverse (P.traversal j) := by
    intro he
    have hc := congrArg color he
    simp only [traversal, color_dart, color_reverse_dart] at hc
    exact P.reduced j i hji hc
  have hmem₁ : P.traversal i ∈ P.darts.filter (fun q => source q=v) := by
    apply Finset.mem_filter.mpr
    exact ⟨P.traversal_mem i, (source_dart _ _ _).trans hi⟩
  have hmem₂ : reverse (P.traversal j) ∈ P.darts.filter (fun q => source q=v) := by
    apply Finset.mem_filter.mpr
    refine ⟨P.reverse_traversal_mem j, ?_⟩
    simp only [traversal, source_reverse_dart, hjs, hi]
  have hsub : {P.traversal i, reverse (P.traversal j)} ⊆
      P.darts.filter (fun q => source q=v) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hmem₁
    · rw [Finset.mem_singleton] at hq
      simpa [hq] using hmem₂
  have hc := Finset.card_le_card hsub
  simpa [degree, hd] using hc

/-- BC equation (25): a nonempty closed reduced path has at least as many
colored edges as vertices, including when its base has degree one. -/
theorem vertices_le_edges : P.vertices.card ≤ P.edges.card := by
  have hpoint (v : V) (hv : v ∈ P.vertices) :
      2 ≤ P.degree v + (if v = P.vertex 0 then 1 else 0) := by
    by_cases h : v=P.vertex 0
    · have hp := P.degree_pos hv
      simp only [if_pos h]
      omega
    · simpa [h] using P.two_le_degree hv h
  have hs := Finset.sum_le_sum hpoint
  have hfilter : (P.vertices.filter fun v => v=P.vertex 0).card ≤ 1 := by
    have hsub : (P.vertices.filter fun v => v=P.vertex 0) ⊆ {P.vertex 0} := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2
    simpa using Finset.card_le_card hsub
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    Finset.sum_ite, Nat.mul_one] at hs
  rw [P.sum_degrees] at hs
  omega

/-- Twice the BC defect is nonnegative without fractions or parity assumptions. -/
theorem twice_vertices_le_length_add_singletons :
    2*P.vertices.card ≤ m + (HaarPathMultiplicity.singletonEdges P.edgeList).card := by
  have he := HaarPathMultiplicity.twice_edges_le_length_add_singletons P.edgeList
  rw [P.edgeList_length] at he
  have hv := P.vertices_le_edges
  change P.vertices.card ≤ P.edgeList.toFinset.card at hv
  omega

/-- Vertices retained by degree-two suppression: the base and every vertex
whose degree differs from two. -/
def coreVertices : Finset V := P.vertices.filter fun v => v=P.vertex 0 ∨ P.degree v ≠ 2

/-- The exact degree-count bound used in BC Lemma 5.8, before constructing
the chains between core vertices. -/
theorem coreVertices_add_twice_vertices_le :
    P.coreVertices.card + 2*P.vertices.card ≤ 2*P.edges.card+2 := by
  have hpoint (v : V) (hv : v ∈ P.vertices) :
      2 + (if v ∈ P.coreVertices then 1 else 0) ≤
        P.degree v + (if v=P.vertex 0 then 2 else 0) := by
    have hp := P.degree_pos hv
    by_cases hroot : v=P.vertex 0
    · simp only [if_pos hroot]
      split_ifs <;> omega
    · have htwo := P.two_le_degree hv hroot
      by_cases hc : v ∈ P.coreVertices
      · have hne : P.degree v ≠ 2 := by
          exact (Finset.mem_filter.mp hc).2.resolve_left hroot
        simp only [if_pos hc, if_neg hroot]
        omega
      · simp only [if_neg hc, if_neg hroot]
        omega
  have hs := Finset.sum_le_sum hpoint
  have hcore : (P.vertices.filter fun v => v ∈ P.coreVertices) = P.coreVertices := by
    exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
  have hfilter : (P.vertices.filter fun v => v=P.vertex 0).card ≤ 1 := by
    have hsub : (P.vertices.filter fun v => v=P.vertex 0) ⊆ {P.vertex 0} := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2
    simpa using Finset.card_le_card hsub
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    Finset.sum_ite, Nat.mul_one] at hs
  rw [hcore,P.sum_degrees] at hs
  omega

/-- Twice the defect, an integer even when the path length or the singleton
count is odd. -/
def defectTwice : ℕ := m + (HaarPathMultiplicity.singletonEdges P.edgeList).card -
  2*P.vertices.card

/-- The Euler-characteristic budget for the number of edges after suppressing
degree-two vertices. This is a numerical budget, not a definition of a
suppressed graph. -/
def coreEdgeBudget : ℕ := P.edges.card + P.coreVertices.card - P.vertices.card

/-- Twice the core-edge budget is at most `6*χ+4`, precisely the exponent
needed for the profile-count estimate. -/
theorem twice_coreEdgeBudget_le : 2*P.coreEdgeBudget ≤ 3*P.defectTwice+4 := by
  have hv := P.vertices_le_edges
  have hc := P.coreVertices_add_twice_vertices_le
  have he := HaarPathMultiplicity.twice_edges_le_length_add_singletons P.edgeList
  rw [P.edgeList_length] at he
  have hχ := P.twice_vertices_le_length_add_singletons
  change 2*P.edges.card ≤ _ at he
  dsimp [coreEdgeBudget,defectTwice]
  omega

/-- The actual finite set of word-profile assignments to the core-edge budget
has the claimed BC exponent. Constructing the suppressed chains is a separate
step; this theorem makes no assumption of an unproved profile cardinal bound. -/
theorem card_budgetProfileAssignments_le (hm : 0 < m) (hd : 0 < d) :
    Fintype.card (Fin P.coreEdgeBudget → BoundedProfile (Color d) m) ≤
      (2*d*m^d)^(3*P.defectTwice+4) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  have hc := HaarPathProfiles.card_signedProfile_le d m
  calc
    _ ≤ ((2*d*m^d)^2)^P.coreEdgeBudget := Nat.pow_le_pow_left hc _
    _ = (2*d*m^d)^(2*P.coreEdgeBudget) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by positivity) P.twice_coreEdgeBudget_le

/-- High-multiplicity occurrences are bounded by four times the BC defect.
This is derived from the actual path graph, including loops and colors. -/
theorem highMultiplicityOccurrences_le_twice_defect :
    HaarPathMultiplicity.highMultiplicityOccurrences P.edgeList ≤ 2*P.defectTwice := by
  have h := HaarPathMultiplicity.highMultiplicityOccurrences_le_twice_excess P.edgeList
  have he := HaarPathMultiplicity.excess_add_twice_edges P.edgeList
  rw [P.edgeList_length] at he
  have hv := P.vertices_le_edges
  have hχ := P.twice_vertices_le_length_add_singletons
  change P.vertices.card ≤ P.edgeList.toFinset.card at hv
  dsimp [defectTwice]
  omega

end Path
end Nonadditivity.HaarPathGraph
