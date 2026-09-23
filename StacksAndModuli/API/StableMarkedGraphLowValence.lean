module

public import StacksAndModuli.API.StableMarkedGraph

/-!
# Low-valence vertices in stable marked graphs

This file isolates the exceptional loop configuration at a weight-zero vertex of special
valence less than three. A loop already contributes two to special valence. If there is
room for nothing else, connectedness forces the graph to be the one-vertex, one-loop,
unmarked graph of genus one. Consequently a prestable graph has no loop at any low-valence
weight-zero vertex.

This is the combinatorial reduction needed when comparing stability of a nodal curve with
stability of its dual graph: only low-valence weight-zero components need to be presented
as smooth rational subcurves.

## Main results

* `VertexWeightedMarkedGraph.genus_markings_eq_one_zero_of_weight_zero_loop_lowValence`:
  the exceptional one-loop classification.
* `VertexWeightedMarkedGraph.loopEdgesAt_eq_empty_of_isPrestable_of_weight_zero_lowValence`:
  a prestable graph has no loop at a low-valence weight-zero vertex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe u v

namespace VertexWeightedMarkedGraph

variable {n : ℕ} {VertexType : Type u} {EdgeType : Type v}
  (G : VertexWeightedMarkedGraph n VertexType EdgeType)

/-- A weight-zero vertex carrying a loop and having special valence less than three
forces the exceptional unmarked genus-one graph.

Indeed, the loop uses both available incidences, so the vertex is isolated from every
other vertex and carries no marking. Connectedness then makes it the unique vertex, and
the loop the unique edge. -/
theorem genus_markings_eq_one_zero_of_weight_zero_loop_lowValence
    (x : G.Vertex) (hw : G.weight x = 0)
    (hloop : (G.loopEdgesAt x).Nonempty) (hs : G.specialValence x < 3) :
    (G.genus, n) = (1, 0) := by
  have hloop_pos : 0 < (G.loopEdgesAt x).ncard :=
    (Set.ncard_pos (s := G.loopEdgesAt x)).mpr hloop
  have hinc : (G.incidentEdgesAt x).Nonempty :=
    hloop.mono (G.loopEdgesAt_subset_incidentEdgesAt x)
  have hinc_pos : 0 < (G.incidentEdgesAt x).ncard :=
    (Set.ncard_pos (s := G.incidentEdgesAt x)).mpr hinc
  have hvalence : G.valence x = 2 := by
    rw [G.valence_eq]
    rw [G.specialValence_eq, G.valence_eq] at hs
    omega
  have hspecial : G.specialValence x = 2 := by
    rw [G.specialValence_eq]
    have hmark : G.markingMultiplicity x = 0 := by
      rw [G.specialValence_eq, hvalence] at hs
      omega
    omega
  have hinc_card : (G.incidentEdgesAt x).ncard = 1 := by
    rw [G.valence_eq] at hvalence
    omega
  have hinc_subsingleton : (G.incidentEdgesAt x).Subsingleton := by
    rw [← Set.ncard_le_one_iff_subsingleton]
    omega
  have hnomark : ¬ ∃ i : Fin n, G.marking i = x := by
    intro h
    have hmarkpos : 0 < G.markingMultiplicity x :=
      (G.markingMultiplicity_pos_iff x).mpr h
    rw [G.specialValence_eq, hvalence] at hspecial
    omega
  obtain ⟨e, he_loop⟩ := hloop
  have hvertex : ∀ y : G.Vertex, y = x := by
    intro y
    by_contra hyx
    have hreach := G.connected y x
    obtain ⟨z, hz⟩ := hreach.nonempty_neighborSet_right hyx
    have hadj : G.toGraph.Adj x.1 z.1 := hz.2
    obtain ⟨e', he'⟩ := hadj
    let E : G.Edge := ⟨e, he_loop.edge_mem⟩
    let E' : G.Edge := ⟨e', he'.edge_mem⟩
    have hE : E ∈ G.incidentEdgesAt x := ⟨x, he_loop⟩
    have hE' : E' ∈ G.incidentEdgesAt x := ⟨z, he'⟩
    have hEE' : E = E' := hinc_subsingleton hE hE'
    have he'' : G.toGraph.IsLink e x.1 z := by
      change G.toGraph.IsLink E.1 x.1 z
      rw [hEE']
      exact he'
    obtain h | h := he_loop.eq_and_eq_or_eq_and_eq he''
    · exact hz.1 (Subtype.ext h.2)
    · exact hz.1 (Subtype.ext h.1)
  let _ : Subsingleton G.Vertex :=
    ⟨fun y z ↦ (hvertex y).trans (hvertex z).symm⟩
  have hn : n = 0 := by
    by_contra hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    exact hnomark ⟨⟨0, hnpos⟩, Subsingleton.elim _ _⟩
  have hedge : G.edgeCount = 1 := by
    have hedge_unique : ∀ e' : G.Edge, e' = ⟨e, he_loop.edge_mem⟩ := by
      intro e'
      obtain ⟨y, z, hyz⟩ := G.toGraph.exists_isLink_of_mem_edgeSet e'.2
      let Y : G.Vertex := ⟨y, hyz.left_mem⟩
      let Z : G.Vertex := ⟨z, hyz.right_mem⟩
      have hyz' : G.toGraph.IsLink e'.1 x.1 x.1 := by
        have hY : Y = x := Subsingleton.elim _ _
        have hZ : Z = x := Subsingleton.elim _ _
        have hyzY : G.toGraph.IsLink e'.1 Y.1 Z.1 := hyz
        rw [hY, hZ] at hyzY
        exact hyzY
      have he'inc : e' ∈ G.incidentEdgesAt x := ⟨x, hyz'⟩
      exact hinc_subsingleton he'inc ⟨x, he_loop⟩
    let _ : Unique G.Edge :=
      { default := ⟨e, he_loop.edge_mem⟩
        uniq := hedge_unique }
    exact Nat.card_unique
  have hweight : G.totalWeight = 0 := by
    rw [G.totalWeight_eq]
    let _ := Fintype.ofFinite G.Vertex
    rw [Finset.sum_eq_single x]
    · exact hw
    · intro y _ hyx
      exact (hyx (Subsingleton.elim y x)).elim
    · simp
  have hvertexCount : G.vertexCount = 1 := Nat.card_unique
  have hgenus : G.genus = 1 := by
    rw [G.genus_eq, G.graphGenus_eq, hedge, hvertexCount, hweight]
  exact Prod.ext hgenus hn

/-- A prestable graph has no loop at a weight-zero vertex of special valence less than
three. This is the precise form needed before treating that vertex as a smooth rational
component. -/
theorem loopEdgesAt_eq_empty_of_isPrestable_of_weight_zero_lowValence
    (hpre : G.IsPrestable) (x : G.Vertex) (hw : G.weight x = 0)
    (hs : G.specialValence x < 3) :
    G.loopEdgesAt x = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro e he
  exact hpre (G.genus_markings_eq_one_zero_of_weight_zero_loop_lowValence
    x hw ⟨e, he⟩ hs)

end VertexWeightedMarkedGraph

end
